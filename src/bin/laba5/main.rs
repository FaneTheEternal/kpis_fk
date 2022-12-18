use std::collections::HashMap;
use std::ops::{DivAssign, Sub};
use std::convert::TryFrom;
use std::fmt::Formatter;

use num::{BigInt, BigUint, Integer, One, ToPrimitive, Zero};
use num::bigint::{RandBigInt, RandomBits};
use num::integer::gcd;
use rand::prelude::*;

type PublicKey = (BigUint, BigUint);
type PrivateKey = (BigUint, BigUint);

fn simple_test(num: &BigUint) -> bool {
    if num.lt(&BigUint::from(100u8)) {
        return false;
    }
    for i in 2..=100u8 {
        if num.mod_floor(&BigUint::from(i)) == BigUint::zero() {
            return false;
        }
    }
    let sqrt = num.sqrt();
    let sqrt = sqrt.clone() * sqrt;
    if num.eq(&sqrt) {
        return false;
    }
    true
}

fn miller_rabin_test(num: &BigUint, k: usize) -> bool {
    let u0: BigUint = BigUint::zero();
    let u1: BigUint = BigUint::from(1u8);
    let u2: BigUint = BigUint::from(2u8);
    let u3: BigUint = BigUint::from(3u8);

    // если num == 2 или num == 3 - эти числа простые, возвращаем true
    if num.eq(&u2) | num.eq(&u3) {
        return true;
    }
    // если num < 2 или num четное - возвращаем false
    if num.lt(&u2)
        | num.mod_floor(&u2).eq(&u0) {
        return false;
    }
    // представим num − 1 в виде (2^s)*t, где t нечётно,
    // это можно сделать последовательным делением num - 1 на 2
    let mut t = num.sub(&u1);
    let mut s = 0usize;
    while t.mod_floor(&u2).eq(&u0) {
        t.div_assign(&u2);
        s += 1;
    }
    // повторить k раз
    for _ in 0..k {
        // выберем случайное целое число a в отрезке [2, num − 2]
        let mut rng = thread_rng();
        let mut a = rng.gen_biguint_range(
            &u2.clone(),
            &num.sub(u2.clone()),
        );
        while a.lt(&u2) | a.ge(&num.sub(&u2)) {
            a = rng.gen_biguint_range(
                &u2.clone(),
                &num.sub(u2.clone()),
            );
        }
        // x = a^t mod num, вычислим с помощью возведения в степень по модулю
        let mut x = a.modpow(&t, &num);
        // если x == 1 или x == num − 1, то перейти на следующую итерацию цикла
        if x.eq(&u1) | x.eq(&num.sub(&u1)) {
            continue;
        }
        // повторить s − 1 раз
        for _ in 1..s {
            // x = x^2 mod num
            x = x.modpow(&u2, &num);
            // если x == 1, то вернуть "составное"
            if x.eq(&u1) {
                return false;
            }
            // если x == n − 1, то перейти на следующую итерацию внешнего цикла
            if x.eq(&num.sub(&u1)) {
                break;
            }
        }
        if !x.eq(&num.sub(&u1)) {
            return false;
        }
    }
    // вернуть "вероятно простое"
    true
}

fn mod_inv(a: BigInt, module: BigInt) -> BigInt {
    let mut mn = (module.clone(), a);
    let mut xy = (BigInt::zero(), BigInt::one());

    while mn.1 != BigInt::zero() {
        xy = (xy.1.clone(), xy.0.clone() - (mn.0.clone() / mn.1.clone()) * xy.1.clone());
        mn = (mn.1.clone(), mn.0.mod_floor(&mn.1));
    }

    while xy.0 < BigInt::zero() {
        xy.0 += module.clone();
    }
    xy.0
}

pub struct RSA {}

impl RSA {
    pub fn find_simple(rng: &mut ThreadRng, rb: &RandomBits) -> BigUint {
        loop {
            let num: BigUint = rb.sample(rng);
            if !simple_test(&num) { continue; }
            if !miller_rabin_test(&num, 100) { continue; }
            return num;
        }
    }

    fn key_gen() -> (PublicKey, PrivateKey) {
        let mut rng = rand::thread_rng();
        let rb = RandomBits::new(1024);
        let p: BigUint = RSA::find_simple(&mut rng, &rb);
        let q: BigUint = RSA::find_simple(&mut rng, &rb);
        let n = p.clone() * q.clone();
        let phi_n = (p - BigUint::one()) * (q - BigUint::one());
        let mut e = rng.gen_biguint_range(&BigUint::one(), &phi_n);
        {
            while gcd(BigInt::from(e.clone()), BigInt::from(phi_n.clone())) != BigInt::one() {
                e = rng.gen_biguint_range(&BigUint::one(), &phi_n);
            }
        }
        let d = mod_inv(BigInt::from(e.clone()), BigInt::from(phi_n.clone()));
        let d = BigUint::try_from(d).expect("Negative 'd'");
        assert_eq!((e.clone() * d.clone()).mod_floor(&phi_n), BigUint::one(), "Invalid 'e', 'd'");

        let puk = (e, n.clone());
        let prk = (d, n.clone());
        (puk, prk)
    }

    fn _encrypt(data: BigUint, key: PublicKey) -> BigUint {
        data.modpow(&key.0, &key.1)
    }

    fn _decrypt(data: BigUint, key: PrivateKey) -> BigUint {
        data.modpow(&key.0, &key.1)
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
enum Color {
    Red,
    Blue,
    Yellow,
}

impl Into<u8> for Color {
    fn into(self) -> u8 {
        match self {
            Color::Red => { 0b00 }
            Color::Blue => { 0b01 }
            Color::Yellow => { 0b10 }
        }
    }
}

impl From<u8> for Color {
    fn from(n: u8) -> Self {
        match n {
            0b00 => Color::Red,
            0b01 => Color::Blue,
            0b10 => Color::Yellow,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Edge(u8, u8);

#[derive(Eq, PartialEq)]
struct Node {
    code: u8,
    color: Color,
}

#[derive(Default)]
struct Graph {
    edges: Vec<Edge>,
    nodes: Vec<Node>,
}

impl Graph {
    fn add_edge(&mut self, lhs: (u8, Color), rhs: (u8, Color)) {
        self.edges.push(Edge(lhs.0, rhs.0));
        if self.nodes.iter().find(|n| n.code == lhs.0).is_none() {
            self.nodes.push(Node { code: lhs.0, color: lhs.1 });
        }
        if self.nodes.iter().find(|n| n.code == rhs.0).is_none() {
            self.nodes.push(Node { code: rhs.0, color: rhs.1 });
        }
    }

    fn uncolored(&self) -> Self {
        let mut graph = Self::default();
        for edge in self.edges.iter() {
            graph.add_edge((edge.0, Color::Red), (edge.1, Color::Red));
        }
        graph
    }
}

impl std::fmt::Debug for Graph {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Graph(\n{}\n)",
            self.edges.iter()
                .map(|e| {
                    let lhs = self.nodes.iter().find(|n| n.code == e.0).unwrap();
                    let rhs = self.nodes.iter().find(|n| n.code == e.1).unwrap();
                    format!("\t{}({:?}) <-> {}({:?})", lhs.code, lhs.color, rhs.code, rhs.color)
                })
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

struct Alice {
    graph: Graph,

    r: HashMap<u8, BigUint>,

    public: HashMap<u8, PublicKey>,
    private: HashMap<u8, PrivateKey>,

    z: HashMap<u8, BigUint>,
}

impl Alice {
    fn new() -> Self {
        let mut graph = Graph::default();
        graph.add_edge((0, Color::Red), (1, Color::Yellow));
        graph.add_edge((1, Color::Yellow), (2, Color::Red));
        graph.add_edge((1, Color::Yellow), (3, Color::Blue));
        graph.add_edge((1, Color::Yellow), (4, Color::Red));
        graph.add_edge((2, Color::Red), (3, Color::Blue));
        graph.add_edge((3, Color::Blue), (4, Color::Red));
        graph.add_edge((4, Color::Red), (5, Color::Yellow));

        let mut public = HashMap::<u8, PublicKey>::new();
        let mut private = HashMap::<u8, PrivateKey>::new();
        let mut r_map = HashMap::<u8, BigUint>::new();
        let mut z = HashMap::<u8, BigUint>::new();

        let mut rng = thread_rng();
        let rb = RandomBits::new(512);
        for node in graph.nodes.iter() {
            let r: BigUint = rb.sample(&mut rng);
            let r = (r | BigUint::from(0b11_u8)) ^ BigUint::from(0b11_u8);
            let r: BigUint = r | BigUint::from(Into::<u8>::into(node.color));
            r_map.insert(node.code, r.clone());

            let (puk, prk) = RSA::key_gen();
            public.insert(node.code, puk.clone());
            private.insert(node.code, prk.clone());
            z.insert(node.code, RSA::_encrypt(r, puk));
        }

        Self {
            graph,
            r: r_map,
            public,
            private,
            z,
        }
    }

    fn request(&self, edge: &Edge) -> (PrivateKey, PrivateKey) {
        (
            self.private.get(&edge.0).unwrap().clone(),
            self.private.get(&edge.1).unwrap().clone(),
        )
    }
}

struct Bob {
    graph: Graph,

    z: HashMap<u8, BigUint>,
    r: HashMap<u8, BigUint>,
}

impl Bob {
    fn colorize(&mut self, alice: &Alice) {
        for edge in &self.graph.edges {
            let (c1, c2) = alice.request(edge);
            let r1 = RSA::_decrypt(
                self.z.get(&edge.0).unwrap().clone(),
                c1,
            );
            self.r.insert(edge.0, r1.clone());
            let r2 = RSA::_decrypt(
                self.z.get(&edge.1).unwrap().clone(),
                c2,
            );
            self.r.insert(edge.1, r2.clone());
            let mask = BigUint::from(0b11_u8);
            let suf1 = r1 & mask.clone();
            let suf2 = r2 & mask;
            if suf1 == suf2 {
                panic!("Alice is a liar! {:?}: {} == {}", edge, suf1, suf2);
            } else {
                println!("SYN {:?}: {} != {}", edge, suf1, suf2);
            }
            if let Some(node) = self.graph.nodes.iter_mut()
                .find(|node| node.code == edge.0) {
                node.color = suf1.to_u8().unwrap().into();
            }
            if let Some(node) = self.graph.nodes.iter_mut()
                .find(|node| node.code == edge.1) {
                node.color = suf2.to_u8().unwrap().into();
            }
        }
    }
}

fn main() {
    let alice = Alice::new();
    println!("Alice {:?}", alice.graph);
    let mut bob = Bob {
        graph: alice.graph.uncolored(),
        z: alice.z.clone(),
        r: Default::default(),
    };
    bob.colorize(&alice);
    println!("Bob {:?}", bob.graph);
    println!("Validate R:");
    for (i, (code, r)) in alice.r.iter().enumerate() {
        let r_b = bob.r.get(&code).unwrap();
        println!(
            "\tR{}: Alice({}) {}= Bob({})",
            i,
            fmt_num(&r),
            if r.eq(r_b) { '=' } else { '!' },
            fmt_num(r_b),
        );
    }
}

fn fmt_num(n: &BigUint) -> String {
    let n = format!("{}", n);
    if n.len() > 9 {
        return [&n[..3], &n[(n.len() - 3)..]].join("...");
    }
    n
}
