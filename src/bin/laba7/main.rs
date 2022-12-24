use std::ops::{DivAssign, Sub};

use num::{BigInt, BigUint, Integer, One, Zero};
use num::bigint::{RandBigInt, RandomBits};
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
        let mut tr = 0usize;
        loop {
            tr += 1;
            let num: BigUint = rb.sample(rng);
            if !simple_test(&num) { continue; }
            if !miller_rabin_test(&num, 100) { continue; }
            println!("GEN PRIME USED {} CYCLIC", tr);
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
            let mut i_ = 1;
            while e.gcd(&phi_n) != BigUint::one() {
                e = rng.gen_biguint_range(&BigUint::one(), &phi_n);
                i_ += 1;
            }
            println!("GEN 'e' USED {} CYCLIC", i_);
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

struct Alice {
    private: PrivateKey,
    public: PublicKey,

    k1: BigUint,
}

impl Alice {
    const A: &'static str = "ALICE";

    fn new() -> (Self, PublicKey) {
        let (puk, prk) = RSA::key_gen();
        (
            Self {
                private: prk,
                public: (Default::default(), Default::default()),
                k1: Default::default(),
            },
            puk
        )
    }

    fn recv_public(&mut self, puk: PrivateKey) {
        self.public = puk;
    }

    fn step1(&mut self) -> BigUint {
        let mut rng = thread_rng();
        let rb = RandomBits::new(128);
        self.k1 = (&rb).sample(&mut rng);
        println!("Alice generate k1: {}", self.k1);
        BigUint::from_bytes_be(format!("{}{}", self.k1, Self::A).as_bytes())
    }

    fn step3(&self, msg: BigUint) -> BigUint {
        let msg = String::from_utf8(msg.to_bytes_be()).unwrap();
        let k1 = self.k1.to_string();
        if !msg.ends_with(&k1) {
            panic!("Alice not found self k1 in msg");
        }
        let msg = msg.strip_suffix(&k1).unwrap();
        msg.parse::<BigUint>().unwrap()
    }
}

struct Bob {
    private: PrivateKey,
    public: PublicKey,

    k2: BigUint,
}

impl Bob {
    const A: &'static str = "BOB";

    fn new() -> (Self, PublicKey) {
        let (puk, prk) = RSA::key_gen();
        (
            Self {
                private: prk,
                public: (Default::default(), Default::default()),
                k2: Default::default(),
            },
            puk
        )
    }

    fn recv_public(&mut self, puk: PrivateKey) {
        self.public = puk;
    }

    fn step2(&mut self, msg: BigUint) -> BigUint {
        let msg = String::from_utf8(msg.to_bytes_be()).unwrap();
        if !msg.ends_with(Alice::A) {
            panic!("Bob: It's not a Alice");
        }
        let msg = msg.strip_suffix(Alice::A).unwrap();
        let k1 = msg.parse::<BigUint>().unwrap();

        let mut rng = thread_rng();
        let rb = RandomBits::new(128);
        self.k2 = (&rb).sample(&mut rng);
        println!("Bob generate k2: {}", self.k2);
        BigUint::from_bytes_be(format!("{}{}", self.k2, k1).as_bytes())
    }

    fn step4(&self, msg: BigUint) {
        if self.k2 == msg {
            println!("Bob recv self k2: {}", msg);
        } else {
            panic!("Bob recv left msg({}), not like self k2({})", msg, self.k2);
        }
    }
}


fn main() {
    let (mut alice, alice_puk) = Alice::new();
    let (mut bob, bob_puk) = Bob::new();
    alice.recv_public(bob_puk);
    bob.recv_public(alice_puk);

    let step1 = alice.step1();
    println!("Alice send: {}", step1);

    let step2 = bob.step2(step1);
    println!("Bob send: {}", step2);

    let step3 = alice.step3(step2);
    println!("Alice send: {}", step3);

    bob.step4(step3);

    println!("Now Alice & Bob can use overall key: k1 xor k2 = {}", alice.k1 ^ bob.k2);
}