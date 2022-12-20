use std::ops::{DivAssign, Sub};

use num::{BigInt, BigUint, Integer, One, Zero};
use num::bigint::{RandBigInt, RandomBits};
use rand::prelude::*;

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

fn find_simple(rng: &mut ThreadRng, rb: &RandomBits) -> BigUint {
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

fn gen_c_d(rng: &mut ThreadRng, rb: &RandomBits, p: &BigUint) -> (BigUint, BigUint) {
    let p_1 = p.clone() - BigUint::one();
    let mut c: BigUint = rb.sample(rng);
    while c.gcd(&p_1) != BigUint::one() {
        c = rb.sample(rng);
    }
    (
        c.clone(),
        mod_inv(BigInt::from(c), BigInt::from(p.clone())).try_into().unwrap()
    )
}

#[derive(Debug)]
struct Alice {
    p: BigUint,
    c: BigUint,
    d: BigUint,
}

impl Alice {
    fn new(rng: &mut ThreadRng, rb: &RandomBits, p: &BigUint) -> Self {
        let (c, d) = gen_c_d(rng, rb, p);
        let s = Self { p: p.clone(), c, d };
        println!("{s:?}");
        s
    }

    fn make_cards(&self, rng: &mut ThreadRng) -> (BigUint, BigUint, BigUint) {
        let lb = BigUint::one();
        let rb = self.p.clone() - BigUint::one();
        (
            rng.gen_biguint_range(&lb, &rb),
            rng.gen_biguint_range(&lb, &rb),
            rng.gen_biguint_range(&lb, &rb),
        )
    }

    fn send_u(&self, a: &BigUint, b: &BigUint, y: &BigUint, rng: &mut impl Rng) -> Vec<BigUint> {
        let mut u = vec![
            a.modpow(&self.c, &self.p),
            b.modpow(&self.c, &self.p),
            y.modpow(&self.c, &self.p),
        ];
        u.shuffle(rng);
        u
    }
}

#[derive(Debug)]
struct Bob {
    p: BigUint,
    c: BigUint,
    d: BigUint,
}

impl Bob {
    fn new(rng: &mut ThreadRng, rb: &RandomBits, p: &BigUint) -> Self {
        let (c, d) = gen_c_d(rng, rb, p);
        let s = Self { p: p.clone(), c, d };
        println!("{s:?}");
        s
    }

    fn pick(&self, mut u: Vec<BigUint>, rng: &mut impl Rng) -> (BigUint, Vec<BigUint>) {
        let u_ = u.remove(rng.gen_range(0..u.len()));
        (
            u_,
            u.into_iter()
                .map(|u| u.modpow(&self.c, &self.p))
                .collect()
        )
    }
}

fn main() {
    let mut rng = thread_rng();
    let rb = RandomBits::new(1024);
    let p = find_simple(&mut rng, &rb);

    let alice = Alice::new(&mut rng, &rb, &p);
    let bob = Bob::new(&mut rng, &rb, &p);

    let (a, b, y) = alice.make_cards(&mut rng);
    println!("Alice says: alpha={} beta={} gamma={}", a, b, y);
    let u = alice.send_u(&a, &b, &y, &mut rng);
    println!("Alice send u: [{}]", u.iter().enumerate()
        .map(|(i, e)| format!("u{}: {}", i + 1, e))
        .collect::<Vec<_>>().join(", ")
    );
    let (u_, v) = bob.pick(u, &mut rng);
    println!("Bob choice u^: {}", u_);
    println!("Bob send v: [{}]", v.iter().enumerate()
        .map(|(i, e)| format!("v{}: {}", i + 1, e))
        .collect::<Vec<_>>().join(", ")
    );
}