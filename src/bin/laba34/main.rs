use std::convert::TryFrom;
use std::ops::{DivAssign, Sub};

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
            while gcd(BigInt::from(e.clone()), BigInt::from(phi_n.clone())) != BigInt::one() {
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

struct Elgamal;

impl Elgamal {
    fn _key_gen(n: &BigUint) -> BigUint {
        let mut rng = rand::thread_rng();
        let lbound = BigUint::from(10usize).pow(2);
        let mut make_key = || {
            rng.gen_biguint_range(&lbound, n)
        };
        let mut key = make_key();
        while key.gcd(n) != BigUint::one() {
            key = make_key();
        }
        key
    }

    pub fn key_gen() -> (BigUint, BigUint, BigUint, BigUint) {
        let mut rng = rand::thread_rng();
        let rb = RandomBits::new(32);
        let q = RSA::find_simple(&mut rng, &rb);
        let g = rng.gen_biguint_range(&BigUint::from(2u32), &q);
        let key = Elgamal::_key_gen(&q);
        let h = g.modpow(&key, &q);
        (q, h, g, key)
    }

    pub fn encrypt(data: String, q: BigUint, h: BigUint, g: BigUint) -> (Vec<BigUint>, BigUint) {
        let k = Elgamal::_key_gen(&q);
        let s = h.modpow(&k, &q);
        let p = g.modpow(&k, &q);
        let s = s.to_u64().unwrap();
        let ct = data.chars()
            .map(|c| BigUint::from(c as u32) * s.clone())
            .collect::<Vec<_>>();
        (ct, p)
    }

    pub fn decrypt(ct: Vec<BigUint>, p: BigUint, key: BigUint, q: BigUint) -> String {
        let h = p.modpow(&key, &q);
        ct.into_iter()
            .map(|n| (n / h.clone()).to_u8().unwrap() as char)
            .collect::<String>()
    }
}


pub fn main() {
    println!("- RSA -");
    let data = "In Rust we trust";
    println!("ORIGINAL {:?}", data);
    let data = BigUint::from_bytes_be(data.as_bytes());
    let (public, private) = RSA::key_gen();
    let enc = RSA::_encrypt(data.clone(), public);
    println!("ENCRYPTED {:?}", enc);
    let dec = RSA::_decrypt(enc, private);
    let data = dec.to_bytes_be();
    let data = String::from_utf8_lossy(&data);
    println!("DECRYPTED {:?}", data);

    println!("- Elgamal -");
    let data = "In Rust we trust".to_string();
    println!("ORIGINAL {:?}", data);
    let (q, h, g, key) = Elgamal::key_gen();
    let (ct, p) = Elgamal::encrypt(data, q.clone(), h, g);
    println!("ENCRYPTED {:?} {:?}", p, ct);
    let dec = Elgamal::decrypt(ct, p, key, q);
    println!("DECRYPTED {:?}", dec);
}
