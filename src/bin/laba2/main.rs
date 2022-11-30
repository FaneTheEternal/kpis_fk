use num_bigint::BigInt;

const Q: isize = 29;
const XA: isize = 13;
const XB: isize = 18;

fn main() {
    let q = BigInt::from(Q);
    println!("q = {}", q);
    let a = BigInt::from(2 * q.clone() + 1);
    println!("a = {}", a);
    let xa = BigInt::from(XA);
    println!("Xa = {}", xa);
    let xb = BigInt::from(XB);
    println!("Xb = {}", xb);

    let ya = a.modpow(&xa, &q);
    println!("Ya = {}", ya);
    let yb = a.modpow(&xb, &q);
    println!("Yb = {}", yb);

    let ka = yb.modpow(&xa, &q);
    println!("Ka = {}", ka);
    let kb = ya.modpow(&xb, &q);
    println!("Kb = {}", kb);
}
