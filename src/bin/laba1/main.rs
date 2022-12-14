use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::ops::AddAssign;
use num::{BigInt, Integer};
use num::integer::Roots;

const A: isize = 5999801;
const B: isize = 48685811;

fn find_div(n: isize) -> isize {
    for i in 2..=(n.sqrt() as isize + 1) {
        if n % i == 0 {
            return i;
        }
    }
    return n;
}

fn split(mut n: isize) -> HashMap<isize, isize> {
    let mut map: HashMap<isize, isize> = HashMap::new();
    while n > 1 {
        let div = find_div(n);
        match map.entry(div) {
            Entry::Occupied(mut oc) => {
                oc.get_mut().add_assign(1)
            }
            Entry::Vacant(mut vac) => {
                vac.insert(1);
            }
        }
        n /= div;
    }
    map
}

fn p0(n: isize) {
    println!("{}) {}", n, "-".repeat(50));
}

fn p1() {
    p0(1);
    println!(
        "A({}): {}", A,
        split(A).into_iter()
            .map(|(k, v)| format!("{}^{}", k, v))
            .collect::<Vec<_>>().join(" * "),
    );
    println!(
        "B({}): {}", B,
        split(B).into_iter()
            .map(|(k, v)| format!("{}^{}", k, v))
            .collect::<Vec<_>>().join(" * "),
    );
}

fn gcd_euclid(mut a: isize, mut b: isize) -> isize {
    while a > 0 && b > 0 {
        if a > b {
            a %= b;
        } else {
            b %= a;
        }
    }
    return a + b;
}

fn p2() {
    p0(2);
    println!("GCD Euclid {}, {} => {}", A, B, gcd_euclid(A, B));

    let mut a = split(A);
    let mut b = split(B);
    let mut gcd_primal = HashMap::<isize, isize>::new();
    for (k, v) in a {
        if let Some(v_b) = b.remove(&k) {
            gcd_primal.insert(k, v.min(v_b));
        }
    }
    println!(
        "GCD Primal {}, {} => {}", A, B,
        gcd_primal.into_iter()
            .map(|(k, v)| k.pow(v as u32))
            .sum::<isize>().max(1),
    );
}

fn p3() {
    p0(3);
    // av + bu = gcd(a, b)
    /// (a, b) -> (v, u, gcd(a, b))
    fn bezout(a: isize, b: isize) -> (isize, isize, isize) {
        if b == 0 {
            return (1, 0, a);
        }
        let (v, u, g) = bezout(b, a % b);
        return (u, v - (a / b) * u, g);
    }
    let (v, u, g) = bezout(A as isize, B as isize);
    println!("Bezout A({}), B({}))", A, B);
    println!("av + bu = gcd(a, b)");
    println!("a * {} + b * {} = {} = {}", v, u, A * v + B * u, g);
}

fn p4() {
    p0(4);
    const N: u32 = 2005;
    const N_E: u32 = 2003;
    const DIV: u32 = 17;
    let n = BigInt::from(N).pow(N_E);
    let div = BigInt::from(DIV);
    let a = n.div_mod_floor(&div);
    println!("{}^{} = {} * {} + {}", N, N_E, DIV, a.0, a.1);
}

fn main() {
    p1();
    p2();
    p3();
    p4();
}