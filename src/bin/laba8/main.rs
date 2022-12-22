use std::ops::{Mul, Sub};
use num::Integer;
use rand::{Rng, thread_rng};

enum Polynom {
    Const(isize),
    Func {
        exp: isize,
        mul: isize,
    },
}

fn main() {
    let m = 48_isize;
    let p = 53_isize;
    let scheme = (4_isize, 5_isize);
    println!("M: {m}; p: {p}; scheme: {scheme:?}");

    let mut rng = thread_rng();

    let polynom = (1..=(scheme.0 - 1))
        .rev()
        .map(|i| Polynom::Func { exp: i, mul: rng.gen_range(1..p) })
        .chain([Polynom::Const(m)])
        .collect::<Vec<_>>();

    println!(
        "F(x) = {} mod {}",
        polynom.iter()
            .map(|m| {
                match m {
                    Polynom::Const(c) => { format!("{}", c) }
                    Polynom::Func { exp, mul } => { format!("{}x^{}", mul, exp) }
                }
            })
            .collect::<Vec<_>>()
            .join(" + "),
        p,
    );

    let k = (1..=(scheme.1))
        .map(|x| {
            polynom.iter()
                .map(|m| {
                    match m {
                        Polynom::Const(c) => { *c }
                        Polynom::Func { exp, mul } => {
                            x.pow(*exp as u32).mul(mul)
                        }
                    }
                })
                .sum::<isize>()
                .mod_floor(&p)
        })
        .collect::<Vec<_>>();

    let mut recover = (1..=scheme.1).collect::<Vec<_>>();
    for _ in 0..(scheme.1 - scheme.0) {
        recover.remove(rng.gen_range(0..recover.len()));
    }

    let m = recover.iter()
        .map(|i| {
            let k = k.get((*i - 1) as usize).unwrap();
            let mut multiplier = *k;
            let mut divider = 1_isize;
            for &j in recover.iter().filter(|&j| j != i) {
                multiplier *= j;
                divider *= (j - i);
            }
            let member = multiplier / divider;
            println!("S{i} * k{i} = {multiplier} / {divider} mod {p} = {member}");
            member
        }).sum::<isize>().mod_floor(&p);
    println!("M: {m}");
}
