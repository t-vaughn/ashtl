// SECTION: io

#[derive(Default)]
struct Scanner {
    buffer: Vec<String>,
}

impl Scanner {
    fn next<T: FromStr>(&mut self) -> T {
        loop {
            if let Some(token) = self.buffer.pop() {
                return token.parse().ok().expect("Failed parse");
            }
            let mut input = String::new();
            std::io::stdin().read_line(&mut input).expect("Failed read");
            self.buffer = input.split_whitespace().rev().map(String::from).collect();
        }
    }
}

#[allow(unused_imports)]
use std::str::FromStr;

// fn main() {
//     let mut sc = Scanner::default();
//     let n: usize = sc.next();
//     let m: u64 = sc.next();
//     if n == 1 {
//         println!("1");
//         return;
//     }
// }

use ashtl::alg;
use ashtl::alg::fps::FPS;
use ashtl::alg::ops::inv;
use rand::Rng;
use rand::seq::SliceRandom;
use std::cmp::{max, min};
use std::time::Instant;

use std::io::{self, BufRead, BufWriter, Read, Write};

const M: u64 = (119 << 23) + 1;

fn main() {
    let a = "0110";
    let a1 = "1010";
    let a2 = "0000";
    let b = FPS::<M>::autocorrelation(a).normalize();
    let b1 = FPS::<M>::autocorrelation(a1).normalize();
    let b2 = FPS::<M>::autocorrelation(a2).normalize();
    let c = (16 * b.eval(inv::<M>(2))).rem_euclid(M as i64);
    let c1 = (16 * b1.eval(inv::<M>(2))).rem_euclid(M as i64);
    let c2 = (16 * b2.eval(inv::<M>(2))).rem_euclid(M as i64);
    println!("{}", c);
    println!("{}", c1);
    println!("{}", c2);
}

// TODO ORDER:
// m √n blossom
// cheeger partioning
// ---------------------------------------------------------------------
// O(log^2 n) dynamic connectivity https://loj.ac/s/2497274
// fix circulation rounding https://courses.csail.mit.edu/6.854/20/sample-projects/A-/Rounding_Flows_Kang_Payor.pdf https://arxiv.org/pdf/1507.08139
// dynamic rerooting tree dp
// slope trick utils
// mod linear shit
// Persistent Range Affine Range Sum
// Range Linear Add Range Min
// Deque Operate All Composite
// hampath heuristic
// top tree
// min ham cycle
// hafnian
// faster mod ops
// st numbering
// ----------------------------------------------------------------------
// larsch
// monge algos
// knapsack cases
// cc2
// 2ecc
// pfaffian
// fix splay tree
// axiotis tzamos may be wrong
// trie
// online z
// level ancestor
// line tree
// contour queries
// hash on tree
// tree iso
// 3ecc
// max clique
// max coclique
// convex polygon contains point
// redo CDQ, CDQ pow
// p recursive algos
// tutte polynomial
// sum of 2 squares
// sum of 3 squares
// dyanmic wavelet matrix
// whatever this is https://judge.yosupo.jp/submission/138316
