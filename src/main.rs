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

fn main() {}

// TODO ORDER:
// line tree
// top tree
// redo CDQ, CDQ pow
// ---------------------------------------------------------------------
// O(log^2 n) dynamic connectivity https://loj.ac/s/2497274
// p recursive algos
// sum of 2 squares
// sum of 3 squares
// subtree LCT
// tree iso
// cheeger partioning
// m √n blossom
// dynamic rerooting tree dp
// slope trick utils
// mod linear shit
// Persistent Range Affine Range Sum
// Range Linear Add Range Min
// Deque Operate All Composite
// hampath heuristic
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
// contour queries
// hash on tree
// 3ecc
// max clique
// max coclique
// convex polygon contains point
// tutte polynomial
// dyanmic wavelet matrix
// whatever this is https://judge.yosupo.jp/submission/138316
