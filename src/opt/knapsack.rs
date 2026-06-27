use rand::seq::SliceRandom;

use crate::{alg::fps::FPS, ds::scan::MonotoneQueue, opt::min_plus::max_plus_ccv};

/// O(n M)
pub fn subset_sum(w: &[u64], t: u64) -> u64 {
    let (mut a, mut b) = (0, 0);
    while b < w.len() && a + w[b] <= t {
        a += w[b];
        b += 1;
    }
    if b == w.len() {
        return a;
    }
    let m = w.iter().max().cloned().unwrap_or(0);
    let mut u;
    let mut v = vec![-1; (m as usize) << 1];
    v[(a + m - t) as usize] = b as i64;
    for i in b..w.len() {
        u = v.clone();
        for x in 0..m as usize {
            v[x + w[i] as usize] = v[x + w[i] as usize].max(u[x]);
            let mut x = (m as usize) << 1;
            while {
                x -= 1;
                x > m as usize
            } {
                for j in 0.max(u[x])..v[x] {
                    v[x - w[j as usize] as usize] = v[x - w[j as usize] as usize].max(j);
                }
            }
        }
    }
    let mut a = t;
    while a > 0 && v[(a + m - t) as usize] < 0 {
        a -= 1;
    }
    a
}

// https://arxiv.org/pdf/2308.11307
/// Õ(n^3/2 w)
pub fn shuffle_zero_one_knapsack(capacity: i64, mut items: Vec<(i64, i64)>) -> i64 {
    let n = items.len();
    let w_max = items.iter().map(|i| i.0).max().unwrap_or(0);
    let sum_weight: i64 = items.iter().map(|i| i.0).sum();
    let target_weight = capacity.min(sum_weight);
    let mut rng = rand::rng();
    items.shuffle(&mut rng);
    let neg_inf = i64::MIN / 2;
    let mut prev_dp = vec![0; (capacity + 1) as usize];
    let mut curr_dp = prev_dp.clone();
    let c_delta = 4.0;
    for i in 1..=n {
        let item = &items[i - 1];
        let w_i = item.0;
        let p_i = item.1;
        let mu_i = (i as f64 / n as f64) * target_weight as f64;
        let delta_i = c_delta * (i as f64).sqrt() * w_max as f64;
        let start_j = (mu_i - delta_i).floor() as i64;
        let end_j = (mu_i + delta_i).ceil() as i64;
        for j in start_j..=end_j {
            if j < 0 || j > capacity {
                continue;
            }
            let j_idx = j as usize;
            let term1 = prev_dp[j_idx];
            let term2 = if j - w_i < 0 {
                neg_inf
            } else {
                let prev_idx = (j - w_i) as usize;
                if prev_idx >= prev_dp.len() || prev_dp[prev_idx] == neg_inf {
                    neg_inf
                } else {
                    prev_dp[prev_idx] + p_i
                }
            };
            curr_dp[j_idx] = term1.max(term2);
        }
        let copy_start = start_j.max(0) as usize;
        let copy_end = capacity.min(end_j) as usize;
        for k in copy_start..=copy_end {
            prev_dp[k] = curr_dp[k];
        }
    }
    *prev_dp.iter().max().unwrap_or(&0)
}

// https://arxiv.org/pdf/1802.06440
/// O(d c log c)
pub fn axiotis_tzamos_zero_one(v: &[u64], w: &[u64], c: u64) -> u64 {
    let n = v.len();
    let mut bucket = vec![Vec::new(); c as usize + 1];
    for i in 0..n {
        if w[i] <= c {
            bucket[w[i] as usize].push(v[i]);
        }
    }
    let mut dp = vec![0; c as usize + 1];
    dp[0] = 0;
    for w in 1..=c as usize {
        let list = &mut bucket[w];
        if list.is_empty() {
            continue;
        }
        list.sort_unstable_by(|a, b| b.cmp(a));
        let m = list.len().min(c as usize / w);
        let mut sum = Vec::with_capacity(m + 1);
        sum.push(0);
        let mut current_sum = 0;
        for &val in &list[0..m] {
            current_sum += val;
            sum.push(current_sum);
        }
        for k in 0..w as usize {
            let n = (c as usize - k) / w + 1;
            if n == 0 {
                continue;
            }
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(dp[i * w + k]);
            }
            let res = max_plus_ccv(&v, &sum);
            for i in 0..n {
                dp[i * w + k] = res[i];
            }
        }
    }
    *dp.iter().max().unwrap_or(&0)
}

/// O(n + c log c)
pub fn zero_one_knapsack_eq<const M: u64>(w: &[usize], c: usize) -> Vec<u64> {
    FPS::<M>::log_prod_1pxit(1, w.into_iter().cloned(), c + 1)
        .exp(c + 1)
        .unwrap()
        .coeff
        .into_iter()
        .map(|i| i.rem_euclid(M as i64) as u64)
        .collect::<Vec<_>>()
}

// https://arxiv.org/pdf/1802.06440
/// O(min(n c, M^2 log M, V^2 log V))
pub fn axiotis_tzamos_complete(v: &[u64], w: &[u64], mut c: u64) -> u64 {
    let n = v.len();
    if n == 0 {
        return 0;
    }
    let max_v = v.iter().max().copied().unwrap_or(0);
    let max_w = w.iter().max().copied().unwrap_or(0);
    if max_v <= 0 || max_w == 0 {
        return 0;
    }
    if n as u64 * c <= 10 * max_v.min(max_w).pow(2) {
        let cap = c as usize;
        let mut dp = vec![0u64; cap + 1];
        for i in 0..n {
            let weight = w[i] as usize;
            let value = v[i];
            if weight <= cap && weight > 0 {
                for j in weight..=cap {
                    dp[j] = dp[j].max(dp[j - weight] + value);
                }
            }
        }
        return dp[cap];
    }
    let limit = max_w.pow(2);
    let mut best_idx = 0;
    let mut max_density = -1.0;
    for i in 0..n {
        if w[i] == 0 {
            continue;
        }
        let density = v[i] as f64 / w[i] as f64;
        if density > max_density {
            max_density = density;
            best_idx = i;
        }
    }
    let best_w = w[best_idx];
    let best_v = v[best_idx];
    if max_w <= max_v {
        let reduce_count = if limit < c { (c - limit) / best_w } else { 0 };
        c -= reduce_count * best_w;
        let minf = i64::MIN / 2;
        let m = max_w;
        let k = m as usize + 1;
        let mut dp = vec![minf; k];
        dp[0] = 0;
        for i in 0..n {
            dp[w[i] as usize] = dp[w[i] as usize].max(v[i] as i64);
        }
        let mut z = 1;
        while z < m {
            let mut dp_new = vec![minf; k];
            for i in 0..k {
                for j in 0..k - i {
                    dp_new[i + j] = dp_new[i + j].max(dp[i] + dp[j]);
                }
            }
            dp = dp_new;
            z <<= 1;
        }
        let mut padded_dp = vec![minf; m as usize];
        padded_dp.extend(dp);
        dp = padded_dp;
        let lg = i64::BITS - c.leading_zeros();
        let len = dp.len();
        for i in (1..=lg).rev() {
            let mut dp_new = vec![minf; len];
            let bit = (c >> (i - 1)) & 1;
            let offset = (m + bit) as usize;
            for idx in 0..len {
                let target_k = offset + idx;
                let min_x = if target_k >= len {
                    target_k - len + 1
                } else {
                    0
                };
                let max_x = target_k.min(len - 1);
                let mut val = minf;
                for x in min_x..=max_x {
                    val = val.max(dp[x] + dp[target_k - x]);
                }
                dp_new[idx] = val;
            }
            dp = dp_new;
        }
        let check_len = (m as usize + 1).min(dp.len());
        *dp[0..check_len].iter().max().unwrap_or(&0) as u64 + reduce_count * best_v
    } else {
        println!("second");
        let z = c / best_w + 1;
        let reduce_count = if max_v <= z { z - max_v } else { 0 };
        let t = z * best_v - reduce_count * best_v;
        c -= reduce_count * best_w;
        let inf = u64::MAX / 2;
        let m = max_v;
        let k = m as usize + 1;
        let mut dp = vec![inf; k];
        dp[0] = 0;
        for i in 0..n {
            dp[v[i] as usize] = dp[v[i] as usize].min(w[i]);
        }
        let mut z = 1;
        while z < m {
            let mut dp_new = vec![inf; k];
            for i in 0..k {
                for j in 0..k - i {
                    dp_new[i + j] = dp_new[i + j].min(dp[i] + dp[j]);
                }
            }
            dp = dp_new;
            z <<= 1;
        }
        let mut padded_dp = vec![inf; m as usize];
        padded_dp.extend(dp);
        dp = padded_dp;
        let lg = u64::BITS - t.leading_zeros();
        let len = dp.len();
        for i in (1..=lg).rev() {
            let mut dp_new = vec![inf; len];
            let bit = (t >> (i - 1)) & 1;
            let offset = (m + bit) as usize;
            for idx in 0..len {
                let target_k = offset + idx;
                let min_x = if target_k >= len {
                    target_k - len + 1
                } else {
                    0
                };
                let max_x = target_k.min(len - 1);
                let mut val = inf;
                for x in min_x..=max_x {
                    val = val.min(dp[x] + dp[target_k - x]);
                }
                dp_new[idx] = val;
            }
            dp = dp_new;
        }
        let check_len = (m as usize + 1).min(dp.len());
        let i = dp[0..check_len].iter().rposition(|&c_p| c_p <= c).unwrap();
        t - m + i as u64 + reduce_count * best_v
    }
}

/// O(n + c log c)
pub fn complete_knapsack_eq<const M: u64>(w: &[usize], c: usize) -> Vec<u64> {
    (-FPS::<M>::log_prod_1pxit(-1, w.into_iter().cloned(), c + 1))
        .exp(c + 1)
        .unwrap()
        .coeff
        .into_iter()
        .map(|i| i.rem_euclid(M as i64) as u64)
        .collect::<Vec<_>>()
}

/// O(n c)
pub fn multiple_knapsack(v: &[u64], w: &[u64], k: &[usize], c: u64) -> Vec<u64> {
    let n = v.len();
    let cap = c as usize;
    let mut dp = vec![0i64; cap + 1];
    for i in 0..n {
        let weight = w[i] as usize;
        let value = v[i] as i64;
        let cnt = k[i];
        if weight == 0 {
            continue;
        }
        let mut new_dp = dp.clone();
        for r in 0..weight.min(cap + 1) {
            let mut mq = MonotoneQueue::with_capacity(cnt + 1, |a, b| a > b);
            for x in 0..=(cap - r) / weight {
                let j = x * weight + r;
                mq.push_back(dp[j] - (x as i64) * value);
                if x >= cnt + 1 {
                    let old_x = x - (cnt + 1);
                    mq.pop_front(&(dp[old_x * weight + r] - (old_x as i64) * value));
                }
                if let Some(&best_g) = mq.min() {
                    new_dp[j] = best_g + (x as i64) * value;
                }
            }
        }
        dp = new_dp;
    }
    dp.into_iter().map(|v| v as u64).collect()
}

/// O(n + c log c)
pub fn multiple_knapsack_eq<const M: u64>(w: &[usize], k: &[usize], c: usize) -> Vec<u64> {
    (FPS::<M>::log_prod_1pxit(-1, k.into_iter().zip(w).map(|(&i, &j)| (i + 1) * j), c + 1)
        - FPS::<M>::log_prod_1pxit(-1, w.into_iter().cloned(), c + 1))
    .exp(c + 1)
    .unwrap()
    .coeff
    .into_iter()
    .map(|i| i.rem_euclid(M as i64) as u64)
    .collect::<Vec<_>>()
}

use std::time::{SystemTime, UNIX_EPOCH};

// Adjust this path to your library layout.
use crate::math::factor::{factor, miller_rabin};

#[inline]
fn mul_mod(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

#[derive(Clone, Debug)]
struct SplitMix64 {
    x: u64,
}

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self { x: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.x = self.x.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.x;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
}

fn entropy_seed() -> u64 {
    let t = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0x9e3779b97f4a7c15);

    t ^ (&t as *const u64 as usize as u64).rotate_left(17)
}

fn next_prime_at_least(mut x: u64) -> u64 {
    const MR_LIMIT: u64 = 7_000_000_000_000_000_000;

    if x <= 2 {
        return 2;
    }
    if x % 2 == 0 {
        x += 1;
    }

    while x <= MR_LIMIT {
        if miller_rabin(x) {
            return x;
        }
        x += 2;
    }

    panic!("failed to generate a Miller-Rabin-supported prime");
}

fn hash_prime_for_universe(universe: usize) -> u64 {
    let u = universe.max(2) as u128;
    let lg = (usize::BITS - universe.max(2).leading_zeros()) as u128;

    // Large enough for the Monte Carlo polynomial identity tests in practical
    // memory-feasible cases. We cap below the stated deterministic MR range.
    let want = 16u128
        .saturating_mul(u)
        .saturating_mul(u)
        .saturating_mul(u)
        .saturating_mul(lg)
        .saturating_add(100);

    let want = want.max(1_000_000_007).min(6_900_000_000_000_000_000u128) as u64;

    next_prime_at_least(want)
}

#[derive(Clone, Debug)]
struct FenwickMod {
    bit: Vec<u64>,
    modu: u64,
}

impl FenwickMod {
    fn new(n: usize, modu: u64) -> Self {
        Self {
            bit: vec![0; n],
            modu,
        }
    }

    fn add(&mut self, mut i: usize, x: u64) {
        while i < self.bit.len() {
            self.bit[i] = ((self.bit[i] as u128 + x as u128) % self.modu as u128) as u64;
            i |= i + 1;
        }
    }

    fn prefix(&self, mut i: usize) -> u64 {
        let mut res = 0u64;

        while i > 0 {
            res = ((res as u128 + self.bit[i - 1] as u128) % self.modu as u128) as u64;
            i &= i - 1;
        }

        res
    }

    fn range(&self, l: usize, r: usize) -> u64 {
        let a = self.prefix(r);
        let b = self.prefix(l);
        if a >= b { a - b } else { a + self.modu - b }
    }
}

#[derive(Clone, Debug)]
pub struct ModularSubsetSum {
    pub modu: usize,
    pub reachable: Vec<bool>,
    prev: Vec<usize>,
    picked: Vec<usize>,
}

impl ModularSubsetSum {
    pub fn contains(&self, target: usize) -> bool {
        self.reachable[target % self.modu]
    }

    pub fn recover_indices(&self, target: usize) -> Option<Vec<usize>> {
        let mut x = target % self.modu;
        if !self.reachable[x] {
            return None;
        }
        let mut out = Vec::new();
        while x != 0 {
            let i = self.picked[x];
            if i == usize::MAX {
                return None;
            }
            out.push(i);
            x = self.prev[x];
        }
        out.reverse();
        Some(out)
    }
}

fn find_new_sums(
    modu: usize,
    x: usize,
    reachable: &[bool],
    bit: &FenwickMod,
    pow: &[u64],
    prime: u64,
    out: &mut Vec<usize>,
) {
    debug_assert!(x < modu);

    let mut stack = vec![(0usize, modu)];

    while let Some((a, b)) = stack.pop() {
        let shifted_hash = bit.range(modu + a - x, modu + b - x);
        let base_hash = bit.range(a, b);
        let expected_shifted_hash = mul_mod(pow[modu - x], base_hash, prime);

        if shifted_hash == expected_shifted_hash {
            continue;
        }

        if b == a + 1 {
            let src = (a + modu - x) % modu;
            if !reachable[a] && reachable[src] {
                out.push(a);
            }
            continue;
        }

        let mid = (a + b) >> 1;
        stack.push((mid, b));
        stack.push((a, mid));
    }
}

/// O(M + n + |X*| log^2 M)
pub fn modular_subset_sum_seeded(modu: usize, xs: &[usize], seed: u64) -> ModularSubsetSum {
    assert!(modu > 0);

    let mut reachable = vec![false; modu];
    let mut prev = vec![usize::MAX; modu];
    let mut picked = vec![usize::MAX; modu];

    reachable[0] = true;
    prev[0] = 0;

    if modu == 1 {
        return ModularSubsetSum {
            modu,
            reachable,
            prev,
            picked,
        };
    }

    let prime = hash_prime_for_universe(modu.max(xs.len() + 1));
    let mut rng = SplitMix64::new(seed ^ 0x243f6a8885a308d3);
    let r = 1 + rng.next_u64() % (prime - 1);

    let mut pow = vec![0u64; 2 * modu + 1];
    pow[0] = 1;
    for i in 0..2 * modu {
        pow[i + 1] = mul_mod(pow[i], r, prime);
    }

    let mut bit = FenwickMod::new(2 * modu, prime);
    bit.add(0, pow[0]);
    bit.add(modu, pow[modu]);

    for (idx, &raw_x) in xs.iter().enumerate() {
        let x = raw_x % modu;
        if x == 0 {
            continue;
        }

        let mut add = Vec::new();
        find_new_sums(modu, x, &reachable, &bit, &pow, prime, &mut add);

        for s in add {
            if reachable[s] {
                continue;
            }

            let p = (s + modu - x) % modu;
            debug_assert!(reachable[p]);

            reachable[s] = true;
            prev[s] = p;
            picked[s] = idx;

            bit.add(s, pow[s]);
            bit.add(s + modu, pow[s + modu]);
        }
    }

    ModularSubsetSum {
        modu,
        reachable,
        prev,
        picked,
    }
}

pub fn modular_subset_sum(modu: usize, xs: &[usize]) -> ModularSubsetSum {
    modular_subset_sum_seeded(modu, xs, entropy_seed())
}

#[derive(Clone, Debug)]
pub struct APNP {
    /// par[u][v] is the predecessor of v on the discovered minimum
    /// non-decreasing path from u to v.
    pub par: Vec<Vec<Option<usize>>>,

    /// when[u][v] is the sorted edge phase when u first reached v.
    /// For u == v, this is Some(usize::MAX).
    pub when: Vec<Vec<Option<usize>>>,
}

impl APNP {
    pub fn reachable(&self, u: usize, v: usize) -> bool {
        self.par[u][v].is_some()
    }

    pub fn path(&self, u: usize, v: usize) -> Option<Vec<usize>> {
        self.par[u][v]?;

        if u == v {
            return Some(vec![u]);
        }

        let mut out = Vec::new();
        let mut x = v;

        out.push(x);

        while x != u {
            x = self.par[u][x]?;
            out.push(x);
        }

        out.reverse();
        Some(out)
    }
}

fn apnp_find_new(
    a: usize,
    b: usize,
    node: usize,
    n: usize,
    base: usize,
    tree: &[Vec<u64>],
    par: &[Vec<Option<usize>>],
    out: &mut Vec<(usize, usize, usize)>,
) {
    if tree[a][node] == tree[b][node] {
        return;
    }

    if node >= base {
        let u = node - base;

        if u < n {
            if par[u][a].is_none() {
                // u reaches b but not a, so new path u -> a has predecessor b.
                out.push((u, a, b));
            } else {
                // u reaches a but not b, so new path u -> b has predecessor a.
                out.push((u, b, a));
            }
        }

        return;
    }

    apnp_find_new(a, b, node << 1, n, base, tree, par, out);
    apnp_find_new(a, b, node << 1 | 1, n, base, tree, par, out);
}

fn apnp_update(tree: &mut [Vec<u64>], prime: u64, v: usize, mut node: usize, val: u64) {
    while node > 0 {
        tree[v][node] = ((tree[v][node] as u128 + val as u128) % prime as u128) as u64;
        node >>= 1;
    }
}

/// Strict/distinct-weight undirected APNP kernel.
///
/// `edges_sorted` must be sorted by increasing edge weight, with no equal-weight
/// issue left unresolved. If your input has equal weights, reduce/tie-expand
/// before calling this, or this computes the strict/tie-broken variant.
pub fn apnp_undirected_strict_sorted_seeded(
    n: usize,
    edges_sorted: &[(usize, usize)],
    seed: u64,
) -> APNP {
    if n == 0 {
        return APNP {
            par: Vec::new(),
            when: Vec::new(),
        };
    }

    let prime = hash_prime_for_universe(n);
    let mut rng = SplitMix64::new(seed ^ 0x13198a2e03707344);
    let r = 1 + rng.next_u64() % (prime - 1);

    let mut pow = vec![1u64; n.max(1)];
    for i in 1..n {
        pow[i] = mul_mod(pow[i - 1], r, prime);
    }

    let base = n.next_power_of_two();
    let mut tree = vec![vec![0u64; 2 * base]; n];

    let mut par = vec![vec![None; n]; n];
    let mut when = vec![vec![None; n]; n];

    for i in 0..n {
        par[i][i] = Some(i);
        when[i][i] = Some(usize::MAX);
        apnp_update(&mut tree, prime, i, base + i, pow[i]);
    }

    for (phase, &(a, b)) in edges_sorted.iter().enumerate() {
        assert!(a < n && b < n);

        let mut add = Vec::new();
        apnp_find_new(a, b, 1, n, base, &tree, &par, &mut add);

        for (u, v, p) in add {
            if par[u][v].is_none() {
                par[u][v] = Some(p);
                when[u][v] = Some(phase);
                apnp_update(&mut tree, prime, v, base + u, pow[u]);
            }
        }
    }

    APNP { par, when }
}

pub fn apnp_undirected_strict_sorted(n: usize, edges_sorted: &[(usize, usize)]) -> APNP {
    apnp_undirected_strict_sorted_seeded(n, edges_sorted, entropy_seed())
}

pub fn apnp_undirected_distinct_by_key<W: Ord + Copy>(
    n: usize,
    edges: &[(usize, usize, W)],
) -> APNP {
    let mut ids: Vec<usize> = (0..edges.len()).collect();
    ids.sort_unstable_by_key(|&i| edges[i].2);

    let sorted: Vec<(usize, usize)> = ids.into_iter().map(|i| (edges[i].0, edges[i].1)).collect();

    apnp_undirected_strict_sorted(n, &sorted)
}

/* ------------------------------------------------------------------------- */
/* Erdős–Ginzburg–Ziv                                                        */
/* ------------------------------------------------------------------------- */

fn largest_prime_factor(n: usize) -> usize {
    factor(n).into_iter().max().unwrap()
}

fn egz_prime_positions_seeded(p: usize, items: &[(usize, usize)], seed: u64) -> Option<Vec<usize>> {
    debug_assert!(items.len() >= 2 * p - 1);

    if p == 1 {
        return Some(vec![0]);
    }

    if p == 2 {
        let mut first = [usize::MAX; 2];

        for i in 0..3 {
            let r = items[i].0 & 1;
            if first[r] != usize::MAX {
                return Some(vec![first[r], i]);
            }
            first[r] = i;
        }

        return None;
    }

    let mut a: Vec<(usize, usize)> = (0..2 * p - 1).map(|i| (items[i].0 % p, i)).collect();

    a.sort_unstable_by_key(|&(x, _)| x);

    for i in 0..p {
        if a[i].0 == a[i + p - 1].0 {
            return Some(a[i..i + p].iter().map(|&(_, pos)| pos).collect());
        }
    }

    let c = a[..p].iter().fold(0usize, |s, &(x, _)| (s + x) % p);

    if c == 0 {
        return Some(a[..p].iter().map(|&(_, pos)| pos).collect());
    }

    let b: Vec<usize> = (0..p - 1)
        .map(|i| (a[i + p].0 + p - a[i + 1].0) % p)
        .collect();

    let target = (p - c) % p;

    for attempt in 0..24u64 {
        let ms = modular_subset_sum_seeded(
            p,
            &b,
            seed ^ 0x9e3779b97f4a7c15u64.wrapping_mul(attempt + 1),
        );

        let Some(sub) = ms.recover_indices(target) else {
            continue;
        };

        let check = sub.iter().fold(0usize, |s, &i| (s + b[i]) % p);
        if check != target {
            continue;
        }

        let mut use_first = vec![true; p];

        for &i in &sub {
            use_first[i + 1] = false;
        }

        let mut out = Vec::with_capacity(p);

        for i in 0..p {
            if use_first[i] {
                out.push(a[i].1);
            }
        }

        for &i in &sub {
            out.push(a[i + p].1);
        }

        debug_assert_eq!(out.len(), p);

        return Some(out);
    }

    None
}

fn egz_rec_seeded(n: usize, items: Vec<(usize, usize)>, seed: u64) -> Option<Vec<usize>> {
    debug_assert!(items.len() >= 2 * n - 1);

    if n == 1 {
        return Some(vec![items[0].1]);
    }

    if miller_rabin(n as u64) {
        let pos = egz_prime_positions_seeded(n, &items, seed)?;
        return Some(pos.into_iter().map(|i| items[i].1).collect());
    }

    let u = largest_prime_factor(n);
    let v = n / u;

    let mut rem = items[..2 * n - 1].to_vec();

    let mut block_items: Vec<(usize, usize)> = Vec::with_capacity(2 * v - 1);
    let mut blocks: Vec<Vec<usize>> = Vec::with_capacity(2 * v - 1);

    for block_id in 0..2 * v - 1 {
        let take_len = 2 * u - 1;
        let take: Vec<(usize, usize)> = rem[..take_len].to_vec();

        let chosen_pos = egz_prime_positions_seeded(
            u,
            &take,
            seed ^ ((block_id as u64 + 1).wrapping_mul(0xbf58476d1ce4e5b9)),
        )?;

        let mut mark = vec![false; rem.len()];
        let mut sum = 0u128;
        let mut original_indices = Vec::with_capacity(u);

        for &pos in &chosen_pos {
            mark[pos] = true;
            sum += take[pos].0 as u128;
            original_indices.push(take[pos].1);
        }

        debug_assert_eq!((sum % u as u128) as usize, 0);

        let c = ((sum / u as u128) % v as u128) as usize;

        block_items.push((c, block_id));
        blocks.push(original_indices);

        rem = rem
            .into_iter()
            .enumerate()
            .filter_map(|(i, item)| if mark[i] { None } else { Some(item) })
            .collect();
    }

    let chosen_blocks = egz_rec_seeded(
        v,
        block_items,
        seed ^ 0x94d049bb133111ebu64.wrapping_mul(n as u64 + 1),
    )?;

    let mut out = Vec::with_capacity(n);

    for block_id in chosen_blocks {
        out.extend(blocks[block_id].iter().copied());
    }

    debug_assert_eq!(out.len(), n);

    Some(out)
}

/// O(n log^2 n)
pub fn erdos_ginzburg_ziv(n: usize, a: &[usize], seed: u64) -> Option<Vec<usize>> {
    assert!(n > 0);
    assert!(a.len() >= 2 * n - 1, "EGZ needs at least 2n-1 inputs");

    let items: Vec<(usize, usize)> = a
        .iter()
        .take(2 * n - 1)
        .enumerate()
        .map(|(i, &x)| (x % n, i))
        .collect();

    for attempt in 0..16u64 {
        let out = egz_rec_seeded(
            n,
            items.clone(),
            seed ^ attempt.wrapping_mul(0x9e3779b97f4a7c15),
        )?;

        if out.len() == n {
            let s = out.iter().fold(0usize, |acc, &i| (acc + a[i] % n) % n);

            if s == 0 {
                return Some(out);
            }
        }
    }

    None
}

// TODO: some of the cases here
// https://codeforces.com/blog/entry/98663
