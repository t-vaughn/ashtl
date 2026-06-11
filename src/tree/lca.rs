use crate::range::rmq::RMQ;
use std::cmp::Ordering;

pub struct LCA<'a> {
    p: &'a [usize],
    dfs: &'a [usize],
    pos: &'a [usize],
    rmq: RMQ<usize>,
}

impl<'a> LCA<'a> {
    /// O(n)
    pub fn new(p: &'a [usize], dfs: &'a [usize], pos: &'a [usize], depth: &[usize]) -> Self {
        let n = dfs.len();
        let z: Vec<usize> = (0..n).map(|i| depth[p[dfs[i]]]).collect();
        Self {
            p,
            dfs,
            pos,
            rmq: RMQ::new(z),
        }
    }

    /// O(1)
    pub fn query(&self, a: usize, b: usize) -> usize {
        if a == b {
            return a;
        }
        let (l, r) = if self.pos[a] <= self.pos[b] {
            (self.pos[a], self.pos[b])
        } else {
            (self.pos[b], self.pos[a])
        };
        self.p[self.dfs[self.rmq.query(l + 1..=r)]]
    }
}

/// builds jump table for binary lifting in O(n)
pub fn build_jmp(par: &[usize], dfs: &[usize], depth: &[usize]) -> Vec<usize> {
    let n = par.len();
    let mut jmp = vec![0; n];
    for &v in dfs {
        let p = par[v];
        if v == p {
            jmp[v] = v;
        } else {
            let pj = jmp[p];
            let pjj = jmp[pj];
            if depth[p] - depth[pj] == depth[pj] - depth[pjj] {
                jmp[v] = pjj;
            } else {
                jmp[v] = p;
            }
        }
    }
    jmp
}

/// O(log n)
pub fn depth_jmp(mut u: usize, d: usize, par: &[usize], jmp: &[usize], depth: &[usize]) -> usize {
    while depth[u] > d {
        if depth[jmp[u]] < d {
            u = par[u];
        } else {
            u = jmp[u];
        }
    }
    u
}

/// O(log n)
pub fn search_jmp(
    mut u: usize,
    mut p: impl FnMut(usize) -> bool,
    par: &[usize],
    jmp: &[usize],
) -> usize {
    while !p(u) {
        if p(jmp[u]) {
            u = par[u];
        } else {
            u = jmp[u];
        }
    }
    u
}

/// O(log n)
pub fn lca_jmp(mut u: usize, mut v: usize, par: &[usize], jmp: &[usize], depth: &[usize]) -> usize {
    if depth[u] > depth[v] {
        (u, v) = (v, u);
    }
    v = depth_jmp(v, depth[u], par, jmp, depth);
    while u != v {
        if jmp[u] == jmp[v] {
            (u, v) = (par[u], par[v]);
        } else {
            (u, v) = (jmp[u], jmp[v]);
        }
    }
    u
}

#[derive(Clone, Debug)]
struct LANode {
    depth: usize,
    parent: usize,
    idx: usize,
    down_leaf: usize,
    ladder: Vec<usize>,
}

#[derive(Clone, Debug)]
pub struct LevelAncestor {
    t: Vec<LANode>,
    jump: Vec<(usize, usize)>,
}

impl LevelAncestor {
    /// O(n)
    pub fn new(adj: &[Vec<usize>]) -> Self {
        let n = adj.len();
        if n == 0 {
            return Self {
                t: Vec::new(),
                jump: Vec::new(),
            };
        }
        const NONE: usize = usize::MAX;
        let mut t = vec![
            LANode {
                depth: 0,
                parent: NONE,
                idx: 0,
                down_leaf: 0,
                ladder: Vec::new(),
            };
            n
        ];
        let mut jump = vec![(0, 0); 2 * n];
        let mut path: Vec<usize> = Vec::new();
        let mut pos = 1;

        fn add_jump(path: &[usize], jump: &mut [(usize, usize)], pos: &mut usize) {
            let lb = *pos & pos.wrapping_neg();
            let last = path.len() - 1;
            let j1 = path[last.saturating_sub(2 * lb)];
            let j2 = path[last.saturating_sub(4 * lb)];
            jump[*pos] = (j1, j2);
            *pos += 1;
        }

        #[derive(Clone, Copy)]
        struct Frame {
            v: usize,
            next: usize,
        }

        for root in 0..n {
            if t[root].parent != NONE {
                continue;
            }
            t[root].parent = root;
            t[root].depth = 0;
            t[root].idx = pos;
            t[root].down_leaf = root;
            path.push(root);
            add_jump(&path, &mut jump, &mut pos);
            let mut stack = vec![Frame { v: root, next: 0 }];
            while !stack.is_empty() {
                let top = stack.len() - 1;
                let v = stack[top].v;
                if stack[top].next < adj[v].len() {
                    let u = adj[v][stack[top].next];
                    stack[top].next += 1;
                    if u == t[v].parent || t[u].parent != NONE {
                        continue;
                    }
                    t[u].parent = v;
                    t[u].depth = t[v].depth + 1;
                    t[u].idx = pos;
                    t[u].down_leaf = u;
                    path.push(u);
                    add_jump(&path, &mut jump, &mut pos);
                    stack.push(Frame { v: u, next: 0 });
                } else {
                    stack.pop();
                    path.pop();
                    if let Some(parent_frame) = stack.last() {
                        let p = parent_frame.v;
                        let child_leaf = t[v].down_leaf;
                        if t[child_leaf].depth > t[t[p].down_leaf].depth {
                            t[p].down_leaf = child_leaf;
                        }
                        add_jump(&path, &mut jump, &mut pos);
                    }
                }
            }
        }
        for v in 0..n {
            let p = t[v].parent;
            if p == v || t[p].down_leaf != t[v].down_leaf {
                let leaf = t[v].down_leaf;
                let heavy_len = t[leaf].depth - t[v].depth;
                let len = (2 * heavy_len).min(t[leaf].depth + 1);
                t[leaf].ladder.resize(len, leaf);
                for k in 1..len {
                    let prev = t[leaf].ladder[k - 1];
                    t[leaf].ladder[k] = t[prev].parent;
                }
            }
        }
        Self { t, jump }
    }

    pub fn len(&self) -> usize {
        self.t.len()
    }

    pub fn is_empty(&self) -> bool {
        self.t.is_empty()
    }

    pub fn parent(&self, v: usize) -> usize {
        self.t[v].parent
    }

    pub fn depth(&self, v: usize) -> usize {
        self.t[v].depth
    }

    /// O(1)
    pub fn kth_ancestor(&self, v: usize, k: usize) -> usize {
        match k {
            0 => v,
            1 => self.t[v].parent,
            2 => self.t[self.t[v].parent].parent,
            _ => {
                let block = 1usize << ((k / 3).ilog2() as usize);
                let j_idx = (self.t[v].idx & !(block - 1)) | block;
                let (j1, j2) = self.jump[j_idx];
                let jump_node = if self.t[v].depth - self.t[j2].depth <= k {
                    j2
                } else {
                    j1
                };
                let leaf = self.t[jump_node].down_leaf;
                let ladder_idx = k + self.t[leaf].depth - self.t[v].depth;
                self.t[leaf].ladder[ladder_idx]
            }
        }
    }

    /// O(1), given the LCA node.
    pub fn kth_on_path_given_lca(&self, u: usize, v: usize, lca: usize, k: usize) -> Option<usize> {
        let u_lca = self.depth(u) - self.depth(lca);
        let v_lca = self.depth(v) - self.depth(lca);
        let path_len = u_lca + v_lca;
        if k > path_len {
            return None;
        }
        if k <= u_lca {
            Some(self.kth_ancestor(u, k))
        } else {
            Some(self.kth_ancestor(v, path_len - k))
        }
    }

    /// O(1), given the LCA through a closure.
    pub fn kth_on_path(
        &self,
        u: usize,
        v: usize,
        k: usize,
        mut lca_query: impl FnMut(usize, usize) -> usize,
    ) -> Option<usize> {
        let lca = lca_query(u, v);
        self.kth_on_path_given_lca(u, v, lca, k)
    }
}

// TODO: level ancestor, ladder decomposition
// https://codeforces.com/blog/entry/126580
// https://codeforces.com/blog/entry/52062?#comment-360824
// https://codeforces.com/blog/entry/71567?#comment-559299
// https://courses.csail.mit.edu/6.851/spring21/lectures/L15.html?notes=8

#[cfg(test)]
mod level_ancestor_tests {
    use super::LevelAncestor;

    #[derive(Clone)]
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

        fn usize(&mut self, n: usize) -> usize {
            (self.next_u64() as usize) % n
        }
    }

    fn add_edge(adj: &mut [Vec<usize>], u: usize, v: usize) {
        adj[u].push(v);
        adj[v].push(u);
    }

    fn naive_kth_ancestor(la: &LevelAncestor, mut v: usize, k: usize) -> usize {
        for _ in 0..k {
            v = la.parent(v);
        }
        v
    }

    fn naive_lca(la: &LevelAncestor, mut a: usize, mut b: usize) -> usize {
        while la.depth(a) > la.depth(b) {
            a = la.parent(a);
        }
        while la.depth(b) > la.depth(a) {
            b = la.parent(b);
        }
        while a != b {
            a = la.parent(a);
            b = la.parent(b);
        }
        a
    }

    fn naive_path_nodes(la: &LevelAncestor, u: usize, v: usize) -> Vec<usize> {
        let l = naive_lca(la, u, v);

        let mut left = Vec::new();
        let mut x = u;
        while x != l {
            left.push(x);
            x = la.parent(x);
        }
        left.push(l);

        let mut right = Vec::new();
        let mut x = v;
        while x != l {
            right.push(x);
            x = la.parent(x);
        }
        right.reverse();

        left.extend(right);
        left
    }

    #[test]
    fn level_ancestor_empty() {
        let adj: Vec<Vec<usize>> = Vec::new();
        let la = LevelAncestor::new(&adj);
        assert_eq!(la.len(), 0);
        assert!(la.is_empty());
    }

    #[test]
    fn level_ancestor_singleton() {
        let adj = vec![Vec::new()];
        let la = LevelAncestor::new(&adj);

        assert_eq!(la.len(), 1);
        assert_eq!(la.depth(0), 0);
        assert_eq!(la.parent(0), 0);
        assert_eq!(la.kth_ancestor(0, 0), 0);
        assert_eq!(la.kth_on_path_given_lca(0, 0, 0, 0), Some(0));
        assert_eq!(la.kth_on_path(0, 0, 0, |_a, _b| 0), Some(0));
        assert_eq!(la.kth_on_path_given_lca(0, 0, 0, 1), None);
    }

    #[test]
    fn level_ancestor_chain() {
        let n = 16;
        let mut adj = vec![Vec::new(); n];

        for i in 1..n {
            add_edge(&mut adj, i - 1, i);
        }

        let la = LevelAncestor::new(&adj);

        for v in 0..n {
            assert_eq!(la.depth(v), v);

            for k in 0..=v {
                assert_eq!(
                    la.kth_ancestor(v, k),
                    v - k,
                    "bad kth ancestor for v={v}, k={k}"
                );
            }
        }

        let u = 14;
        let v = 3;
        let path = naive_path_nodes(&la, u, v);

        for k in 0..path.len() {
            assert_eq!(
                la.kth_on_path(u, v, k, |a, b| naive_lca(&la, a, b)),
                Some(path[k]),
                "bad kth_on_path on chain for k={k}"
            );
        }

        assert_eq!(
            la.kth_on_path(u, v, path.len(), |a, b| naive_lca(&la, a, b)),
            None
        );
    }

    #[test]
    fn level_ancestor_star() {
        let n = 12;
        let mut adj = vec![Vec::new(); n];

        for v in 1..n {
            add_edge(&mut adj, 0, v);
        }

        let la = LevelAncestor::new(&adj);

        assert_eq!(la.kth_ancestor(0, 0), 0);

        for v in 1..n {
            assert_eq!(la.depth(v), 1);
            assert_eq!(la.parent(v), 0);
            assert_eq!(la.kth_ancestor(v, 0), v);
            assert_eq!(la.kth_ancestor(v, 1), 0);
        }

        for u in 1..n {
            for v in 1..n {
                let path = naive_path_nodes(&la, u, v);
                for k in 0..path.len() {
                    assert_eq!(
                        la.kth_on_path(u, v, k, |a, b| naive_lca(&la, a, b)),
                        Some(path[k]),
                        "bad kth_on_path in star, u={u}, v={v}, k={k}"
                    );
                }
            }
        }
    }

    #[test]
    fn level_ancestor_binary_tree() {
        let n = 31;
        let mut adj = vec![Vec::new(); n];

        for v in 1..n {
            add_edge(&mut adj, (v - 1) / 2, v);
        }

        let la = LevelAncestor::new(&adj);

        for v in 0..n {
            for k in 0..=la.depth(v) {
                assert_eq!(
                    la.kth_ancestor(v, k),
                    naive_kth_ancestor(&la, v, k),
                    "bad kth ancestor in binary tree, v={v}, k={k}"
                );
            }
        }

        for u in 0..n {
            for v in 0..n {
                let path = naive_path_nodes(&la, u, v);

                for k in 0..path.len() {
                    assert_eq!(
                        la.kth_on_path_given_lca(u, v, naive_lca(&la, u, v), k),
                        Some(path[k]),
                        "bad kth_on_path in binary tree, u={u}, v={v}, k={k}"
                    );
                }

                assert_eq!(
                    la.kth_on_path_given_lca(u, v, naive_lca(&la, u, v), path.len()),
                    None
                );
            }
        }
    }

    #[test]
    fn level_ancestor_forest() {
        let n = 10;
        let mut adj = vec![Vec::new(); n];

        // Component 1: 0 - 1 - 2 - 3
        add_edge(&mut adj, 0, 1);
        add_edge(&mut adj, 1, 2);
        add_edge(&mut adj, 2, 3);

        // Component 2: 4 centered star
        add_edge(&mut adj, 4, 5);
        add_edge(&mut adj, 4, 6);
        add_edge(&mut adj, 4, 7);

        // Component 3: 8 - 9
        add_edge(&mut adj, 8, 9);

        let la = LevelAncestor::new(&adj);

        for v in 0..n {
            for k in 0..=la.depth(v) {
                assert_eq!(
                    la.kth_ancestor(v, k),
                    naive_kth_ancestor(&la, v, k),
                    "bad kth ancestor in forest, v={v}, k={k}"
                );
            }
        }

        assert_eq!(la.kth_ancestor(3, 3), 0);
        assert_eq!(la.kth_ancestor(7, 1), 4);
        assert_eq!(la.kth_ancestor(9, 1), 8);
    }

    #[test]
    fn level_ancestor_random_trees_against_naive() {
        let mut rng = SplitMix64::new(123456789);

        for n in [2usize, 3, 4, 5, 8, 17, 64, 127, 256] {
            for trial in 0..50 {
                let mut adj = vec![Vec::new(); n];

                // Random rooted tree with parent[v] < v, so vertex 0 is root.
                for v in 1..n {
                    let p = rng.usize(v);
                    add_edge(&mut adj, p, v);
                }

                // Shuffle adjacency order to make DFS order less predictable.
                for v in 0..n {
                    for i in 0..adj[v].len() {
                        let j = rng.usize(adj[v].len());
                        adj[v].swap(i, j);
                    }
                }

                let la = LevelAncestor::new(&adj);

                for v in 0..n {
                    for k in 0..=la.depth(v) {
                        assert_eq!(
                            la.kth_ancestor(v, k),
                            naive_kth_ancestor(&la, v, k),
                            "bad kth ancestor, n={n}, trial={trial}, v={v}, k={k}"
                        );
                    }
                }

                for _ in 0..1000 {
                    let u = rng.usize(n);
                    let v = rng.usize(n);
                    let path = naive_path_nodes(&la, u, v);
                    let k = rng.usize(path.len() + 2);

                    let got = la.kth_on_path(u, v, k, |a, b| naive_lca(&la, a, b));
                    let want = path.get(k).copied();

                    assert_eq!(
                        got, want,
                        "bad kth_on_path, n={n}, trial={trial}, u={u}, v={v}, k={k}, path={path:?}"
                    );
                }
            }
        }
    }

    #[test]
    #[should_panic]
    fn level_ancestor_panics_above_root() {
        let mut adj = vec![Vec::new(); 3];
        add_edge(&mut adj, 0, 1);
        add_edge(&mut adj, 1, 2);

        let la = LevelAncestor::new(&adj);
        let _ = la.kth_ancestor(2, 3);
    }
}
