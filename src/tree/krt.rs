use super::lca::LCA;
use crate::range::rmq::RMQ;
use std::cmp::{Ordering, Reverse};
use std::ops::Range;

/// Kruskal reconstruction tree
pub struct KRT<F: FnMut(usize, usize, usize)> {
    pub n: usize,
    pub chs: Vec<[usize; 2]>,
    pub nxt: usize,
    pub p: Vec<usize>,
    pub idx: Vec<usize>,
    pub dsu: Vec<usize>,
    pub on_union: F,
}

impl<F: FnMut(usize, usize, usize)> KRT<F> {
    pub fn new(n: usize, on_union: F) -> Self {
        let mut dsu = Vec::with_capacity(n << 1);
        dsu.extend(0..n << 1);
        let mut p = Vec::with_capacity(n << 1);
        p.extend(0..n << 1);
        Self {
            n,
            chs: vec![[usize::MAX; 2]; n << 1],
            nxt: n,
            p,
            idx: vec![usize::MAX; n],
            dsu,
            on_union,
        }
    }

    /// O(log n)
    pub fn find(&mut self, mut x: usize) -> usize {
        while self.dsu[x] != x {
            let p = self.dsu[x];
            self.dsu[x] = self.dsu[p];
            x = p;
        }
        x
    }

    /// O(log n)
    pub fn add_edge(&mut self, u: usize, v: usize, idx: usize) -> &mut Self {
        let (ru, rv) = (self.find(u), self.find(v));
        if ru != rv {
            self.chs[self.nxt] = [ru, rv];
            self.idx[self.nxt - self.n] = idx;
            (self.p[ru], self.p[rv]) = (self.nxt, self.nxt);
            self.dsu[ru] = self.nxt;
            self.dsu[rv] = self.nxt;
            self.nxt += 1;
            (self.on_union)(ru, rv, self.nxt);
        }
        self
    }

    /// O(n)
    pub fn dfs(&self) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
        let k = self.nxt;
        let mut ss = vec![1; k];
        let mut depth = vec![0; k];
        let mut pos = vec![0; k];
        let mut dfs = vec![0; k];
        for u in 0..k - 1 {
            ss[self.p[u]] += ss[u];
        }
        pos.copy_from_slice(&ss);
        for u in (0..k - 1).rev() {
            let v = self.p[u];
            depth[u] = depth[v] + 1;
            (pos[u], pos[v]) = (pos[v], pos[v] - pos[u]);
        }
        for i in 0..k {
            pos[i] -= 1;
            dfs[pos[i]] = i;
        }
        (ss, pos, dfs, depth)
    }

    /// O(n) construction, O(1) query
    pub fn leaf_pos_rmq(&self, pos: &[usize]) -> (RMQ<usize>, RMQ<usize>) {
        (RMQ::new(pos), RMQ::new(pos))
    }

    /// O(n) construction O(1) query
    pub fn lca<'a>(&'a self, dfs: &'a [usize], pos: &'a [usize], depth: &'a [usize]) -> LCA<'a> {
        let k = self.nxt;
        let mut z = Vec::with_capacity(k);
        z.extend((0..k).map(|i| depth[self.p[dfs[i]]]));
        LCA::new(&self.p, dfs, pos, depth)
    }
}

// TODO: line tree
// https://codeforces.com/blog/entry/71568

// /// A line tree of a weighted tree.
// ///
// /// `ord` is the vertex order on the line.
// /// `pos[v]` is the position of original tree vertex `v` on the line.
// /// For each `i`, line edge `i` lies between `ord[i]` and `ord[i + 1]`.
// ///
// /// `edge_idx[i]` is the original tree-edge id assigned to line edge `i`.
// /// `edge_dir[i] = (a,b)` is the direction of that original tree edge when
// /// crossing the line edge from left to right.
// #[derive(Clone, Debug)]
// pub struct LineTree {
//     pub ord: Vec<usize>,
//     pub pos: Vec<usize>,
//     pub edge_idx: Vec<usize>,
//     pub edge_dir: Vec<(usize, usize)>,
// }

// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
// pub struct DirectedLineEdge {
//     pub edge_idx: usize,
//     pub from: usize,
//     pub to: usize,
// }

// impl LineTree {
//     /// O(n log n), or O(n) if the comparator is consistent with an already sorted order
//     /// but this function still performs the sort.
//     ///
//     /// `tree_edges[eid] = (u,v)`.
//     ///
//     /// `cmp_edge(a,b)` must order edge ids by nondecreasing tree-edge weight.
//     /// Ties may be broken arbitrarily.
//     pub fn from_tree_by(
//         n: usize,
//         tree_edges: &[(usize, usize)],
//         mut cmp_edge: impl FnMut(usize, usize) -> Ordering,
//     ) -> Self {
//         assert_eq!(
//             tree_edges.len(),
//             n.saturating_sub(1),
//             "LineTree::from_tree_by expects a tree: got n={} and {} edges",
//             n,
//             tree_edges.len()
//         );

//         let mut order: Vec<usize> = (0..tree_edges.len()).collect();

//         order.sort_unstable_by(|&a, &b| cmp_edge(a, b).then_with(|| a.cmp(&b)));

//         Self::from_tree_sorted(n, tree_edges, &order)
//     }

//     /// O(n), assuming `order` lists the tree edges in nondecreasing weight.
//     ///
//     /// This is the direct linked-list/DSU construction of the line tree.
//     pub fn from_tree_sorted(n: usize, tree_edges: &[(usize, usize)], order: &[usize]) -> Self {
//         assert_eq!(
//             tree_edges.len(),
//             n.saturating_sub(1),
//             "LineTree::from_tree_sorted expects a tree: got n={} and {} edges",
//             n,
//             tree_edges.len()
//         );
//         assert_eq!(order.len(), tree_edges.len());

//         if n == 0 {
//             return Self {
//                 ord: Vec::new(),
//                 pos: Vec::new(),
//                 edge_idx: Vec::new(),
//                 edge_dir: Vec::new(),
//             };
//         }

//         if n == 1 {
//             return Self {
//                 ord: vec![0],
//                 pos: vec![0],
//                 edge_idx: Vec::new(),
//                 edge_dir: Vec::new(),
//             };
//         }

//         fn find(dsu: &mut [usize], mut x: usize) -> usize {
//             let mut r = x;
//             while dsu[r] != r {
//                 r = dsu[r];
//             }
//             while dsu[x] != x {
//                 let p = dsu[x];
//                 dsu[x] = r;
//                 x = p;
//             }
//             r
//         }

//         let mut dsu: Vec<usize> = (0..n).collect();
//         let mut size = vec![1usize; n];

//         // Linked list of the current line order for each DSU component root.
//         let mut head: Vec<usize> = (0..n).collect();
//         let mut tail: Vec<usize> = (0..n).collect();

//         // If `next_vertex[x] != usize::MAX`, then in the final line order
//         // vertex `x` is followed by `next_vertex[x]`.
//         let mut next_vertex = vec![usize::MAX; n];

//         // Data for the line edge from `x` to `next_vertex[x]`.
//         let mut next_edge_idx = vec![usize::MAX; n];
//         let mut next_edge_dir = vec![(usize::MAX, usize::MAX); n];

//         let mut unions = 0usize;

//         for &eid in order {
//             assert!(eid < tree_edges.len());

//             let (mut u, mut v) = tree_edges[eid];

//             assert!(
//                 u < n && v < n,
//                 "tree edge {} has endpoint outside 0..{}: ({},{})",
//                 eid,
//                 n,
//                 u,
//                 v
//             );

//             let mut ru = find(&mut dsu, u);
//             let mut rv = find(&mut dsu, v);

//             assert_ne!(
//                 ru, rv,
//                 "LineTree::from_tree_sorted received a non-tree ordering/input: edge {} closes a cycle",
//                 eid
//             );

//             // Union by size. If we swap components, also swap the original edge
//             // direction so that `u -> v` always points from the left component
//             // to the right component in the newly concatenated line.
//             if size[ru] < size[rv] {
//                 std::mem::swap(&mut ru, &mut rv);
//                 std::mem::swap(&mut u, &mut v);
//             }

//             // Concatenate line(ru) + edge eid + line(rv).
//             let left_tail = tail[ru];
//             let right_head = head[rv];

//             next_vertex[left_tail] = right_head;
//             next_edge_idx[left_tail] = eid;
//             next_edge_dir[left_tail] = (u, v);

//             tail[ru] = tail[rv];
//             size[ru] += size[rv];
//             dsu[rv] = ru;

//             unions += 1;
//         }

//         assert_eq!(
//             unions,
//             n - 1,
//             "LineTree::from_tree_sorted did not connect all vertices"
//         );

//         let root = find(&mut dsu, 0);
//         assert_eq!(
//             size[root], n,
//             "LineTree::from_tree_sorted input was not connected"
//         );

//         let mut ord = Vec::with_capacity(n);
//         let mut pos = vec![usize::MAX; n];
//         let mut edge_idx = Vec::with_capacity(n - 1);
//         let mut edge_dir = Vec::with_capacity(n - 1);

//         let mut x = head[root];

//         loop {
//             pos[x] = ord.len();
//             ord.push(x);

//             let y = next_vertex[x];
//             if y == usize::MAX {
//                 break;
//             }

//             edge_idx.push(next_edge_idx[x]);
//             edge_dir.push(next_edge_dir[x]);

//             x = y;
//         }

//         assert_eq!(ord.len(), n);
//         assert_eq!(edge_idx.len(), n - 1);
//         assert_eq!(edge_dir.len(), n - 1);

//         Self {
//             ord,
//             pos,
//             edge_idx,
//             edge_dir,
//         }
//     }

//     /// Convenience constructor when weights are stored separately.
//     pub fn from_tree_weights<K: Ord>(
//         n: usize,
//         tree_edges: &[(usize, usize)],
//         weight: &[K],
//     ) -> Self {
//         assert_eq!(tree_edges.len(), weight.len());

//         Self::from_tree_by(n, tree_edges, |a, b| weight[a].cmp(&weight[b]))
//     }

//     /// The line-edge range corresponding to the path between `u` and `v`.
//     ///
//     /// Line edge `i` lies between `ord[i]` and `ord[i + 1]`, so if
//     /// `pos[u] < pos[v]`, the relevant edge range is `pos[u]..pos[v]`.
//     pub fn edge_range(&self, u: usize, v: usize) -> Option<Range<usize>> {
//         let mut l = self.pos[u];
//         let mut r = self.pos[v];

//         if l == r {
//             return None;
//         }

//         if l > r {
//             std::mem::swap(&mut l, &mut r);
//         }

//         Some(l..r)
//     }

//     /// Build an RMQ for path maximum queries on the line.
//     ///
//     /// Since your `RMQ<K>` is a range-min structure, this stores `Reverse(key)`.
//     pub fn max_edge_rmq<K: Ord>(&self, mut key: impl FnMut(usize) -> K) -> RMQ<Reverse<K>> {
//         let a: Vec<Reverse<K>> = self.edge_idx.iter().map(|&eid| Reverse(key(eid))).collect();

//         RMQ::new(a)
//     }

//     /// Returns an original edge id attaining the maximum key on the original
//     /// tree path between `u` and `v`.
//     pub fn max_edge_with_rmq<K: Ord>(
//         &self,
//         u: usize,
//         v: usize,
//         rmq: &RMQ<Reverse<K>>,
//     ) -> Option<usize> {
//         let range = self.edge_range(u, v)?;
//         let p = rmq.query(range);
//         Some(self.edge_idx[p])
//     }

//     /// Same as `max_edge_with_rmq`, but returns the original tree edge directed
//     /// from the query source side toward the query target side.
//     pub fn directed_max_edge_with_rmq<K: Ord>(
//         &self,
//         u: usize,
//         v: usize,
//         rmq: &RMQ<Reverse<K>>,
//     ) -> Option<DirectedLineEdge> {
//         let range = self.edge_range(u, v)?;
//         let p = rmq.query(range);

//         let (a, b) = self.edge_dir[p];

//         if self.pos[u] <= self.pos[v] {
//             Some(DirectedLineEdge {
//                 edge_idx: self.edge_idx[p],
//                 from: a,
//                 to: b,
//             })
//         } else {
//             Some(DirectedLineEdge {
//                 edge_idx: self.edge_idx[p],
//                 from: b,
//                 to: a,
//             })
//         }
//     }
// }

#[cfg(test)]
mod tests {
    use super::KRT;

    /// Helper to build LCA + RMQs and query the max-edge index over [l..r]
    fn max_edge_in_interval(
        krt: &mut KRT<impl FnMut(usize, usize, usize)>,
        l: usize,
        r: usize,
    ) -> usize {
        // run dfs to compute ss, pos, dfs order, depth
        let (_ss, pos, dfs, depth) = krt.dfs();
        // build the LCA and two RMQs
        let (mut rmq_min, mut rmq_max) = krt.leaf_pos_rmq(&pos);
        let mut lca = krt.lca(&dfs, &pos, &depth);
        // find the two extremal leaves
        let i = rmq_min.query(l..=r);
        let j = rmq_max.query(l..=r);
        // their LCA in the reconstruction tree
        let anc = lca.query(i, j);
        // internal edge idx stored at anc - original_n
        if anc < krt.n {
            // interval of size 1
            usize::MAX
        } else {
            krt.idx[anc - krt.n]
        }
    }

    #[test]
    fn test_single_leaf() {
        let mut krt = KRT::new(1, |_, _, _| {});
        // no edges to add
        assert_eq!(max_edge_in_interval(&mut krt, 0, 0), usize::MAX);
    }

    #[test]
    fn test_two_leaves() {
        let mut krt = KRT::new(2, |_, _, _| {});
        // add a single edge (0,1) with index 42
        krt.add_edge(0, 1, 42);
        assert_eq!(max_edge_in_interval(&mut krt, 0, 1), 42);
    }

    #[test]
    fn test_chain_of_three() {
        let mut krt = KRT::new(3, |_, _, _| {});
        // edges sorted by weight: (0-1)->5, (1-2)->7
        krt.add_edge(0, 1, 5).add_edge(1, 2, 7);
        // full span [0..2] should pick the heavier edge (index 7)
        assert_eq!(max_edge_in_interval(&mut krt, 0, 2), 7);
        // sub-span [0..1] => edge 5
        assert_eq!(max_edge_in_interval(&mut krt, 0, 1), 5);
        // sub-span [1..2] => edge 7
        assert_eq!(max_edge_in_interval(&mut krt, 1, 2), 7);
    }

    #[test]
    fn test_chain_of_four() {
        let mut krt = KRT::new(4, |_, _, _| {});
        // add edges in increasing "weight" order by idx
        krt.add_edge(0, 1, 1).add_edge(1, 2, 2).add_edge(2, 3, 3);
        // [0..3] => the max-index is 3
        assert_eq!(max_edge_in_interval(&mut krt, 0, 3), 3);
        // [1..3] => max-index among edges (1-2),(2-3) is 3
        assert_eq!(max_edge_in_interval(&mut krt, 1, 3), 3);
        // [2..3] => 3
        assert_eq!(max_edge_in_interval(&mut krt, 2, 3), 3);
    }

    #[test]
    fn test_star_topology() {
        let mut krt = KRT::new(4, |_, _, _| {});
        // We connect leaves 1,2,3 each to center 0:
        krt.add_edge(0, 1, 10).add_edge(0, 2, 20).add_edge(0, 3, 30);
        // in a star, the heaviest connection in any multi-leaf interval
        // is the maximum of those edge-indices
        assert_eq!(max_edge_in_interval(&mut krt, 1, 3), 30);
        assert_eq!(max_edge_in_interval(&mut krt, 2, 3), 30);
        assert_eq!(max_edge_in_interval(&mut krt, 1, 2), 20);
    }

    #[test]
    fn test_unordered_additions() {
        let mut krt = KRT::new(3, |_, _, _| {});
        // add in non-sorted order: but behavior requires sorted edges
        // here we simulate user error: the heavier edge is added first
        krt.add_edge(1, 2, 99).add_edge(0, 1, 11);
        // since we did 1-2 first, that edge becomes the first internal node,
        // then 0-1 merges the component {1,2} with 0, so second internal node
        // => [0..2] returns the idx of the second merge = 11
        assert_eq!(max_edge_in_interval(&mut krt, 0, 2), 11);
    }
}
