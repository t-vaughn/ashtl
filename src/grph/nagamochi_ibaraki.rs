/// O(m + n)
pub fn ni_decomposition(adj: &[Vec<usize>]) -> Vec<Vec<(usize, usize)>> {
    let n = adj.len();
    let mut forests: Vec<Vec<(usize, usize)>> = Vec::new();
    if n == 0 {
        return forests;
    }
    let mut degrees = vec![0; n];
    let mut visited = vec![false; n];
    let mut buckets: Vec<Vec<usize>> = vec![vec![]; n];
    let mut pos_in_bucket = vec![0; n];
    for i in 0..n {
        buckets[0].push(i);
        pos_in_bucket[i] = i;
    }
    let mut max_d = 0;
    for _ in 0..n {
        while max_d > 0 && buckets[max_d].is_empty() {
            max_d -= 1;
        }
        let u = buckets[max_d].pop().unwrap();
        visited[u] = true;
        for &v in &adj[u] {
            if !visited[v] {
                let d = degrees[v];
                while forests.len() <= d {
                    forests.push(Vec::new());
                }
                forests[d].push((u, v));
                let pos = pos_in_bucket[v];
                let last_val = *buckets[d].last().unwrap();
                buckets[d].swap_remove(pos);
                if pos < buckets[d].len() {
                    pos_in_bucket[last_val] = pos;
                }
                degrees[v] += 1;
                let new_d = degrees[v];
                if new_d >= buckets.len() {
                    buckets.push(vec![]);
                }
                pos_in_bucket[v] = buckets[new_d].len();
                buckets[new_d].push(v);
                if new_d > max_d {
                    max_d = new_d;
                }
            }
        }
    }
    forests
}

pub fn ni_sparsifier_k(n: usize, forests: &[Vec<(usize, usize)>], k: usize) -> Vec<Vec<usize>> {
    let mut sparsifier = vec![vec![]; n];
    for depth in 0..k.min(forests.len()) {
        for &(u, v) in &forests[depth] {
            sparsifier[u].push(v);
            sparsifier[v].push(u);
        }
    }
    sparsifier
}
