use crate::ds::sort::counting_sort_dedup_by_key;

// O(n + |key|) assuming O(1) query LCA
pub fn vtree(
    n: usize,
    key: &mut [usize],
    vs: &mut Vec<usize>,
    vadj: &mut [Vec<usize>],
    pos: &[usize],
    mut lca: impl FnMut(usize, usize) -> usize,
) {
    vs.clear();
    if key.is_empty() {
        return;
    }
    let z = counting_sort_dedup_by_key(key, n, |&v| pos[v]);
    vs.truncate(z);
    vs.resize(key.len(), 0);
    vs.copy_from_slice(key);
    for i in 1..key.len() {
        vs.push(lca(key[i - 1], key[i]));
    }
    let z = counting_sort_dedup_by_key(vs, n, |&v| pos[v]);
    vs.truncate(z);
    for &v in &*vs {
        vadj[v].clear();
    }
    for i in 1..vs.len() {
        vadj[lca(vs[i - 1], vs[i])].push(vs[i]);
    }
}
