use crate::tree::lct::{LCT, LCTNode};

const EPS: f64 = 1e-12;

#[derive(Clone, Debug)]
pub struct CirculationRoundEdge {
    pub from: usize,
    pub to: usize,
    pub flow: f64,
    pub cost: f64,
}

fn is_integral(f: f64) -> bool {
    (f - f.round()).abs() <= EPS
}

fn avail_fwd(f: f64) -> f64 {
    let a = f.ceil() - f;
    if a.abs() <= EPS { 0.0 } else { a }
}

fn avail_bwd(f: f64) -> f64 {
    let a = f - f.floor();
    if a.abs() <= EPS { 0.0 } else { a }
}

fn snap(f: &mut f64) {
    let r = f.round();
    if (*f - r).abs() <= EPS {
        *f = r;
    }
}

/// O(m log n)
pub fn round_circulation(n: usize, edges: &mut [CirculationRoundEdge]) {
    #[derive(Clone, Debug)]
    struct CircNode {
        is_edge: bool,
        edge_index: usize,
        end0: usize,
        end1: usize,
        sign: f64,
        flow: f64,
        cost: f64,
        add: f64,
        cost_sum: f64,
        min_fwd: f64,
        min_fwd_node: usize,
        min_bwd: f64,
        min_bwd_node: usize,
    }

    impl CircNode {
        fn vertex() -> Self {
            Self {
                is_edge: false,
                edge_index: usize::MAX,
                end0: 0,
                end1: 0,
                sign: 1.0,
                flow: 0.0,
                cost: 0.0,
                add: 0.0,
                cost_sum: 0.0,
                min_fwd: f64::INFINITY,
                min_fwd_node: 0,
                min_bwd: f64::INFINITY,
                min_bwd_node: 0,
            }
        }

        fn empty_edge_node() -> Self {
            Self::vertex()
        }
    }

    fn better(a_val: f64, a_node: usize, b_val: f64, b_node: usize) -> (f64, usize) {
        if b_val < a_val {
            (b_val, b_node)
        } else {
            (a_val, a_node)
        }
    }

    fn pull_circ([x, l, r]: [usize; 3], ns: &mut [LCTNode<CircNode>]) {
        if x == 0 {
            return;
        }
        let mut cost_sum = 0.0;
        let mut min_fwd = f64::INFINITY;
        let mut min_fwd_node = 0;
        let mut min_bwd = f64::INFINITY;
        let mut min_bwd_node = 0;
        if l != 0 {
            cost_sum += ns[l].v.cost_sum;
            (min_fwd, min_fwd_node) =
                better(min_fwd, min_fwd_node, ns[l].v.min_fwd, ns[l].v.min_fwd_node);
            (min_bwd, min_bwd_node) =
                better(min_bwd, min_bwd_node, ns[l].v.min_bwd, ns[l].v.min_bwd_node);
        }
        if ns[x].v.is_edge {
            cost_sum += ns[x].v.cost;
            let af = avail_fwd(ns[x].v.flow);
            let ab = avail_bwd(ns[x].v.flow);
            (min_fwd, min_fwd_node) = better(min_fwd, min_fwd_node, af, x);
            (min_bwd, min_bwd_node) = better(min_bwd, min_bwd_node, ab, x);
        }
        if r != 0 {
            cost_sum += ns[r].v.cost_sum;
            (min_fwd, min_fwd_node) =
                better(min_fwd, min_fwd_node, ns[r].v.min_fwd, ns[r].v.min_fwd_node);
            (min_bwd, min_bwd_node) =
                better(min_bwd, min_bwd_node, ns[r].v.min_bwd, ns[r].v.min_bwd_node);
        }
        if min_fwd.abs() <= EPS {
            min_fwd = 0.0;
        }
        if min_bwd.abs() <= EPS {
            min_bwd = 0.0;
        }
        ns[x].v.cost_sum = cost_sum;
        ns[x].v.min_fwd = min_fwd;
        ns[x].v.min_fwd_node = min_fwd_node;
        ns[x].v.min_bwd = min_bwd;
        ns[x].v.min_bwd_node = min_bwd_node;
    }

    fn apply_add_circ(x: usize, delta: f64, ns: &mut [LCTNode<CircNode>]) {
        if x == 0 || delta.abs() <= EPS {
            return;
        }
        if ns[x].v.is_edge {
            ns[x].v.flow += delta;
            snap(&mut ns[x].v.flow);
        }
        ns[x].v.add += delta;
        ns[x].v.min_fwd -= delta;
        ns[x].v.min_bwd += delta;
        if ns[x].v.min_fwd.abs() <= EPS {
            ns[x].v.min_fwd = 0.0;
        }
        if ns[x].v.min_bwd.abs() <= EPS {
            ns[x].v.min_bwd = 0.0;
        }
    }

    fn push_circ([x, l, r]: [usize; 3], ns: &mut [LCTNode<CircNode>]) {
        if x == 0 {
            return;
        }
        let delta = ns[x].v.add;
        if delta.abs() <= EPS {
            ns[x].v.add = 0.0;
            return;
        }
        apply_add_circ(l, delta, ns);
        apply_add_circ(r, delta, ns);
        ns[x].v.add = 0.0;
    }

    fn rev_circ(x: usize, ns: &mut [LCTNode<CircNode>]) {
        if x == 0 {
            return;
        }
        let v = &mut ns[x].v;
        v.cost_sum = -v.cost_sum;
        std::mem::swap(&mut v.min_fwd, &mut v.min_bwd);
        std::mem::swap(&mut v.min_fwd_node, &mut v.min_bwd_node);
        v.add = -v.add;
        if v.is_edge {
            v.flow = -v.flow;
            v.cost = -v.cost;
            v.sign = -v.sign;
        }
    }

    fn set_edge_node(
        lct: &mut LCT<
            CircNode,
            impl FnMut([usize; 3], &mut [LCTNode<CircNode>]),
            impl FnMut([usize; 3], &mut [LCTNode<CircNode>]),
            impl FnMut(usize, &mut [LCTNode<CircNode>]),
        >,
        en: usize,
        edge_index: usize,
        end0: usize,
        end1: usize,
        flow: f64,
        cost: f64,
    ) {
        lct.splay(en);
        lct.ns[en].v.is_edge = true;
        lct.ns[en].v.edge_index = edge_index;
        lct.ns[en].v.end0 = end0;
        lct.ns[en].v.end1 = end1;
        lct.ns[en].v.sign = 1.0;
        lct.ns[en].v.flow = flow;
        lct.ns[en].v.cost = cost;
        lct.ns[en].v.add = 0.0;
        lct.pull(en);
    }

    fn original_flow_of_edge_node(
        lct: &mut LCT<
            CircNode,
            impl FnMut([usize; 3], &mut [LCTNode<CircNode>]),
            impl FnMut([usize; 3], &mut [LCTNode<CircNode>]),
            impl FnMut(usize, &mut [LCTNode<CircNode>]),
        >,
        en: usize,
    ) -> (usize, f64, usize, usize) {
        lct.update_node(en, |x, _, ns| {
            let edge_index = ns[x].v.edge_index;
            let mut flow = ns[x].v.sign * ns[x].v.flow;
            snap(&mut flow);
            let a = ns[x].v.end0;
            let b = ns[x].v.end1;
            (edge_index, flow, a, b)
        })
    }

    fn clear_edge_node(
        lct: &mut LCT<
            CircNode,
            impl FnMut([usize; 3], &mut [LCTNode<CircNode>]),
            impl FnMut([usize; 3], &mut [LCTNode<CircNode>]),
            impl FnMut(usize, &mut [LCTNode<CircNode>]),
        >,
        en: usize,
    ) {
        lct.update_node(en, |x, _, ns| {
            ns[x].v = CircNode::empty_edge_node();
        });
    }

    fn remove_edge_node(
        lct: &mut LCT<
            CircNode,
            impl FnMut([usize; 3], &mut [LCTNode<CircNode>]),
            impl FnMut([usize; 3], &mut [LCTNode<CircNode>]),
            impl FnMut(usize, &mut [LCTNode<CircNode>]),
        >,
        en: usize,
        edges: &mut [CirculationRoundEdge],
        active: &mut [usize],
    ) {
        if en == 0 {
            return;
        }
        let (ei, mut flow, a, b) = original_flow_of_edge_node(lct, en);
        snap(&mut flow);
        if ei != usize::MAX {
            edges[ei].flow = flow;
            snap(&mut edges[ei].flow);
            if is_integral(edges[ei].flow) {
                edges[ei].flow = edges[ei].flow.round();
            }
            active[ei] = 0;
        }
        if a != 0 {
            lct.cut(en, a);
        }
        if b != 0 {
            lct.cut(en, b);
        }
        clear_edge_node(lct, en);
    }

    if n == 0 || edges.is_empty() {
        return;
    }
    let m = edges.len();
    let init = CircNode::vertex();
    let mut lct = LCT::with_capacity(n + m, init, pull_circ, push_circ, rev_circ);
    let mut vertex_node = vec![0usize; n];
    for v in 0..n {
        vertex_node[v] = lct.add_node(CircNode::vertex());
    }
    let mut active = vec![0; m];
    let mut eidx = 0;
    while eidx < m {
        snap(&mut edges[eidx].flow);
        if is_integral(edges[eidx].flow) {
            edges[eidx].flow = edges[eidx].flow.round();
            eidx += 1;
            continue;
        }
        let u = edges[eidx].from;
        let v = edges[eidx].to;
        if u == v {
            edges[eidx].flow = if edges[eidx].cost >= 0.0 {
                edges[eidx].flow.floor()
            } else {
                edges[eidx].flow.ceil()
            };
            eidx += 1;
            continue;
        }
        let un = vertex_node[u];
        let vn = vertex_node[v];
        if !lct.conn(un, vn) {
            let en = lct.add_node(CircNode::empty_edge_node());
            lct.link(un, en);
            lct.link(en, vn);
            lct.expose_path(un, vn);
            lct.splay(en);
            set_edge_node(
                &mut lct,
                en,
                eidx,
                un,
                vn,
                edges[eidx].flow,
                edges[eidx].cost,
            );
            active[eidx] = en;
            eidx += 1;
            continue;
        }
        let root = lct.expose_path(un, vn);
        let path_cost = lct.ns[root].v.cost_sum;
        let path_min_fwd = lct.ns[root].v.min_fwd;
        let path_min_fwd_node = lct.ns[root].v.min_fwd_node;
        let path_min_bwd = lct.ns[root].v.min_bwd;
        let path_min_bwd_node = lct.ns[root].v.min_bwd_node;
        let cost_a = edges[eidx].cost - path_cost;
        let use_a = cost_a <= 0.0;
        let avail_edge = if use_a {
            avail_fwd(edges[eidx].flow)
        } else {
            avail_bwd(edges[eidx].flow)
        };
        let avail_path = if use_a { path_min_bwd } else { path_min_fwd };
        let blocker = if use_a {
            path_min_bwd_node
        } else {
            path_min_fwd_node
        };
        let delta = avail_edge.min(avail_path);
        if delta <= EPS {
            if avail_path <= EPS && blocker != 0 {
                remove_edge_node(&mut lct, blocker, edges, &mut active);
                continue;
            }
        }
        let path_delta = if use_a { -delta } else { delta };
        let root = lct.expose_path(un, vn);
        apply_add_circ(root, path_delta, &mut lct.ns);
        edges[eidx].flow += if use_a { delta } else { -delta };
        snap(&mut edges[eidx].flow);
        let root = lct.expose_path(un, vn);
        let (zero_val, zero_node) = if path_delta > 0.0 {
            (lct.ns[root].v.min_fwd, lct.ns[root].v.min_fwd_node)
        } else {
            (lct.ns[root].v.min_bwd, lct.ns[root].v.min_bwd_node)
        };
        if zero_val <= EPS && zero_node != 0 {
            remove_edge_node(&mut lct, zero_node, edges, &mut active);
        }
        if is_integral(edges[eidx].flow) {
            edges[eidx].flow = edges[eidx].flow.round();
            eidx += 1;
        }
    }
    for ei in 0..m {
        let en = active[ei];
        if en != 0 {
            let (_stored_ei, mut flow, _a, _b) = original_flow_of_edge_node(&mut lct, en);
            snap(&mut flow);
            edges[ei].flow = flow;
        }
    }
    for e in edges.iter_mut() {
        snap(&mut e.flow);
        e.flow = e.flow.round();
    }
}
