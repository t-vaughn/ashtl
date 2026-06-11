#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LCTNode<T> {
    pub v: T,
    pub p: usize,
    pub ch: [usize; 2],
    pub rev: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LCT<T, Pull, Push, Rev>
where
    Pull: FnMut([usize; 3], &mut [LCTNode<T>]),
    Push: FnMut([usize; 3], &mut [LCTNode<T>]),
    Rev: FnMut(usize, &mut [LCTNode<T>]),
{
    pub ns: Vec<LCTNode<T>>,
    pub pull: Pull,
    pub push: Push,
    pub rev: Rev,
}

impl<T, Pull, Push, Rev> LCT<T, Pull, Push, Rev>
where
    Pull: FnMut([usize; 3], &mut [LCTNode<T>]),
    Push: FnMut([usize; 3], &mut [LCTNode<T>]),
    Rev: FnMut(usize, &mut [LCTNode<T>]),
{
    pub fn new(init: T, pull: Pull, push: Push, rev: Rev) -> Self {
        Self {
            ns: vec![LCTNode {
                v: init,
                p: 0,
                ch: [0, 0],
                rev: false,
            }],
            pull,
            push,
            rev,
        }
    }

    pub fn with_capacity(capacity: usize, init: T, pull: Pull, push: Push, rev: Rev) -> Self {
        let mut ns = Vec::with_capacity(capacity + 1);
        ns.push(LCTNode {
            v: init,
            p: 0,
            ch: [0, 0],
            rev: false,
        });
        Self {
            ns,
            pull,
            push,
            rev,
        }
    }

    pub fn add_node(&mut self, v: T) -> usize {
        let id = self.ns.len();
        self.ns.push(LCTNode {
            v,
            p: 0,
            ch: [0, 0],
            rev: false,
        });
        id
    }

    pub fn len(&self) -> usize {
        self.ns.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ns.len() <= 1
    }

    fn is_aux_root(&self, x: usize) -> bool {
        let p = self.ns[x].p;
        p == 0 || (self.ns[p].ch[0] != x && self.ns[p].ch[1] != x)
    }

    fn apply_rev(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        self.ns[x].rev ^= true;
        (self.rev)(x, &mut self.ns);
    }

    pub fn push(&mut self, x: usize) {
        if x == 0 {
            return;
        } else if self.ns[x].rev {
            self.ns[x].ch.swap(0, 1);
            let [l, r] = self.ns[x].ch;
            self.apply_rev(l);
            self.apply_rev(r);
            self.ns[x].rev = false;
        }
        let [l, r] = self.ns[x].ch;
        (self.push)([x, l, r], &mut self.ns);
    }

    pub fn pull(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let [l, r] = self.ns[x].ch;
        (self.pull)([x, l, r], &mut self.ns);
    }

    fn rotate(&mut self, x: usize) {
        let p = self.ns[x].p;
        let g = self.ns[p].p;
        let xr = self.ns[p].ch[1] == x;
        let k = xr as usize;
        let b = self.ns[x].ch[k ^ 1];
        if !self.is_aux_root(p) {
            if self.ns[g].ch[0] == p {
                self.ns[g].ch[0] = x;
            } else {
                self.ns[g].ch[1] = x;
            }
        }
        self.ns[x].p = g;
        self.ns[x].ch[k ^ 1] = p;
        self.ns[p].p = x;
        self.ns[p].ch[k] = b;
        if b != 0 {
            self.ns[b].p = p;
        }
        self.pull(p);
        self.pull(x);
    }

    pub fn splay(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        let mut stack = vec![x];
        let mut y = x;
        while !self.is_aux_root(y) {
            y = self.ns[y].p;
            stack.push(y);
        }
        while let Some(z) = stack.pop() {
            self.push(z);
        }
        while !self.is_aux_root(x) {
            let p = self.ns[x].p;
            if !self.is_aux_root(p) {
                let g = self.ns[p].p;
                let zigzig = (self.ns[p].ch[0] == x) == (self.ns[g].ch[0] == p);
                if zigzig {
                    self.rotate(p);
                } else {
                    self.rotate(x);
                }
            }
            self.rotate(x);
        }
        self.pull(x);
    }

    pub fn access(&mut self, x: usize) {
        let mut last = 0;
        let mut y = x;
        while y != 0 {
            self.splay(y);
            self.ns[y].ch[1] = last;
            if last != 0 {
                self.ns[last].p = y;
            }
            self.pull(y);
            last = y;
            y = self.ns[y].p;
        }
        self.splay(x);
    }

    pub fn make_root(&mut self, x: usize) {
        self.access(x);
        self.apply_rev(x);
    }

    pub fn find_root(&mut self, x: usize) -> usize {
        self.access(x);
        let mut y = x;
        self.push(y);
        while self.ns[y].ch[0] != 0 {
            y = self.ns[y].ch[0];
            self.push(y);
        }
        self.splay(y);
        y
    }

    pub fn conn(&mut self, a: usize, b: usize) -> bool {
        if a == b {
            true
        } else {
            self.find_root(a) == self.find_root(b)
        }
    }

    pub fn link(&mut self, a: usize, b: usize) {
        debug_assert!(a != 0 && b != 0 && a != b);
        self.make_root(a);
        debug_assert_ne!(self.find_root(b), a, "LCT::link would create a cycle");
        self.ns[a].p = b;
    }

    pub fn cut(&mut self, a: usize, b: usize) {
        debug_assert!(a != 0 && b != 0);
        self.make_root(a);
        self.access(b);
        if self.ns[b].ch[0] == a && self.ns[a].ch[1] == 0 {
            self.ns[b].ch[0] = 0;
            self.ns[a].p = 0;
            self.pull(b);
        } else {
            debug_assert!(
                false,
                "LCT::cut called on non-adjacent represented-tree nodes"
            );
        }
    }

    pub fn expose_path(&mut self, a: usize, b: usize) -> usize {
        debug_assert!(a != 0 && b != 0);
        self.make_root(a);
        self.access(b);
        b
    }

    pub fn query_path<R>(
        &mut self,
        a: usize,
        b: usize,
        mut f: impl FnMut(usize, [usize; 2], &mut [LCTNode<T>]) -> R,
    ) -> R {
        let root = self.expose_path(a, b);
        let ch = self.ns[root].ch;
        f(root, ch, &mut self.ns)
    }

    pub fn update_node<R>(
        &mut self,
        x: usize,
        mut f: impl FnMut(usize, [usize; 2], &mut [LCTNode<T>]) -> R,
    ) -> R {
        debug_assert!(x != 0);
        self.access(x);
        let ch = self.ns[x].ch;
        let out = f(x, ch, &mut self.ns);
        self.pull(x);
        out
    }

    pub fn first_on_path(&mut self, x: usize) -> usize {
        debug_assert!(x != 0);
        self.access(x);
        let mut y = x;
        self.push(y);
        while self.ns[y].ch[0] != 0 {
            y = self.ns[y].ch[0];
            self.push(y);
        }
        self.splay(y);
        y
    }
}

#[derive(Clone, Debug)]
pub struct SLCTNode<T> {
    pub v: T,
    pub p: usize,
    pub ch: [usize; 2],
    pub rev: bool,
    pub k: i8,
}

pub struct SLCT<T, Pull, Push, Rev, Virtual, Link, Cut> {
    pub ns: Vec<SLCTNode<T>>,
    pub pull: Pull,
    pub push: Push,
    pub rev: Rev,
    pub virt: Virtual,
    pub link: Link,
    pub cut: Cut,
}

impl<T, Pull, Push, Rev, Virtual, Link, Cut> SLCT<T, Pull, Push, Rev, Virtual, Link, Cut>
where
    Pull: FnMut(usize, [usize; 2], &mut [SLCTNode<T>]),
    Push: FnMut(usize, usize, &mut [SLCTNode<T>]),
    Rev: FnMut(usize, &mut [SLCTNode<T>]),
    Virtual: FnMut(usize, usize, bool, &mut [SLCTNode<T>]),
    Link: FnMut(usize, usize, &mut [SLCTNode<T>]),
    Cut: FnMut(usize, usize, &mut [SLCTNode<T>]),
{
    pub fn new(
        init: T,
        pull: Pull,
        push: Push,
        rev: Rev,
        virt: Virtual,
        link: Link,
        cut: Cut,
    ) -> Self {
        let mut ns = Vec::new();
        ns.push(SLCTNode {
            v: init,
            p: 0,
            ch: [0, 0],
            rev: false,
            k: -1,
        });
        Self {
            ns,
            pull,
            push,
            rev,
            virt,
            link,
            cut,
        }
    }

    pub fn with_capacity(
        cap: usize,
        init: T,
        pull: Pull,
        push: Push,
        rev: Rev,
        virt: Virtual,
        link: Link,
        cut: Cut,
    ) -> Self {
        let mut nodes = Vec::with_capacity(cap + 1);
        nodes.push(SLCTNode {
            v: init,
            p: 0,
            ch: [0, 0],
            rev: false,
            k: -1,
        });
        Self {
            ns: nodes,
            pull,
            push,
            rev,
            virt,
            link,
            cut,
        }
    }

    pub fn maintain(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        if self.ns[x].rev {
            let [ch0, ch1] = self.ns[x].ch;
            self.ns[x].ch.swap(0, 1);
            if ch0 != 0 {
                self.ns[ch0].k = 1;
                self.reverse(ch0);
            }
            if ch1 != 0 {
                self.ns[ch1].k = 0;
                self.reverse(ch1);
            }
            self.ns[x].rev = false;
        }
    }

    pub fn pull(&mut self, x: usize) {
        (self.pull)(x, self.ns[x].ch, &mut self.ns);
    }

    pub fn reverse(&mut self, x: usize) {
        if x != 0 {
            self.ns[x].rev ^= true;
            (self.rev)(x, &mut self.ns);
        }
    }

    pub fn rot(&mut self, x: usize) {
        let p = self.ns[x].p;
        let g = self.ns[p].p;
        let k = self.ns[x].k as usize;
        let t = self.ns[p].k;
        (self.push)(p, x, &mut self.ns);
        let ch = self.ns[x].ch[k ^ 1];
        self.ns[p].ch[k] = ch;
        if ch != 0 {
            self.ns[ch].p = p;
            self.ns[ch].k = k as i8;
        }
        self.ns[p].p = x;
        self.ns[p].k = (k ^ 1) as i8;
        self.ns[x].ch[k ^ 1] = p;
        self.ns[x].p = g;
        self.ns[x].k = t;
        if t != -1 {
            self.ns[g].ch[t as usize] = x;
        }
        self.pull(p);
    }

    pub fn splay(&mut self, x: usize) {
        if x == 0 {
            return;
        }
        self.maintain(x);
        while self.ns[x].k != -1 {
            let p = self.ns[x].p;
            if self.ns[p].k == -1 {
                self.maintain(p);
                self.maintain(x);
                self.rot(x);
            } else {
                let g = self.ns[p].p;
                self.maintain(g);
                self.maintain(p);
                self.maintain(x);
                if self.ns[x].k == self.ns[p].k {
                    self.rot(p);
                    self.rot(x);
                } else {
                    self.rot(x);
                    self.rot(x);
                }
            }
        }
        self.pull(x);
    }

    pub fn access(&mut self, x: usize) {
        self.splay(x);
        let rs = self.ns[x].ch[1];
        if rs != 0 {
            self.ns[rs].k = -1;
            (self.virt)(x, rs, true, &mut self.ns);
        }
        self.ns[x].ch[1] = 0;
        self.pull(x);
        while self.ns[x].p != 0 {
            let p = self.ns[x].p;
            self.splay(p);
            let p_rs = self.ns[p].ch[1];
            if p_rs != 0 {
                self.ns[p_rs].k = -1;
                (self.virt)(p, p_rs, true, &mut self.ns);
            }
            (self.virt)(p, x, false, &mut self.ns);
            self.ns[p].ch[1] = x;
            self.ns[x].k = 1;
            self.rot(x);
            self.pull(x);
        }
    }

    pub fn make_root(&mut self, x: usize) {
        self.access(x);
        self.reverse(x);
    }

    pub fn link(&mut self, u: usize, v: usize) {
        if u == 0 || v == 0 || u == v {
            return;
        }
        self.make_root(u);
        self.access(v);
        (self.link)(u, v, &mut self.ns);
        self.ns[u].p = v;
        (self.virt)(v, u, true, &mut self.ns);
        self.pull(v);
    }

    pub fn cut(&mut self, u: usize, v: usize) {
        self.make_root(u);
        self.access(v);
        let ch0 = self.ns[v].ch[0];
        if ch0 != 0 {
            (self.cut)(ch0, v, &mut self.ns);
            self.ns[ch0].p = 0;
            self.ns[ch0].k = -1;
            self.ns[v].ch[0] = 0;
            self.pull(v);
        }
    }

    pub fn update<R>(
        &mut self,
        u: usize,
        p: usize,
        mut f: impl FnMut(usize, &mut [SLCTNode<T>]) -> R,
    ) -> R {
        self.access(u);
        self.reverse(u);
        self.access(p);
        let res = f(u, &mut self.ns);
        self.pull(u);
        res
    }

    pub fn query<R>(
        &mut self,
        u: usize,
        p: usize,
        mut f: impl FnMut(usize, usize, &mut [SLCTNode<T>]) -> R,
    ) -> R {
        self.access(u);
        self.reverse(u);
        self.access(p);
        f(u, p, &mut self.ns)
    }
}
