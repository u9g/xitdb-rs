//! The count-augmented B+tree behind sorted maps and sets (`src/sorted.rs`).
//!
//! A tree is a leaf of up to 16 entries, or a branch of up to 16 children,
//! each with a separator (the smallest key its subtree may hold; the first
//! is unused) and the number of entries below it. The model follows
//! `sorted_get`, `sorted_rank`, `sorted_get_by_index`, `sorted_put`
//! (including node splits), `sorted_grow_root` and `sorted_remove` branch by
//! branch, with keys abstracted to integers (the crate only compares them)
//! and values to integers. Every result is stated in terms of the tree's
//! entries in order, `flat(n)`:
//!
//! * a well-formed tree's entries are strictly sorted by key and respect
//!   the separators ([`lemma_inv_flat`]);
//! * get, rank and get-by-index are the lookup, the number of smaller keys
//!   and the indexing of that sorted sequence ([`lemma_get`], [`lemma_rank`],
//!   [`lemma_get_by_index`]);
//! * put and remove keep the tree well-formed (including the 16-entry node
//!   limit the file format enforces) and insert into / remove from that
//!   sequence ([`theorem_put`], [`lemma_remove`]), which behaves as a map
//!   ([`lemma_insert_semantics`], [`lemma_remove_semantics`]).
//!
//! Copy-on-write is modelled for the hash map (`hamt.rs`); here nodes are
//! values, so the model covers what the tree computes, not where it is
//! stored.

use vstd::prelude::*;

verus! {

/// A (key, value) entry.
pub type Entry = (int, int);

pub enum Node {
    Leaf(Seq<Entry>),
    /// children, separators, counts
    Branch(Seq<Node>, Seq<int>, Seq<int>),
}

pub open spec fn sorted(s: Seq<Entry>) -> bool {
    forall|a: int, b: int| 0 <= a < b < s.len() ==> s[a].0 < s[b].0
}

/// The entries of a tree, in order.
pub open spec fn flat(n: Node) -> Seq<Entry>
    decreases n,
{
    match n {
        Node::Leaf(e) => e,
        Node::Branch(c, _, _) => flat_upto(c, c.len() as int),
    }
}

/// The entries of the first `j` children.
pub open spec fn flat_upto(c: Seq<Node>, j: int) -> Seq<Entry>
    decreases c, j,
{
    if j <= 0 || j > c.len() {
        Seq::empty()
    } else {
        flat_upto(c, j - 1) + flat(c[j - 1])
    }
}

pub open spec fn fl(c: Seq<Node>) -> Seq<Entry> {
    flat_upto(c, c.len() as int)
}

pub open spec fn sum(cnt: Seq<int>, j: int) -> int
    decreases j,
{
    if j <= 0 {
        0
    } else {
        sum(cnt, j - 1) + cnt[j - 1]
    }
}

pub open spec fn above(k: int, lo: Option<int>) -> bool {
    lo matches Some(l) ==> l <= k
}

pub open spec fn below(k: int, hi: Option<int>) -> bool {
    hi matches Some(h) ==> k < h
}

pub open spec fn below_eq(k: int, hi: Option<int>) -> bool {
    hi matches Some(h) ==> k <= h
}

pub open spec fn child_lo(lo: Option<int>, s: Seq<int>, j: int) -> Option<int> {
    if j == 0 {
        lo
    } else {
        Some(s[j])
    }
}

pub open spec fn child_hi(hi: Option<int>, s: Seq<int>, j: int) -> Option<int> {
    if j + 1 >= s.len() {
        hi
    } else {
        Some(s[j + 1])
    }
}

/// A well-formed tree whose keys are in `[lo, hi)`.
pub open spec fn inv(n: Node, lo: Option<int>, hi: Option<int>) -> bool
    decreases n,
{
    match n {
        Node::Leaf(e) => {
            &&& e.len() <= 16
            &&& sorted(e)
            &&& forall|j: int| 0 <= j < e.len() ==> above(#[trigger] e[j].0, lo) && below(e[j].0, hi)
        },
        Node::Branch(c, s, cnt) => {
            &&& 1 <= c.len() <= 16
            &&& s.len() == c.len()
            &&& cnt.len() == c.len()
            &&& forall|j: int| 0 <= j < c.len() ==> inv(#[trigger] c[j], child_lo(lo, s, j), child_hi(hi, s, j))
            &&& forall|j: int| 0 <= j < c.len() ==> cnt[j] == flat(#[trigger] c[j]).len()
            &&& forall|j: int| 1 <= j < c.len() ==> above(#[trigger] s[j], lo) && below_eq(s[j], hi)
            &&& forall|j: int, j2: int| 1 <= j < j2 < c.len() ==> #[trigger] s[j] <= #[trigger] s[j2]
        },
    }
}

/// `inv` of a branch, without the bounds on its size.
pub open spec fn binv(c: Seq<Node>, s: Seq<int>, cnt: Seq<int>, lo: Option<int>, hi: Option<int>) -> bool {
    &&& s.len() == c.len()
    &&& cnt.len() == c.len()
    &&& forall|j: int| 0 <= j < c.len() ==> inv(#[trigger] c[j], child_lo(lo, s, j), child_hi(hi, s, j))
    &&& forall|j: int| 0 <= j < c.len() ==> cnt[j] == flat(#[trigger] c[j]).len()
    &&& forall|j: int| 1 <= j < c.len() ==> above(#[trigger] s[j], lo) && below_eq(s[j], hi)
    &&& forall|j: int, j2: int| 1 <= j < j2 < c.len() ==> #[trigger] s[j] <= #[trigger] s[j2]
}

// searching a sorted sequence

/// The first index at or after `i` whose key is at least `k`: the loop in
/// the leaf case of every operation.
pub open spec fn find(e: Seq<Entry>, k: int, i: int) -> int
    decreases e.len() - i,
{
    if i >= e.len() {
        e.len() as int
    } else if e[i].0 >= k {
        i
    } else {
        find(e, k, i + 1)
    }
}

pub open spec fn lookup(e: Seq<Entry>, k: int) -> Option<int> {
    let i = find(e, k, 0);
    if 0 <= i < e.len() && e[i].0 == k {
        Some(e[i].1)
    } else {
        None
    }
}

pub open spec fn flat_insert(e: Seq<Entry>, k: int, v: int) -> Seq<Entry> {
    let i = find(e, k, 0);
    if 0 <= i < e.len() && e[i].0 == k {
        e.update(i, (k, v))
    } else {
        e.insert(i, (k, v))
    }
}

pub open spec fn flat_remove(e: Seq<Entry>, k: int) -> Seq<Entry> {
    let i = find(e, k, 0);
    if 0 <= i < e.len() && e[i].0 == k {
        e.remove(i)
    } else {
        e
    }
}

/// `child_for_key`: the last child whose separator is at most `k`.
pub open spec fn cfk(s: Seq<int>, num: int, k: int, i: int) -> int
    decreases num - i,
{
    if i + 1 < num && s[i + 1] <= k {
        cfk(s, num, k, i + 1)
    } else {
        i
    }
}

/// `child_for_rank`: the child holding `rem`, and the rank within it.
pub open spec fn cfr(cnt: Seq<int>, num: int, i: int, rem: int) -> (int, int)
    decreases num - i,
{
    if i + 1 < num && rem >= cnt[i] {
        cfr(cnt, num, i + 1, rem - cnt[i])
    } else {
        (i, rem)
    }
}

// the operations

/// `sorted_get`.
pub open spec fn get(n: Node, k: int) -> Option<int>
    decreases n,
{
    match n {
        Node::Leaf(e) => lookup(e, k),
        Node::Branch(c, s, _) => {
            let i = cfk(s, c.len() as int, k, 0);
            if 0 <= i < c.len() {
                get(c[i], k)
            } else {
                None
            }
        },
    }
}

/// `sorted_rank`: the number of keys below `k`.
pub open spec fn rank(n: Node, k: int) -> int
    decreases n,
{
    match n {
        Node::Leaf(e) => find(e, k, 0),
        Node::Branch(c, s, cnt) => {
            let i = cfk(s, c.len() as int, k, 0);
            if 0 <= i < c.len() {
                sum(cnt, i) + rank(c[i], k)
            } else {
                0
            }
        },
    }
}

/// `sorted_get_by_index`; `None` is `InvalidBTreeNode` from `check_rank`.
pub open spec fn get_by_index(n: Node, r: int) -> Option<Entry>
    decreases n,
{
    match n {
        Node::Leaf(e) => if 0 <= r < e.len() {
            Some(e[r])
        } else {
            None
        },
        Node::Branch(c, _, cnt) => {
            let (i, rem) = cfr(cnt, c.len() as int, 0, r);
            if 0 <= i < c.len() {
                get_by_index(c[i], rem)
            } else {
                None
            }
        },
    }
}

// basic facts

proof fn lemma_find(e: Seq<Entry>, k: int, i: int)
    requires
        0 <= i <= e.len(),
    ensures
        i <= find(e, k, i) <= e.len(),
        forall|j: int| i <= j < find(e, k, i) ==> #[trigger] e[j].0 < k,
        find(e, k, i) < e.len() ==> e[find(e, k, i)].0 >= k,
    decreases e.len() - i,
{
    if i < e.len() && e[i].0 < k {
        lemma_find(e, k, i + 1);
    }
}

/// In a sorted sequence, `find` is the only index with smaller keys before
/// it and a key at least `k` at it.
proof fn lemma_find_unique(e: Seq<Entry>, k: int, r: int)
    requires
        sorted(e),
        0 <= r <= e.len(),
        forall|j: int| 0 <= j < r ==> #[trigger] e[j].0 < k,
        r < e.len() ==> e[r].0 >= k,
    ensures
        find(e, k, 0) == r,
{
    lemma_find(e, k, 0);
    let f = find(e, k, 0);
    if f < r {
        assert(e[f].0 < k);
    } else if f > r {
        assert(e[r].0 < k);
    }
}

proof fn lemma_sum_nonneg_mono(cnt: Seq<int>, a: int, b: int)
    requires
        0 <= a <= b <= cnt.len(),
        forall|j: int| 0 <= j < cnt.len() ==> #[trigger] cnt[j] >= 0,
    ensures
        0 <= sum(cnt, a) <= sum(cnt, b),
    decreases b,
{
    if b > a {
        lemma_sum_nonneg_mono(cnt, a, b - 1);
    } else if a > 0 {
        lemma_sum_nonneg_mono(cnt, 0, a - 1);
    }
}

proof fn lemma_flat_prefix(c: Seq<Node>, d: Seq<Node>, j: int)
    requires
        0 <= j <= c.len(),
        j <= d.len(),
        forall|i: int| 0 <= i < j ==> c[i] == d[i],
    ensures
        flat_upto(c, j) == flat_upto(d, j),
    decreases j,
{
    if j > 0 {
        lemma_flat_prefix(c, d, j - 1);
    }
}

proof fn lemma_fl_concat(c1: Seq<Node>, c2: Seq<Node>)
    ensures
        fl(c1 + c2) == fl(c1) + fl(c2),
    decreases c2.len(),
{
    if c2.len() == 0 {
        assert(c1 + c2 =~= c1);
        assert(fl(c1) + fl(c2) =~= fl(c1));
    } else {
        let c2p = c2.drop_last();
        let n = (c1 + c2).len() as int;
        lemma_fl_concat(c1, c2p);
        lemma_flat_prefix(c1 + c2, c1 + c2p, n - 1);
        lemma_flat_prefix(c2, c2p, c2.len() - 1);
        assert((c1 + c2)[n - 1] == c2[c2.len() - 1]);
        assert(fl(c1 + c2) == flat_upto(c1 + c2, n - 1) + flat(c2[c2.len() - 1]));
        assert(fl(c2) == flat_upto(c2, c2.len() - 1) + flat(c2[c2.len() - 1]));
        assert(fl(c1 + c2) =~= fl(c1) + fl(c2));
    }
}

proof fn lemma_fl_single(x: Node)
    ensures
        fl(seq![x]) == flat(x),
{
    assert(flat_upto(seq![x], 0) =~= Seq::<Entry>::empty());
    assert(fl(seq![x]) =~= flat(x));
}

/// Splitting the children at `i` splits the entries.
proof fn lemma_fl_split3(c: Seq<Node>, i: int)
    requires
        0 <= i < c.len(),
    ensures
        fl(c) == fl(c.subrange(0, i)) + flat(c[i]) + fl(c.subrange(i + 1, c.len() as int)),
        fl(c.subrange(0, i)) == flat_upto(c, i),
{
    let pre = c.subrange(0, i);
    let post = c.subrange(i + 1, c.len() as int);
    assert(c =~= pre + seq![c[i]] + post);
    lemma_fl_concat(pre + seq![c[i]], post);
    lemma_fl_concat(pre, seq![c[i]]);
    lemma_fl_single(c[i]);
    lemma_flat_prefix(c, pre, i);
}

proof fn lemma_sum_len(c: Seq<Node>, cnt: Seq<int>, j: int)
    requires
        cnt.len() == c.len(),
        0 <= j <= c.len(),
        forall|i: int| 0 <= i < c.len() ==> cnt[i] == flat(#[trigger] c[i]).len(),
    ensures
        sum(cnt, j) == flat_upto(c, j).len(),
    decreases j,
{
    if j > 0 {
        lemma_sum_len(c, cnt, j - 1);
    }
}

/// Every entry of `fl(c)` is an entry of one of the children.
proof fn lemma_fl_member(c: Seq<Node>, x: int)
    requires
        0 <= x < fl(c).len(),
    ensures
        exists|j: int, t: int| 0 <= j < c.len() && 0 <= t < flat(c[j]).len() && #[trigger] flat(c[j])[t] == fl(c)[x],
    decreases c.len(),
{
    let cp = c.drop_last();
    let m = c.len() - 1;
    lemma_flat_prefix(c, cp, m);
    assert(fl(c) == fl(cp) + flat(c[m]));
    if x < fl(cp).len() {
        lemma_fl_member(cp, x);
        let (j, t) = choose|j: int, t: int| 0 <= j < cp.len() && 0 <= t < flat(cp[j]).len() && #[trigger] flat(cp[j])[t] == fl(cp)[x];
        assert(flat(c[j])[t] == fl(c)[x]);
    } else {
        assert(flat(c[m])[x - fl(cp).len()] == fl(c)[x]);
    }
}

/// The entries of a well-formed tree are sorted and within its bounds.
pub proof fn lemma_inv_flat(n: Node, lo: Option<int>, hi: Option<int>)
    requires
        inv(n, lo, hi),
    ensures
        sorted(flat(n)),
        forall|j: int| 0 <= j < flat(n).len() ==> above(#[trigger] flat(n)[j].0, lo) && below(flat(n)[j].0, hi),
    decreases n,
{
    if let Node::Branch(c, s, cnt) = n {
        lemma_binv_flat(c, s, cnt, lo, hi, c.len() as int);
    }
}

/// The first `j` children's entries are sorted, above `lo`, and below the
/// next child's separator.
proof fn lemma_binv_flat(c: Seq<Node>, s: Seq<int>, cnt: Seq<int>, lo: Option<int>, hi: Option<int>, j: int)
    requires
        binv(c, s, cnt, lo, hi),
        0 <= j <= c.len(),
    ensures
        sorted(flat_upto(c, j)),
        forall|x: int| 0 <= x < flat_upto(c, j).len() ==> above(#[trigger] flat_upto(c, j)[x].0, lo)
            && below(flat_upto(c, j)[x].0, if j >= 1 { child_hi(hi, s, j - 1) } else { hi }),
    decreases c, j,
{
    if j > 0 {
        lemma_binv_flat(c, s, cnt, lo, hi, j - 1);
        let a = flat_upto(c, j - 1);
        let b = flat(c[j - 1]);
        assert(inv(c[j - 1], child_lo(lo, s, j - 1), child_hi(hi, s, j - 1)));
        lemma_inv_flat(c[j - 1], child_lo(lo, s, j - 1), child_hi(hi, s, j - 1));
        assert(flat_upto(c, j) == a + b);
        // everything in a is below s[j - 1], which is at most everything in b
        assert forall|x: int| 0 <= x < a.len() implies #[trigger] a[x].0 < s[j - 1] || j == 1 by {
            if j >= 2 {
                assert(child_hi(hi, s, j - 2) == Some(s[j - 1]));
            }
        }
        assert forall|x: int| 0 <= x < (a + b).len() implies above(#[trigger] (a + b)[x].0, lo)
            && below((a + b)[x].0, child_hi(hi, s, j - 1)) by {
            if x < a.len() {
                assert((a + b)[x] == a[x]);
                if j >= 2 {
                    assert(child_hi(hi, s, j - 2) == Some(s[j - 1]));
                    if j < c.len() {
                        assert(s[j - 1] <= s[j]);
                    } else {
                        assert(below_eq(s[j - 1], hi));
                    }
                }
            } else {
                assert((a + b)[x] == b[x - a.len()]);
                if j >= 2 {
                    assert(above(s[j - 1], lo));
                }
            }
        }
        assert forall|p: int, q: int| 0 <= p < q < (a + b).len() implies (a + b)[p].0 < (a + b)[q].0 by {
            if q < a.len() {
            } else if p >= a.len() {
                assert((a + b)[p] == b[p - a.len()]);
                assert((a + b)[q] == b[q - a.len()]);
            } else {
                assert((a + b)[p] == a[p]);
                assert((a + b)[q] == b[q - a.len()]);
                assert(above(b[q - a.len()].0, child_lo(lo, s, j - 1)));
            }
        }
    }
}

/// Descending into child `cfk` keeps `k` within the child's bounds.
proof fn lemma_cfk(s: Seq<int>, num: int, k: int, i: int)
    requires
        0 <= i < num <= s.len(),
        i == 0 || s[i] <= k,
    ensures
        i <= cfk(s, num, k, i) < num,
        cfk(s, num, k, i) >= 1 ==> s[cfk(s, num, k, i)] <= k || cfk(s, num, k, i) == i,
        cfk(s, num, k, i) == 0 || s[cfk(s, num, k, i)] <= k,
        cfk(s, num, k, i) + 1 < num ==> k < s[cfk(s, num, k, i) + 1],
    decreases num - i,
{
    if i + 1 < num && s[i + 1] <= k {
        lemma_cfk(s, num, k, i + 1);
    }
}

proof fn lemma_cfr(cnt: Seq<int>, num: int, i: int, rem: int)
    requires
        0 <= i < num <= cnt.len(),
        forall|j: int| 0 <= j < cnt.len() ==> #[trigger] cnt[j] >= 0,
    ensures
        ({
            let (ri, rr) = cfr(cnt, num, i, rem);
            &&& i <= ri < num
            &&& rr == rem - (sum(cnt, ri) - sum(cnt, i))
            &&& ri + 1 < num ==> rr < cnt[ri]
            &&& rem >= 0 ==> rr >= 0
            &&& rem < 0 ==> ri == i && rr == rem
        }),
    decreases num - i,
{
    if i + 1 < num && rem >= cnt[i] {
        lemma_cfr(cnt, num, i + 1, rem - cnt[i]);
    }
}

/// The entries of the children before `i` are below `k`, and those after
/// it are above `k`, when `k` is within child `i`'s bounds.
proof fn lemma_around_child(c: Seq<Node>, s: Seq<int>, cnt: Seq<int>, lo: Option<int>, hi: Option<int>, i: int, k: int)
    requires
        binv(c, s, cnt, lo, hi),
        0 <= i < c.len(),
        above(k, child_lo(lo, s, i)),
        below(k, child_hi(hi, s, i)),
    ensures
        forall|x: int| 0 <= x < fl(c.subrange(0, i)).len() ==> #[trigger] fl(c.subrange(0, i))[x].0 < k,
        forall|x: int| 0 <= x < fl(c.subrange(i + 1, c.len() as int)).len()
            ==> #[trigger] fl(c.subrange(i + 1, c.len() as int))[x].0 > k,
{
    let pre = c.subrange(0, i);
    let post = c.subrange(i + 1, c.len() as int);
    assert forall|x: int| 0 <= x < fl(pre).len() implies #[trigger] fl(pre)[x].0 < k by {
        lemma_fl_member(pre, x);
        let (j, t) = choose|j: int, t: int| 0 <= j < pre.len() && 0 <= t < flat(pre[j]).len() && #[trigger] flat(pre[j])[t] == fl(pre)[x];
        assert(pre[j] == c[j]);
        assert(inv(c[j], child_lo(lo, s, j), child_hi(hi, s, j)));
        lemma_inv_flat(c[j], child_lo(lo, s, j), child_hi(hi, s, j));
        assert(child_hi(hi, s, j) == Some(s[j + 1]));
        if j + 1 < i {
            assert(s[j + 1] <= s[i]);
        }
    }
    assert forall|x: int| 0 <= x < fl(post).len() implies #[trigger] fl(post)[x].0 > k by {
        lemma_fl_member(post, x);
        let (j, t) = choose|j: int, t: int| 0 <= j < post.len() && 0 <= t < flat(post[j]).len() && #[trigger] flat(post[j])[t] == fl(post)[x];
        let jj = j + i + 1;
        assert(post[j] == c[jj]);
        assert(inv(c[jj], child_lo(lo, s, jj), child_hi(hi, s, jj)));
        lemma_inv_flat(c[jj], child_lo(lo, s, jj), child_hi(hi, s, jj));
        assert(child_hi(hi, s, i) == Some(s[i + 1]));
        if jj > i + 1 {
            assert(s[i + 1] <= s[jj]);
        }
    }
}

/// Searching `a + b + c` for a key above everything in `a` and below
/// everything in `c` only looks at `b`.
proof fn lemma_find_concat(a: Seq<Entry>, b: Seq<Entry>, c: Seq<Entry>, k: int)
    requires
        sorted(a + b + c),
        forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x].0 < k,
        forall|x: int| 0 <= x < c.len() ==> #[trigger] c[x].0 > k,
    ensures
        sorted(b),
        find(a + b + c, k, 0) == a.len() + find(b, k, 0),
        lookup(a + b + c, k) == lookup(b, k),
        flat_insert(a + b + c, k, 0) == flat_insert(a + b + c, k, 0),
        forall|v: int| #[trigger] flat_insert(a + b + c, k, v) == a + flat_insert(b, k, v) + c,
        flat_remove(a + b + c, k) == a + flat_remove(b, k) + c,
{
    let abc = a + b + c;
    assert forall|p: int, q: int| 0 <= p < q < b.len() implies b[p].0 < b[q].0 by {
        assert(abc[a.len() + p] == b[p]);
        assert(abc[a.len() + q] == b[q]);
    }
    lemma_find(b, k, 0);
    let fb = find(b, k, 0);
    let r = a.len() + fb;
    assert forall|j: int| 0 <= j < r implies #[trigger] abc[j].0 < k by {
        if j < a.len() {
            assert(abc[j] == a[j]);
        } else {
            assert(abc[j] == b[j - a.len()]);
        }
    }
    if r < abc.len() {
        if fb < b.len() {
            assert(abc[r] == b[fb]);
        } else {
            assert(abc[r] == c[0]);
        }
    }
    lemma_find_unique(abc, k, r);
    if fb < b.len() {
        assert(abc[r] == b[fb]);
    } else if r < abc.len() {
        assert(abc[r] == c[0]);
    }
    assert forall|v: int| #[trigger] flat_insert(abc, k, v) == a + flat_insert(b, k, v) + c by {
        if fb < b.len() && b[fb].0 == k {
            assert(abc.update(r, (k, v)) =~= a + b.update(fb, (k, v)) + c);
        } else {
            assert(abc.insert(r, (k, v)) =~= a + b.insert(fb, (k, v)) + c);
        }
    }
    if fb < b.len() && b[fb].0 == k {
        assert(abc.remove(r) =~= a + b.remove(fb) + c);
    }
}

// reading

pub proof fn lemma_get(n: Node, lo: Option<int>, hi: Option<int>, k: int)
    requires
        inv(n, lo, hi),
        above(k, lo),
        below(k, hi),
    ensures
        get(n, k) == lookup(flat(n), k),
        rank(n, k) == find(flat(n), k, 0),
    decreases n,
{
    if let Node::Branch(c, s, cnt) = n {
        let num = c.len() as int;
        lemma_cfk(s, num, k, 0);
        let i = cfk(s, num, k, 0);
        assert(inv(c[i], child_lo(lo, s, i), child_hi(hi, s, i)));
        lemma_get(c[i], child_lo(lo, s, i), child_hi(hi, s, i), k);
        lemma_around_child(c, s, cnt, lo, hi, i, k);
        lemma_fl_split3(c, i);
        lemma_inv_flat(n, lo, hi);
        lemma_find_concat(fl(c.subrange(0, i)), flat(c[i]), fl(c.subrange(i + 1, num)), k);
        lemma_sum_len(c, cnt, i);
    }
}

pub proof fn lemma_rank(n: Node, k: int)
    requires
        inv(n, None, None),
    ensures
        rank(n, k) == find(flat(n), k, 0),
        get(n, k) == lookup(flat(n), k),
{
    lemma_get(n, None, None, k);
}

pub proof fn lemma_get_by_index(n: Node, lo: Option<int>, hi: Option<int>, r: int)
    requires
        inv(n, lo, hi),
    ensures
        get_by_index(n, r) == if 0 <= r < flat(n).len() {
            Some(flat(n)[r])
        } else {
            None
        },
    decreases n,
{
    if let Node::Branch(c, s, cnt) = n {
        let num = c.len() as int;
        assert forall|j: int| 0 <= j < cnt.len() implies #[trigger] cnt[j] >= 0 by {
            assert(cnt[j] == flat(c[j]).len());
        }
        lemma_cfr(cnt, num, 0, r);
        let (i, rem) = cfr(cnt, num, 0, r);
        assert(inv(c[i], child_lo(lo, s, i), child_hi(hi, s, i)));
        lemma_get_by_index(c[i], child_lo(lo, s, i), child_hi(hi, s, i), rem);
        lemma_fl_split3(c, i);
        lemma_sum_len(c, cnt, i);
        lemma_sum_len(c, cnt, i + 1);
        lemma_sum_len(c, cnt, num);
        lemma_sum_nonneg_mono(cnt, i + 1, num);
        assert(sum(cnt, 0) == 0);
        assert(cnt[i] == flat(c[i]).len());
        let pre = fl(c.subrange(0, i));
        if 0 <= rem < flat(c[i]).len() {
            assert(fl(c)[pre.len() + rem] == flat(c[i])[rem]);
        }
    }
}

// writing

pub struct PutResult {
    pub node: Node,
    pub count: int,
    pub added: bool,
    /// the new right sibling, its count and its separator
    pub split: Option<(Node, int, int)>,
}

/// `sorted_put`, with the value written into the entry it returns.
pub open spec fn put(n: Node, k: int, v: int) -> PutResult
    decreases n,
{
    match n {
        Node::Leaf(e) => {
            let i = find(e, k, 0);
            if 0 <= i < e.len() && e[i].0 == k {
                PutResult { node: Node::Leaf(e.update(i, (k, v))), count: e.len() as int, added: false, split: None }
            } else {
                let es = e.insert(i, (k, v));
                if es.len() <= 16 {
                    PutResult { node: Node::Leaf(es), count: es.len() as int, added: true, split: None }
                } else {
                    // BTREE_SPLIT_COUNT entries stay; the sibling's separator
                    // is the key of its first entry
                    PutResult {
                        node: Node::Leaf(es.subrange(0, 8)),
                        count: 8,
                        added: true,
                        split: Some((Node::Leaf(es.subrange(8, es.len() as int)), es.len() - 8, es[8].0)),
                    }
                }
            }
        },
        Node::Branch(c, s, cnt) => {
            let num = c.len() as int;
            let i = cfk(s, num, k, 0);
            if !(0 <= i < num) {
                PutResult { node: n, count: 0, added: false, split: None }
            } else {
                let r = put(c[i], k, v);
                let c1 = c.update(i, r.node);
                let cnt1 = cnt.update(i, r.count);
                let c2 = match r.split {
                    Some((rn, _, _)) => c1.insert(i + 1, rn),
                    None => c1,
                };
                let s2 = match r.split {
                    Some((_, _, rs)) => s.insert(i + 1, rs),
                    None => s,
                };
                let cnt2 = match r.split {
                    Some((_, rc, _)) => cnt1.insert(i + 1, rc),
                    None => cnt1,
                };
                assemble(c2, s2, cnt2, r.added)
            }
        },
    }
}

/// The end of the branch case of `sorted_put`: one branch, or two if there
/// are more than 16 children.
pub open spec fn assemble(c2: Seq<Node>, s2: Seq<int>, cnt2: Seq<int>, added: bool) -> PutResult {
    let len2 = c2.len() as int;
    if len2 <= 16 {
        PutResult { node: Node::Branch(c2, s2, cnt2), count: sum(cnt2, len2), added, split: None }
    } else {
        // the sibling's separator is separators[BTREE_SPLIT_COUNT]
        PutResult {
            node: Node::Branch(c2.subrange(0, 8), s2.subrange(0, 8), cnt2.subrange(0, 8)),
            count: sum(cnt2.subrange(0, 8), 8),
            added,
            split: Some(
                (
                    Node::Branch(c2.subrange(8, len2), s2.subrange(8, len2), cnt2.subrange(8, len2)),
                    sum(cnt2.subrange(8, len2), len2 - 8),
                    s2[8],
                ),
            ),
        }
    }
}

proof fn lemma_assemble(c2: Seq<Node>, s2: Seq<int>, cnt2: Seq<int>, lo: Option<int>, hi: Option<int>, added: bool)
    requires
        binv(c2, s2, cnt2, lo, hi),
        1 <= c2.len() <= 17,
    ensures
        ({
            let r = assemble(c2, s2, cnt2, added);
            &&& r.count == flat(r.node).len()
            &&& r.added == added
            &&& match r.split {
                None => inv(r.node, lo, hi) && flat(r.node) == fl(c2),
                Some((rn, rc, rs)) => {
                    &&& inv(r.node, lo, Some(rs))
                    &&& inv(rn, Some(rs), hi)
                    &&& rc == flat(rn).len()
                    &&& above(rs, lo)
                    &&& below_eq(rs, hi)
                    &&& flat(r.node) + flat(rn) == fl(c2)
                },
            }
        }),
{
    let len2 = c2.len() as int;
    if len2 <= 16 {
        lemma_sum_len(c2, cnt2, len2);
    } else {
        lemma_binv_split(c2, s2, cnt2, lo, hi, 8);
        let (cl, cr) = (c2.subrange(0, 8), c2.subrange(8, len2));
        assert(c2 =~= cl + cr);
        lemma_fl_concat(cl, cr);
        lemma_sum_len(cl, cnt2.subrange(0, 8), 8);
        lemma_sum_len(cr, cnt2.subrange(8, len2), len2 - 8);
    }
}

/// `sorted_grow_root`: a root that split gets a new parent.
pub open spec fn grow_root(r: PutResult) -> Node {
    match r.split {
        Some((rn, rc, rs)) => Node::Branch(seq![r.node, rn], seq![0, rs], seq![r.count, rc]),
        None => r.node,
    }
}

/// `sorted_remove`: emptied leaves are left in place.
pub open spec fn remove(n: Node, k: int) -> (Node, bool)
    decreases n,
{
    match n {
        Node::Leaf(e) => {
            let i = find(e, k, 0);
            if 0 <= i < e.len() && e[i].0 == k {
                (Node::Leaf(e.remove(i)), true)
            } else {
                (n, false)
            }
        },
        Node::Branch(c, s, cnt) => {
            let num = c.len() as int;
            let i = cfk(s, num, k, 0);
            if !(0 <= i < num) {
                (n, false)
            } else {
                let (cn, found) = remove(c[i], k);
                if !found {
                    (n, false)
                } else {
                    (Node::Branch(c.update(i, cn), s, cnt.update(i, cnt[i] - 1)), true)
                }
            }
        },
    }
}

// sorted sequences as maps

pub open spec fn has_entry(e: Seq<Entry>, x: Entry) -> bool {
    exists|y: int| 0 <= y < e.len() && e[y] == x
}

pub proof fn lemma_insert_semantics(e: Seq<Entry>, k: int, v: int)
    requires
        sorted(e),
    ensures
        sorted(flat_insert(e, k, v)),
        forall|k2: int| #[trigger] lookup(flat_insert(e, k, v), k2) == if k2 == k {
            Some(v)
        } else {
            lookup(e, k2)
        },
        flat_insert(e, k, v).len() == e.len() + if lookup(e, k) is None { 1int } else { 0int },
        forall|x: int| 0 <= x < flat_insert(e, k, v).len() ==> (#[trigger] flat_insert(e, k, v)[x].0 == k
            || exists|y: int| 0 <= y < e.len() && e[y].0 == flat_insert(e, k, v)[x].0),
{
    lemma_find(e, k, 0);
    let i = find(e, k, 0);
    let e2 = flat_insert(e, k, v);
    if 0 <= i < e.len() && e[i].0 == k {
        assert(e2 == e.update(i, (k, v)));
        assert forall|k2: int| #[trigger] lookup(e2, k2) == if k2 == k { Some(v) } else { lookup(e, k2) } by {
            lemma_find(e, k2, 0);
            let f = find(e, k2, 0);
            lemma_find_unique(e2, k2, f);
        }
        assert forall|x: int| 0 <= x < e2.len() implies (#[trigger] e2[x].0 == k
            || exists|y: int| 0 <= y < e.len() && e[y].0 == e2[x].0) by {
            if x != i {
                assert(e[x].0 == e2[x].0);
            }
        }
    } else {
        assert(e2 == e.insert(i, (k, v)));
        assert(sorted(e2)) by {
            assert forall|a: int, b: int| 0 <= a < b < e2.len() implies e2[a].0 < e2[b].0 by {
                if b < i {
                } else if a > i {
                    assert(e2[a] == e[a - 1] && e2[b] == e[b - 1]);
                } else if a == i {
                    assert(e2[b] == e[b - 1]);
                    assert(e[i].0 >= k);
                    if b - 1 > i {
                        assert(e[i].0 < e[b - 1].0);
                    }
                } else if b == i {
                    assert(e2[a] == e[a]);
                } else {
                    assert(e2[a] == e[a] && e2[b] == e[b - 1]);
                }
            }
        }
        assert forall|k2: int| #[trigger] lookup(e2, k2) == if k2 == k { Some(v) } else { lookup(e, k2) } by {
            lemma_find(e, k2, 0);
            let f = find(e, k2, 0);
            if k2 == k {
                lemma_find_unique(e2, k2, i);
            } else if k2 < k {
                if f > i {
                    assert(e[i].0 < k2);
                }
                assert forall|j: int| 0 <= j < f implies #[trigger] e2[j].0 < k2 by {
                    assert(e2[j] == e[j]);
                }
                lemma_find_unique(e2, k2, f);
                if f < i {
                    assert(e2[f] == e[f]);
                }
            } else {
                if f < i {
                    assert(e[f].0 < k);
                }
                assert forall|j: int| 0 <= j < f + 1 implies #[trigger] e2[j].0 < k2 by {
                    if j < i {
                        assert(e2[j] == e[j]);
                    } else if j > i {
                        assert(e2[j] == e[j - 1]);
                    }
                }
                if f + 1 < e2.len() {
                    assert(e2[f + 1] == e[f]);
                }
                lemma_find_unique(e2, k2, f + 1);
            }
        }
        assert forall|x: int| 0 <= x < e2.len() implies (#[trigger] e2[x].0 == k
            || exists|y: int| 0 <= y < e.len() && e[y].0 == e2[x].0) by {
            if x < i {
                assert(e[x].0 == e2[x].0);
            } else if x > i {
                assert(e[x - 1].0 == e2[x].0);
            }
        }
    }
}

pub proof fn lemma_remove_semantics(e: Seq<Entry>, k: int)
    requires
        sorted(e),
    ensures
        sorted(flat_remove(e, k)),
        forall|k2: int| #[trigger] lookup(flat_remove(e, k), k2) == if k2 == k {
            None
        } else {
            lookup(e, k2)
        },
        flat_remove(e, k).len() == e.len() - if lookup(e, k) is Some { 1int } else { 0int },
        forall|x: int| 0 <= x < flat_remove(e, k).len() ==> #[trigger] has_entry(e, flat_remove(e, k)[x]),
{
    lemma_find(e, k, 0);
    let i = find(e, k, 0);
    let e2 = flat_remove(e, k);
    if 0 <= i < e.len() && e[i].0 == k {
        assert(e2 == e.remove(i));
        assert(sorted(e2)) by {
            assert forall|a: int, b: int| 0 <= a < b < e2.len() implies e2[a].0 < e2[b].0 by {
                if b < i {
                } else if a >= i {
                    assert(e2[a] == e[a + 1] && e2[b] == e[b + 1]);
                } else {
                    assert(e2[a] == e[a] && e2[b] == e[b + 1]);
                }
            }
        }
        assert forall|k2: int| #[trigger] lookup(e2, k2) == if k2 == k { None } else { lookup(e, k2) } by {
            lemma_find(e, k2, 0);
            let f = find(e, k2, 0);
            if k2 <= k {
                if f > i {
                    assert(e[i].0 < k2);
                }
                assert forall|j: int| 0 <= j < f implies #[trigger] e2[j].0 < k2 by {
                    assert(e2[j] == e[j]);
                }
                if f < e2.len() {
                    if f < i {
                        assert(e2[f] == e[f]);
                    } else {
                        assert(e2[f] == e[f + 1]);
                        assert(e[i].0 < e[f + 1].0);
                    }
                }
                lemma_find_unique(e2, k2, f);
            } else {
                if f <= i {
                    assert(e[f].0 >= k2);
                    if f < i {
                        assert(e[f].0 < e[i].0);
                    }
                }
                assert forall|j: int| 0 <= j < f - 1 implies #[trigger] e2[j].0 < k2 by {
                    if j < i {
                        assert(e2[j] == e[j]);
                    } else {
                        assert(e2[j] == e[j + 1]);
                    }
                }
                if f - 1 < e2.len() {
                    assert(e2[f - 1] == e[f]);
                }
                lemma_find_unique(e2, k2, f - 1);
            }
        }
        assert forall|x: int| 0 <= x < e2.len() implies #[trigger] has_entry(e, e2[x]) by {
            if x < i {
                assert(e[x] == e2[x]);
            } else {
                assert(e[x + 1] == e2[x]);
            }
        }
    } else {
        assert forall|x: int| 0 <= x < e2.len() implies #[trigger] has_entry(e, e2[x]) by {
            assert(e[x] == e2[x]);
        }
    }
}

// the branch invariant under the edits put and remove make

proof fn lemma_binv_update(c: Seq<Node>, s: Seq<int>, cnt: Seq<int>, lo: Option<int>, hi: Option<int>, i: int, cn: Node, cc: int)
    requires
        binv(c, s, cnt, lo, hi),
        0 <= i < c.len(),
        inv(cn, child_lo(lo, s, i), child_hi(hi, s, i)),
        cc == flat(cn).len(),
    ensures
        binv(c.update(i, cn), s, cnt.update(i, cc), lo, hi),
{
    let c2 = c.update(i, cn);
    assert forall|j: int| 0 <= j < c2.len() implies inv(#[trigger] c2[j], child_lo(lo, s, j), child_hi(hi, s, j)) by {
        if j != i {
            assert(c2[j] == c[j]);
        }
    }
    assert forall|j: int| 0 <= j < c2.len() implies cnt.update(i, cc)[j] == flat(#[trigger] c2[j]).len() by {
        if j != i {
            assert(c2[j] == c[j]);
        }
    }
}

proof fn lemma_binv_insert(
    c: Seq<Node>,
    s: Seq<int>,
    cnt: Seq<int>,
    lo: Option<int>,
    hi: Option<int>,
    i: int,
    cn: Node,
    cc: int,
    rn: Node,
    rc: int,
    rs: int,
)
    requires
        binv(c, s, cnt, lo, hi),
        0 <= i < c.len(),
        inv(cn, child_lo(lo, s, i), Some(rs)),
        inv(rn, Some(rs), child_hi(hi, s, i)),
        above(rs, child_lo(lo, s, i)),
        below_eq(rs, child_hi(hi, s, i)),
        cc == flat(cn).len(),
        rc == flat(rn).len(),
    ensures
        binv(c.update(i, cn).insert(i + 1, rn), s.insert(i + 1, rs), cnt.update(i, cc).insert(i + 1, rc), lo, hi),
{
    let c2 = c.update(i, cn).insert(i + 1, rn);
    let s2 = s.insert(i + 1, rs);
    let cnt2 = cnt.update(i, cc).insert(i + 1, rc);
    let num = c.len() as int;
    assert(c2.len() == num + 1);
    assert forall|j: int| 0 <= j < c2.len() implies inv(#[trigger] c2[j], child_lo(lo, s2, j), child_hi(hi, s2, j)) by {
        if j < i {
            assert(c2[j] == c[j]);
            assert(child_lo(lo, s2, j) == child_lo(lo, s, j));
            assert(child_hi(hi, s2, j) == child_hi(hi, s, j));
        } else if j == i {
            assert(c2[j] == cn);
            assert(child_lo(lo, s2, j) == child_lo(lo, s, i));
        } else if j == i + 1 {
            assert(c2[j] == rn);
            assert(child_hi(hi, s2, j) == child_hi(hi, s, i));
        } else {
            assert(c2[j] == c[j - 1]);
            assert(child_lo(lo, s2, j) == child_lo(lo, s, j - 1));
            assert(child_hi(hi, s2, j) == child_hi(hi, s, j - 1));
        }
    }
    assert forall|j: int| 0 <= j < c2.len() implies cnt2[j] == flat(#[trigger] c2[j]).len() by {
        if j < i {
            assert(c2[j] == c[j]);
        } else if j > i + 1 {
            assert(c2[j] == c[j - 1]);
        }
    }
    assert(above(rs, lo) && below_eq(rs, hi)) by {
        if i >= 1 {
            assert(above(s[i], lo));
        }
        if i + 1 < num {
            assert(below_eq(s[i + 1], hi));
        }
    }
    assert forall|j: int| 1 <= j < c2.len() implies above(#[trigger] s2[j], lo) && below_eq(s2[j], hi) by {
        if j < i + 1 {
            assert(s2[j] == s[j]);
        } else if j > i + 1 {
            assert(s2[j] == s[j - 1]);
        }
    }
    assert forall|j: int, j2: int| 1 <= j < j2 < c2.len() implies #[trigger] s2[j] <= #[trigger] s2[j2] by {
        if j2 <= i {
            assert(s2[j] == s[j] && s2[j2] == s[j2]);
        } else if j > i + 1 {
            assert(s2[j] == s[j - 1] && s2[j2] == s[j2 - 1]);
        } else if j == i + 1 {
            assert(s2[j2] == s[j2 - 1]);
            if j2 - 1 > i + 1 {
                assert(s[i + 1] <= s[j2 - 1]);
            }
        } else if j2 == i + 1 {
            assert(s2[j] == s[j]);
            if j < i {
                assert(s[j] <= s[i]);
            }
        } else {
            assert(s2[j] == s[j] && s2[j2] == s[j2 - 1]);
            assert(s[j] <= s[i]);
            if j2 - 1 > i + 1 {
                assert(s[i + 1] <= s[j2 - 1]);
            }
            assert(rs <= s[i + 1]);
        }
    }
}

proof fn lemma_binv_split(c: Seq<Node>, s: Seq<int>, cnt: Seq<int>, lo: Option<int>, hi: Option<int>, m: int)
    requires
        binv(c, s, cnt, lo, hi),
        1 <= m < c.len(),
    ensures
        binv(c.subrange(0, m), s.subrange(0, m), cnt.subrange(0, m), lo, Some(s[m])),
        binv(c.subrange(m, c.len() as int), s.subrange(m, c.len() as int), cnt.subrange(m, c.len() as int), Some(s[m]), hi),
        above(s[m], lo),
        below_eq(s[m], hi),
{
    let len = c.len() as int;
    let (cl, sl, nl) = (c.subrange(0, m), s.subrange(0, m), cnt.subrange(0, m));
    let (cr, sr, nr) = (c.subrange(m, len), s.subrange(m, len), cnt.subrange(m, len));
    assert forall|j: int| 0 <= j < cl.len() implies inv(#[trigger] cl[j], child_lo(lo, sl, j), child_hi(Some(s[m]), sl, j)) by {
        assert(cl[j] == c[j]);
        assert(child_lo(lo, sl, j) == child_lo(lo, s, j));
        assert(child_hi(Some(s[m]), sl, j) == child_hi(hi, s, j));
    }
    assert forall|j: int| 0 <= j < cl.len() implies nl[j] == flat(#[trigger] cl[j]).len() by {
        assert(cl[j] == c[j]);
    }
    assert forall|j: int| 1 <= j < cl.len() implies above(#[trigger] sl[j], lo) && below_eq(sl[j], Some(s[m])) by {
        assert(sl[j] == s[j]);
    }
    assert forall|j: int, j2: int| 1 <= j < j2 < cl.len() implies #[trigger] sl[j] <= #[trigger] sl[j2] by {
        assert(sl[j] == s[j] && sl[j2] == s[j2]);
    }
    assert forall|j: int| 0 <= j < cr.len() implies inv(#[trigger] cr[j], child_lo(Some(s[m]), sr, j), child_hi(hi, sr, j)) by {
        assert(cr[j] == c[j + m]);
        assert(child_lo(Some(s[m]), sr, j) == child_lo(lo, s, j + m));
        assert(child_hi(hi, sr, j) == child_hi(hi, s, j + m));
    }
    assert forall|j: int| 0 <= j < cr.len() implies nr[j] == flat(#[trigger] cr[j]).len() by {
        assert(cr[j] == c[j + m]);
    }
    assert forall|j: int| 1 <= j < cr.len() implies above(#[trigger] sr[j], Some(s[m])) && below_eq(sr[j], hi) by {
        assert(sr[j] == s[j + m]);
    }
    assert forall|j: int, j2: int| 1 <= j < j2 < cr.len() implies #[trigger] sr[j] <= #[trigger] sr[j2] by {
        assert(sr[j] == s[j + m] && sr[j2] == s[j2 + m]);
    }
}

// put and remove

pub open spec fn put_ok(n: Node, lo: Option<int>, hi: Option<int>, k: int, v: int, r: PutResult) -> bool {
    &&& r.count == flat(r.node).len()
    &&& r.added == (lookup(flat(n), k) is None)
    &&& match r.split {
        None => inv(r.node, lo, hi) && flat(r.node) == flat_insert(flat(n), k, v),
        Some((rn, rc, rs)) => {
            &&& inv(r.node, lo, Some(rs))
            &&& inv(rn, Some(rs), hi)
            &&& rc == flat(rn).len()
            &&& above(rs, lo)
            &&& below_eq(rs, hi)
            &&& flat(r.node) + flat(rn) == flat_insert(flat(n), k, v)
        },
    }
}

proof fn lemma_put_leaf(e: Seq<Entry>, lo: Option<int>, hi: Option<int>, k: int, v: int)
    requires
        inv(Node::Leaf(e), lo, hi),
        above(k, lo),
        below(k, hi),
    ensures
        put_ok(Node::Leaf(e), lo, hi, k, v, put(Node::Leaf(e), k, v)),
{
    lemma_insert_semantics(e, k, v);
    lemma_find(e, k, 0);
    let es = flat_insert(e, k, v);
    assert forall|x: int| 0 <= x < es.len() implies above(#[trigger] es[x].0, lo) && below(es[x].0, hi) by {
        if es[x].0 != k {
            let y = choose|y: int| 0 <= y < e.len() && e[y].0 == es[x].0;
        }
    }
    let r = put(Node::Leaf(e), k, v);
    if !(lookup(e, k) is None) {
        assert(r.node == Node::Leaf(es));
    } else if es.len() > 16 {
        let left = es.subrange(0, 8);
        let right = es.subrange(8, es.len() as int);
        assert forall|x: int| 0 <= x < left.len() implies above(#[trigger] left[x].0, lo) && below(left[x].0, Some(es[8].0)) by {
            assert(left[x] == es[x]);
        }
        assert forall|x: int| 0 <= x < right.len() implies above(#[trigger] right[x].0, Some(es[8].0)) && below(right[x].0, hi) by {
            assert(right[x] == es[x + 8]);
        }
        assert(left + right =~= es);
    }
}

/// What a branch knows about the child `put` descends into.
pub open spec fn branch_step(c: Seq<Node>, s: Seq<int>, cnt: Seq<int>, lo: Option<int>, hi: Option<int>, k: int, v: int, i: int, r: PutResult) -> bool {
    &&& inv(Node::Branch(c, s, cnt), lo, hi)
    &&& above(k, lo)
    &&& below(k, hi)
    &&& i == cfk(s, c.len() as int, k, 0)
    &&& 0 <= i < c.len()
    &&& above(k, child_lo(lo, s, i))
    &&& below(k, child_hi(hi, s, i))
    &&& r == put(c[i], k, v)
    &&& put_ok(c[i], child_lo(lo, s, i), child_hi(hi, s, i), k, v, r)
}

proof fn lemma_put_branch_nosplit(c: Seq<Node>, s: Seq<int>, cnt: Seq<int>, lo: Option<int>, hi: Option<int>, k: int, v: int, i: int, r: PutResult)
    requires
        branch_step(c, s, cnt, lo, hi, k, v, i, r),
        r.split is None,
    ensures
        put_ok(Node::Branch(c, s, cnt), lo, hi, k, v, put(Node::Branch(c, s, cnt), k, v)),
{
    let n = Node::Branch(c, s, cnt);
    let num = c.len() as int;
    lemma_inv_flat(n, lo, hi);
    lemma_around_child(c, s, cnt, lo, hi, i, k);
    lemma_fl_split3(c, i);
    let pre = c.subrange(0, i);
    let post = c.subrange(i + 1, num);
    lemma_find_concat(fl(pre), flat(c[i]), fl(post), k);
    let c1 = c.update(i, r.node);
    let cnt1 = cnt.update(i, r.count);
    lemma_binv_update(c, s, cnt, lo, hi, i, r.node, r.count);
    lemma_fl_split3(c1, i);
    assert(c1.subrange(0, i) =~= pre);
    assert(c1.subrange(i + 1, num) =~= post);
    assert(put(n, k, v) == assemble(c1, s, cnt1, r.added));
    lemma_assemble(c1, s, cnt1, lo, hi, r.added);
}

proof fn lemma_put_branch_split(c: Seq<Node>, s: Seq<int>, cnt: Seq<int>, lo: Option<int>, hi: Option<int>, k: int, v: int, i: int, r: PutResult)
    requires
        branch_step(c, s, cnt, lo, hi, k, v, i, r),
        r.split is Some,
    ensures
        put_ok(Node::Branch(c, s, cnt), lo, hi, k, v, put(Node::Branch(c, s, cnt), k, v)),
{
    let n = Node::Branch(c, s, cnt);
    let num = c.len() as int;
    let (rn, rc, rs) = r.split.unwrap();
    lemma_inv_flat(n, lo, hi);
    lemma_around_child(c, s, cnt, lo, hi, i, k);
    lemma_fl_split3(c, i);
    let pre = c.subrange(0, i);
    let post = c.subrange(i + 1, num);
    let (a, b, cc) = (fl(pre), flat(c[i]), fl(post));
    lemma_find_concat(a, b, cc, k);
    let c2 = c.update(i, r.node).insert(i + 1, rn);
    let s2 = s.insert(i + 1, rs);
    let cnt2 = cnt.update(i, r.count).insert(i + 1, rc);
    let len2 = num + 1;
    lemma_binv_insert(c, s, cnt, lo, hi, i, r.node, r.count, rn, rc, rs);
    assert(c2 =~= pre + seq![r.node] + seq![rn] + post);
    lemma_fl_concat(pre + seq![r.node] + seq![rn], post);
    lemma_fl_concat(pre + seq![r.node], seq![rn]);
    lemma_fl_concat(pre, seq![r.node]);
    lemma_fl_single(r.node);
    lemma_fl_single(rn);
    assert(fl(c2) =~= a + (flat(r.node) + flat(rn)) + cc);
    assert(put(n, k, v) == assemble(c2, s2, cnt2, r.added));
    lemma_assemble(c2, s2, cnt2, lo, hi, r.added);
}

pub proof fn lemma_put(n: Node, lo: Option<int>, hi: Option<int>, k: int, v: int)
    requires
        inv(n, lo, hi),
        above(k, lo),
        below(k, hi),
    ensures
        put_ok(n, lo, hi, k, v, put(n, k, v)),
    decreases n,
{
    match n {
        Node::Leaf(e) => lemma_put_leaf(e, lo, hi, k, v),
        Node::Branch(c, s, cnt) => {
            let num = c.len() as int;
            lemma_cfk(s, num, k, 0);
            let i = cfk(s, num, k, 0);
            assert(inv(c[i], child_lo(lo, s, i), child_hi(hi, s, i)));
            lemma_put(c[i], child_lo(lo, s, i), child_hi(hi, s, i), k, v);
            let r = put(c[i], k, v);
            if r.split is None {
                lemma_put_branch_nosplit(c, s, cnt, lo, hi, k, v, i, r);
            } else {
                lemma_put_branch_split(c, s, cnt, lo, hi, k, v, i, r);
            }
        },
    }
}

pub proof fn lemma_remove(n: Node, lo: Option<int>, hi: Option<int>, k: int)
    requires
        inv(n, lo, hi),
        above(k, lo),
        below(k, hi),
    ensures
        remove(n, k).1 == (lookup(flat(n), k) is Some),
        inv(remove(n, k).0, lo, hi),
        flat(remove(n, k).0) == flat_remove(flat(n), k),
    decreases n,
{
    lemma_inv_flat(n, lo, hi);
    match n {
        Node::Leaf(e) => {
            lemma_remove_semantics(e, k);
            let e2 = flat_remove(e, k);
            assert forall|x: int| 0 <= x < e2.len() implies above(#[trigger] e2[x].0, lo) && below(e2[x].0, hi) by {
                assert(has_entry(e, e2[x]));
                let y = choose|y: int| 0 <= y < e.len() && e[y] == e2[x];
            }
        },
        Node::Branch(c, s, cnt) => {
            let num = c.len() as int;
            lemma_cfk(s, num, k, 0);
            let i = cfk(s, num, k, 0);
            let (loi, hii) = (child_lo(lo, s, i), child_hi(hi, s, i));
            assert(inv(c[i], loi, hii));
            lemma_remove(c[i], loi, hii, k);
            let (cn, found) = remove(c[i], k);
            lemma_around_child(c, s, cnt, lo, hi, i, k);
            lemma_fl_split3(c, i);
            let pre = c.subrange(0, i);
            let post = c.subrange(i + 1, num);
            lemma_find_concat(fl(pre), flat(c[i]), fl(post), k);
            lemma_inv_flat(c[i], loi, hii);
            lemma_remove_semantics(flat(c[i]), k);
            if found {
                assert(cnt[i] == flat(c[i]).len());
                lemma_binv_update(c, s, cnt, lo, hi, i, cn, cnt[i] - 1);
                let c2 = c.update(i, cn);
                lemma_fl_split3(c2, i);
                assert(c2.subrange(0, i) =~= pre);
                assert(c2.subrange(i + 1, num) =~= post);
            }
        },
    }
}

/// Putting into a sorted map: the tree stays well-formed (a root that
/// splits gets a new parent), and its entries become the sorted insert,
/// which behaves as a map (see `lemma_insert_semantics`).
pub proof fn theorem_put(root: Node, k: int, v: int)
    requires
        inv(root, None, None),
    ensures
        inv(grow_root(put(root, k, v)), None, None),
        flat(grow_root(put(root, k, v))) == flat_insert(flat(root), k, v),
        put(root, k, v).added == (lookup(flat(root), k) is None),
{
    lemma_put(root, None, None, k, v);
    let r = put(root, k, v);
    if let Some((rn, rc, rs)) = r.split {
        let c = seq![r.node, rn];
        let s = seq![0, rs];
        assert(c =~= seq![r.node] + seq![rn]);
        lemma_fl_concat(seq![r.node], seq![rn]);
        lemma_fl_single(r.node);
        lemma_fl_single(rn);
        assert(child_hi(None, s, 0) == Some(rs));
        assert forall|j: int| 0 <= j < c.len() implies inv(#[trigger] c[j], child_lo(None, s, j), child_hi(None, s, j)) by {}
    }
}

/// An empty sorted map is an empty leaf.
pub proof fn lemma_empty_sorted()
    ensures
        inv(Node::Leaf(Seq::empty()), None, None),
        flat(Node::Leaf(Seq::empty())) == Seq::<Entry>::empty(),
{
}

} // verus!
