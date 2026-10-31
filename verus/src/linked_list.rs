//! The count-augmented B-tree behind linked array lists (`src/btree.rs`).
//!
//! A tree is a leaf of up to 16 values, or a branch of up to 16 children
//! with the number of values below each. Every leaf is at the same depth,
//! and every node but an empty root holds at least one value. The model
//! follows `read_btree_slot`, `btree_insert` and `btree_make_root`,
//! `btree_remove` (dropping emptied children, merging underfull ones, and
//! the caller's collapsing of a one-child root), `btree_join` (with
//! `btree_join_left`, `btree_join_right`, `btree_merge_nodes` and the
//! assemble functions) and `btree_split`, with values abstracted to
//! integers. In terms of a tree's values in order, `flat(n)`:
//!
//! * get returns the value at an index ([`lemma_get`]);
//! * insert inserts at an index ([`theorem_insert`]);
//! * remove removes at an index ([`theorem_remove`]);
//! * join concatenates ([`lemma_join`]), and split cuts at an index
//!   ([`lemma_split`]), so slicing (two splits) and concatenation are
//!   correct;
//!
//! and every result is a well-formed tree within the 16-entry node limit.
//! Like `sorted.rs`, this covers what the tree computes; copy-on-write is
//! modelled in `hamt.rs`.

use vstd::prelude::*;

verus! {

pub enum Node {
    Leaf(Seq<int>),
    /// children, counts
    Branch(Seq<Node>, Seq<int>),
}

pub open spec fn flat(n: Node) -> Seq<int>
    decreases n,
{
    match n {
        Node::Leaf(v) => v,
        Node::Branch(c, _) => flat_upto(c, c.len() as int),
    }
}

pub open spec fn flat_upto(c: Seq<Node>, j: int) -> Seq<int>
    decreases c, j,
{
    if j <= 0 || j > c.len() {
        Seq::empty()
    } else {
        flat_upto(c, j - 1) + flat(c[j - 1])
    }
}

pub open spec fn fl(c: Seq<Node>) -> Seq<int> {
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

/// `node.num`: how many values or children a node has.
pub open spec fn num(n: Node) -> int {
    match n {
        Node::Leaf(v) => v.len() as int,
        Node::Branch(c, _) => c.len() as int,
    }
}

/// `subtree_count`.
pub open spec fn count(n: Node) -> int {
    match n {
        Node::Leaf(v) => v.len() as int,
        Node::Branch(_, cnt) => sum(cnt, cnt.len() as int),
    }
}

/// `btree_height`: follows the first child.
pub open spec fn height(n: Node) -> nat
    decreases n,
{
    match n {
        Node::Leaf(_) => 0,
        Node::Branch(c, _) => if c.len() > 0 {
            1 + height(c[0])
        } else {
            1
        },
    }
}

/// The children of a branch, each a well-formed, non-empty tree of height
/// `hc`, with their counts.
pub open spec fn bwf(c: Seq<Node>, cnt: Seq<int>, hc: nat) -> bool {
    &&& cnt.len() == c.len()
    &&& forall|j: int| 0 <= j < c.len() ==> wf(#[trigger] c[j], hc)
    &&& forall|j: int| 0 <= j < c.len() ==> cnt[j] == flat(#[trigger] c[j]).len() && flat(c[j]).len() >= 1
}

/// A well-formed tree of height `h`.
pub open spec fn wf(n: Node, h: nat) -> bool
    decreases n, 1int,
{
    match n {
        Node::Leaf(v) => h == 0 && v.len() <= 16,
        Node::Branch(c, cnt) => {
            &&& h >= 1
            &&& 1 <= c.len() <= 16
            &&& cnt.len() == c.len()
            &&& forall|j: int| 0 <= j < c.len() ==> wf(#[trigger] c[j], (h - 1) as nat)
            &&& forall|j: int| 0 <= j < c.len() ==> cnt[j] == flat(#[trigger] c[j]).len() && flat(c[j]).len() >= 1
        },
    }
}

/// What `btree_remove` returns: `wf`, except that it may have no entries.
pub open spec fn wf_rm(n: Node, h: nat) -> bool {
    match n {
        Node::Leaf(v) => h == 0 && v.len() <= 16,
        Node::Branch(c, cnt) => h >= 1 && c.len() <= 16 && bwf(c, cnt, (h - 1) as nat),
    }
}

/// `child_for_rank`.
pub open spec fn cfr(cnt: Seq<int>, n: int, i: int, rem: int, inclusive: bool) -> (int, int)
    decreases n - i,
{
    if i + 1 < n && (rem > cnt[i] || (!inclusive && rem == cnt[i])) {
        cfr(cnt, n, i + 1, rem - cnt[i], inclusive)
    } else {
        (i, rem)
    }
}

// the operations

/// `read_btree_slot`; `None` is `InvalidBTreeNode` from `check_rank`.
pub open spec fn get(n: Node, r: int) -> Option<int>
    decreases n,
{
    match n {
        Node::Leaf(v) => if 0 <= r < v.len() {
            Some(v[r])
        } else {
            None
        },
        Node::Branch(c, cnt) => {
            let (i, rem) = cfr(cnt, c.len() as int, 0, r, false);
            if 0 <= i < c.len() {
                get(c[i], rem)
            } else {
                None
            }
        },
    }
}

pub struct J {
    pub node: Node,
    pub count: int,
    pub split: Option<(Node, int)>,
}

/// The values a join result holds.
pub open spec fn jflat(j: J) -> Seq<int> {
    match j.split {
        Some((sn, _)) => flat(j.node) + flat(sn),
        None => flat(j.node),
    }
}

/// A well-formed join result of height `h`: one node, or two non-empty
/// ones.
pub open spec fn jwf(j: J, h: nat) -> bool {
    &&& wf(j.node, h)
    &&& j.count == flat(j.node).len()
    &&& j.split matches Some((sn, sc)) ==> wf(sn, h) && sc == flat(sn).len() && flat(sn).len() >= 1 && flat(
        j.node,
    ).len() >= 1
}

/// The end of `btree_insert`: one node, or two split at
/// `BTREE_SPLIT_COUNT`.
pub open spec fn insert_leaf(vals: Seq<int>) -> J {
    if vals.len() <= 16 {
        J { node: Node::Leaf(vals), count: vals.len() as int, split: None }
    } else {
        J {
            node: Node::Leaf(vals.subrange(0, 8)),
            count: 8,
            split: Some((Node::Leaf(vals.subrange(8, vals.len() as int)), vals.len() - 8)),
        }
    }
}

pub open spec fn insert_branch(c: Seq<Node>, cnt: Seq<int>) -> J {
    let total = c.len() as int;
    if total <= 16 {
        J { node: Node::Branch(c, cnt), count: sum(cnt, total), split: None }
    } else {
        J {
            node: Node::Branch(c.subrange(0, 8), cnt.subrange(0, 8)),
            count: sum(cnt.subrange(0, 8), 8),
            split: Some((Node::Branch(c.subrange(8, total), cnt.subrange(8, total)), sum(cnt.subrange(8, total), total - 8))),
        }
    }
}

/// Replaces child `i` with a join result.
pub open spec fn replace_child(c: Seq<Node>, i: int, j: J) -> Seq<Node> {
    match j.split {
        Some((sn, _)) => c.update(i, j.node).insert(i + 1, sn),
        None => c.update(i, j.node),
    }
}

pub open spec fn replace_count(cnt: Seq<int>, i: int, j: J) -> Seq<int> {
    match j.split {
        Some((_, sc)) => cnt.update(i, j.count).insert(i + 1, sc),
        None => cnt.update(i, j.count),
    }
}

/// `btree_insert` of the value `x` at `r`.
pub open spec fn insert(n: Node, r: int, x: int) -> Option<J>
    decreases n,
{
    match n {
        Node::Leaf(v) => if 0 <= r <= v.len() {
            Some(insert_leaf(v.insert(r, x)))
        } else {
            None
        },
        Node::Branch(c, cnt) => {
            let (i, rem) = cfr(cnt, c.len() as int, 0, r, true);
            if !(0 <= i < c.len()) {
                None
            } else {
                match insert(c[i], rem, x) {
                    None => None,
                    Some(j) => Some(insert_branch(replace_child(c, i, j), replace_count(cnt, i, j))),
                }
            }
        },
    }
}

/// `btree_make_root`.
pub open spec fn make_root(j: J) -> Node {
    match j.split {
        Some((sn, sc)) => Node::Branch(seq![j.node, sn], seq![j.count, sc]),
        None => j.node,
    }
}

/// `concat_nodes`.
pub open spec fn concat_nodes(a: Node, b: Node) -> Node {
    match (a, b) {
        (Node::Leaf(va), Node::Leaf(vb)) => Node::Leaf(va + vb),
        (Node::Branch(ca, na), Node::Branch(cb, nb)) => Node::Branch(ca + cb, na + nb),
        _ => a,
    }
}

/// `btree_remove` after the child at `i` has become `m`.
pub open spec fn remove_finish(c: Seq<Node>, cnt: Seq<int>, i: int, m: Node) -> Node {
    if num(m) == 0 {
        // drop_child
        Node::Branch(c.remove(i), cnt.remove(i))
    } else if num(m) < 8 && c.len() > 1 {
        let first = if i + 1 >= c.len() { i - 1 } else { i };
        let ni = if i + 1 >= c.len() { i - 1 } else { i + 1 };
        let nb = c[ni];
        if num(m) + num(nb) <= 16 {
            let merged = if first == i { concat_nodes(m, nb) } else { concat_nodes(nb, m) };
            let c1 = c.remove(first + 1);
            let cnt1 = cnt.remove(first + 1);
            Node::Branch(c1.update(first, merged), cnt1.update(first, count(merged)))
        } else {
            Node::Branch(c.update(i, m), cnt.update(i, count(m)))
        }
    } else {
        Node::Branch(c.update(i, m), cnt.update(i, count(m)))
    }
}

/// `btree_remove` of the value at `r`.
pub open spec fn remove(n: Node, r: int) -> Option<Node>
    decreases n,
{
    match n {
        Node::Leaf(v) => if 0 <= r < v.len() {
            Some(Node::Leaf(v.remove(r)))
        } else {
            None
        },
        Node::Branch(c, cnt) => {
            let (i, rem) = cfr(cnt, c.len() as int, 0, r, false);
            if !(0 <= i < c.len()) {
                None
            } else {
                match remove(c[i], rem) {
                    None => None,
                    Some(m) => Some(remove_finish(c, cnt, i, m)),
                }
            }
        },
    }
}

/// The caller's loop replacing a root that has one child with that child.
pub open spec fn collapse(n: Node) -> Node
    decreases n,
{
    match n {
        Node::Branch(c, _) => if c.len() == 1 {
            collapse(c[0])
        } else {
            n
        },
        _ => n,
    }
}

/// `LinkedArrayListRemove`: a list of one value gets a new empty root.
pub open spec fn remove_root(root: Node, r: int) -> Option<Node> {
    if flat(root).len() == 1 {
        if r == 0 {
            Some(Node::Leaf(Seq::empty()))
        } else {
            None
        }
    } else {
        match remove(root, r) {
            Some(m) => Some(collapse(m)),
            None => None,
        }
    }
}

// facts about the entries

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

pub proof fn lemma_fl_concat(c1: Seq<Node>, c2: Seq<Node>)
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

pub proof fn lemma_fl_single(x: Node)
    ensures
        fl(seq![x]) == flat(x),
{
    assert(flat_upto(seq![x], 0) =~= Seq::<int>::empty());
    assert(fl(seq![x]) =~= flat(x));
}

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

proof fn lemma_sum_mono(cnt: Seq<int>, a: int, b: int)
    requires
        0 <= a <= b <= cnt.len(),
        forall|j: int| 0 <= j < cnt.len() ==> #[trigger] cnt[j] >= 0,
    ensures
        0 <= sum(cnt, a) <= sum(cnt, b),
    decreases b,
{
    if b > a {
        lemma_sum_mono(cnt, a, b - 1);
    } else if a > 0 {
        lemma_sum_mono(cnt, 0, a - 1);
    }
}

proof fn lemma_cfr(cnt: Seq<int>, n: int, i: int, rem: int, inclusive: bool)
    requires
        0 <= i < n <= cnt.len(),
        forall|j: int| 0 <= j < cnt.len() ==> #[trigger] cnt[j] >= 0,
    ensures
        ({
            let (ri, rr) = cfr(cnt, n, i, rem, inclusive);
            &&& i <= ri < n
            &&& rr == rem - (sum(cnt, ri) - sum(cnt, i))
            &&& ri + 1 < n ==> if inclusive { rr <= cnt[ri] } else { rr < cnt[ri] }
            &&& rem >= 0 ==> rr >= 0
            &&& rem < 0 ==> ri == i && rr == rem
        }),
    decreases n - i,
{
    if i + 1 < n && (rem > cnt[i] || (!inclusive && rem == cnt[i])) {
        lemma_cfr(cnt, n, i + 1, rem - cnt[i], inclusive);
    }
}

/// Facts about a well-formed tree: its height, count, and that a branch's
/// counts are non-negative and add up.
pub proof fn lemma_wf(n: Node, h: nat)
    requires
        wf(n, h),
    ensures
        height(n) == h,
        count(n) == flat(n).len(),
        n is Branch ==> flat(n).len() >= 1,
    decreases n,
{
    if let Node::Branch(c, cnt) = n {
        assert(wf(c[0], (h - 1) as nat));
        lemma_wf(c[0], (h - 1) as nat);
        lemma_sum_len(c, cnt, c.len() as int);
        lemma_fl_split3(c, 0);
    }
}

proof fn lemma_counts_nonneg(c: Seq<Node>, cnt: Seq<int>, hc: nat)
    requires
        bwf(c, cnt, hc),
    ensures
        forall|j: int| 0 <= j < cnt.len() ==> #[trigger] cnt[j] >= 0,
{
    assert forall|j: int| 0 <= j < cnt.len() implies #[trigger] cnt[j] >= 0 by {
        assert(cnt[j] == flat(c[j]).len());
    }
}

proof fn lemma_bwf_wf(c: Seq<Node>, cnt: Seq<int>, h: nat)
    requires
        h >= 1,
        1 <= c.len() <= 16,
        bwf(c, cnt, (h - 1) as nat),
    ensures
        wf(Node::Branch(c, cnt), h),
{
}

proof fn lemma_wf_bwf(c: Seq<Node>, cnt: Seq<int>, h: nat)
    requires
        wf(Node::Branch(c, cnt), h),
    ensures
        bwf(c, cnt, (h - 1) as nat),
        h >= 1,
        1 <= c.len() <= 16,
{
}

/// Child `i` is where index `r` lands: `sum(cnt, i) + rem == r`.
proof fn lemma_descend(c: Seq<Node>, cnt: Seq<int>, h: nat, r: int, inclusive: bool)
    requires
        wf(Node::Branch(c, cnt), h),
        0 <= r,
        if inclusive { r <= fl(c).len() } else { r < fl(c).len() },
    ensures
        ({
            let (i, rem) = cfr(cnt, c.len() as int, 0, r, inclusive);
            &&& 0 <= i < c.len()
            &&& 0 <= rem
            &&& if inclusive { rem <= flat(c[i]).len() } else { rem < flat(c[i]).len() }
            &&& r == flat_upto(c, i).len() + rem
        }),
{
    let num = c.len() as int;
    lemma_counts_nonneg(c, cnt, (h - 1) as nat);
    lemma_cfr(cnt, num, 0, r, inclusive);
    let (i, rem) = cfr(cnt, num, 0, r, inclusive);
    lemma_sum_len(c, cnt, i);
    lemma_sum_len(c, cnt, i + 1);
    lemma_sum_len(c, cnt, num);
    lemma_sum_mono(cnt, i + 1, num);
    assert(sum(cnt, 0) == 0);
    assert(cnt[i] == flat(c[i]).len());
}

// reading

pub proof fn lemma_get(n: Node, h: nat, r: int)
    requires
        wf(n, h),
    ensures
        get(n, r) == if 0 <= r < flat(n).len() {
            Some(flat(n)[r])
        } else {
            None
        },
    decreases n,
{
    if let Node::Branch(c, cnt) = n {
        let num = c.len() as int;
        lemma_counts_nonneg(c, cnt, (h - 1) as nat);
        lemma_cfr(cnt, num, 0, r, false);
        let (i, rem) = cfr(cnt, num, 0, r, false);
        assert(wf(c[i], (h - 1) as nat));
        lemma_get(c[i], (h - 1) as nat, rem);
        lemma_fl_split3(c, i);
        lemma_sum_len(c, cnt, i);
        lemma_sum_len(c, cnt, i + 1);
        lemma_sum_len(c, cnt, num);
        lemma_sum_mono(cnt, i + 1, num);
        assert(sum(cnt, 0) == 0);
        assert(cnt[i] == flat(c[i]).len());
        if 0 <= rem < flat(c[i]).len() {
            assert(fl(c)[flat_upto(c, i).len() + rem] == flat(c[i])[rem]);
        }
    }
}

// inserting

proof fn lemma_insert_branch(c: Seq<Node>, cnt: Seq<int>, hc: nat)
    requires
        bwf(c, cnt, hc),
        1 <= c.len() <= 17,
    ensures
        jwf(insert_branch(c, cnt), hc + 1),
        jflat(insert_branch(c, cnt)) == fl(c),
{
    let total = c.len() as int;
    if total <= 16 {
        lemma_sum_len(c, cnt, total);
    } else {
        let (cl, cr) = (c.subrange(0, 8), c.subrange(8, total));
        let (nl, nr) = (cnt.subrange(0, 8), cnt.subrange(8, total));
        assert(c =~= cl + cr);
        lemma_fl_concat(cl, cr);
        assert forall|j: int| 0 <= j < cl.len() implies wf(#[trigger] cl[j], hc) && nl[j] == flat(cl[j]).len() && flat(cl[j]).len() >= 1 by {
            assert(cl[j] == c[j]);
        }
        assert forall|j: int| 0 <= j < cr.len() implies wf(#[trigger] cr[j], hc) && nr[j] == flat(cr[j]).len() && flat(cr[j]).len() >= 1 by {
            assert(cr[j] == c[j + 8]);
        }
        lemma_sum_len(cl, nl, 8);
        lemma_sum_len(cr, nr, total - 8);
        lemma_fl_split3(cl, 0);
        lemma_fl_split3(cr, 0);
    }
}

#[verifier::rlimit(30)]
proof fn lemma_replace_child_split(c: Seq<Node>, cnt: Seq<int>, hc: nat, i: int, j: J)
    requires
        bwf(c, cnt, hc),
        0 <= i < c.len(),
        jwf(j, hc),
        flat(j.node).len() >= 1,
        j.split is Some,
    ensures
        bwf(replace_child(c, i, j), replace_count(cnt, i, j), hc),
        replace_child(c, i, j).len() == c.len() + 1,
        fl(replace_child(c, i, j)) == fl(c.subrange(0, i)) + jflat(j) + fl(c.subrange(i + 1, c.len() as int)),
{
    let (sn, sc) = j.split.unwrap();
    let c2 = c.update(i, j.node).insert(i + 1, sn);
    let cnt2 = cnt.update(i, j.count).insert(i + 1, sc);
    assert(replace_child(c, i, j) == c2);
    assert(replace_count(cnt, i, j) == cnt2);
    let pre = c.subrange(0, i);
    let post = c.subrange(i + 1, c.len() as int);
    assert forall|k: int| 0 <= k < c2.len() implies wf(#[trigger] c2[k], hc) && cnt2[k] == flat(c2[k]).len() && flat(c2[k]).len() >= 1 by {
        if k < i {
            assert(c2[k] == c[k] && cnt2[k] == cnt[k]);
        } else if k > i + 1 {
            assert(c2[k] == c[k - 1] && cnt2[k] == cnt[k - 1]);
        }
    }
    assert(c2 =~= pre + seq![j.node] + seq![sn] + post);
    lemma_fl_concat(pre + seq![j.node] + seq![sn], post);
    lemma_fl_concat(pre + seq![j.node], seq![sn]);
    lemma_fl_concat(pre, seq![j.node]);
    lemma_fl_single(j.node);
    lemma_fl_single(sn);
    assert(fl(c2) =~= fl(pre) + jflat(j) + fl(post));
}

proof fn lemma_replace_child_nosplit(c: Seq<Node>, cnt: Seq<int>, hc: nat, i: int, j: J)
    requires
        bwf(c, cnt, hc),
        0 <= i < c.len(),
        jwf(j, hc),
        flat(j.node).len() >= 1,
        j.split is None,
    ensures
        bwf(replace_child(c, i, j), replace_count(cnt, i, j), hc),
        replace_child(c, i, j).len() == c.len(),
        fl(replace_child(c, i, j)) == fl(c.subrange(0, i)) + jflat(j) + fl(c.subrange(i + 1, c.len() as int)),
{
    let c2 = c.update(i, j.node);
    let cnt2 = cnt.update(i, j.count);
    assert(replace_child(c, i, j) == c2);
    assert(replace_count(cnt, i, j) == cnt2);
    assert forall|k: int| 0 <= k < c2.len() implies wf(#[trigger] c2[k], hc) && cnt2[k] == flat(c2[k]).len() && flat(c2[k]).len() >= 1 by {
        if k != i {
            assert(c2[k] == c[k] && cnt2[k] == cnt[k]);
        }
    }
    lemma_fl_split3(c2, i);
    assert(c2.subrange(0, i) =~= c.subrange(0, i));
    assert(c2.subrange(i + 1, c.len() as int) =~= c.subrange(i + 1, c.len() as int));
}

/// Replacing child `i` by a join result of the same height keeps the
/// children well-formed, and splices its values in.
proof fn lemma_replace_child(c: Seq<Node>, cnt: Seq<int>, hc: nat, i: int, j: J)
    requires
        bwf(c, cnt, hc),
        0 <= i < c.len(),
        jwf(j, hc),
        flat(j.node).len() >= 1,
    ensures
        bwf(replace_child(c, i, j), replace_count(cnt, i, j), hc),
        replace_child(c, i, j).len() == c.len() + if j.split is Some { 1int } else { 0int },
        fl(replace_child(c, i, j)) == fl(c.subrange(0, i)) + jflat(j) + fl(c.subrange(i + 1, c.len() as int)),
{
    if j.split is Some {
        lemma_replace_child_split(c, cnt, hc, i, j);
    } else {
        lemma_replace_child_nosplit(c, cnt, hc, i, j);
    }
}

#[verifier::rlimit(30)]
proof fn lemma_insert_step(c: Seq<Node>, cnt: Seq<int>, h: nat, i: int, rem: int, x: int, j: J)
    requires
        wf(Node::Branch(c, cnt), h),
        0 <= i < c.len(),
        0 <= rem <= flat(c[i]).len(),
        jwf(j, (h - 1) as nat),
        jflat(j) == flat(c[i]).insert(rem, x),
        flat(j.node).len() >= 1,
    ensures
        jwf(insert_branch(replace_child(c, i, j), replace_count(cnt, i, j)), h),
        jflat(insert_branch(replace_child(c, i, j), replace_count(cnt, i, j))) == fl(c).insert(flat_upto(c, i).len() + rem, x),
        flat(insert_branch(replace_child(c, i, j), replace_count(cnt, i, j)).node).len() >= 1,
{
    let hc = (h - 1) as nat;
    let num = c.len() as int;
    lemma_wf_bwf(c, cnt, h);
    lemma_replace_child(c, cnt, hc, i, j);
    lemma_insert_branch(replace_child(c, i, j), replace_count(cnt, i, j), hc);
    lemma_fl_split3(c, i);
    let (a, b, cc) = (fl(c.subrange(0, i)), flat(c[i]), fl(c.subrange(i + 1, num)));
    assert(a + b.insert(rem, x) + cc =~= (a + b + cc).insert(a.len() + rem, x));
    lemma_fl_split3(replace_child(c, i, j), 0);
}

pub proof fn lemma_insert(n: Node, h: nat, r: int, x: int)
    requires
        wf(n, h),
        0 <= r <= flat(n).len(),
    ensures
        insert(n, r, x) is Some,
        jwf(insert(n, r, x).unwrap(), h),
        jflat(insert(n, r, x).unwrap()) == flat(n).insert(r, x),
        flat(insert(n, r, x).unwrap().node).len() >= 1,
    decreases n,
{
    match n {
        Node::Leaf(v) => {
            let vals = v.insert(r, x);
            if vals.len() > 16 {
                assert(vals.subrange(0, 8) + vals.subrange(8, vals.len() as int) =~= vals);
            }
        },
        Node::Branch(c, cnt) => {
            lemma_descend(c, cnt, h, r, true);
            let (i, rem) = cfr(cnt, c.len() as int, 0, r, true);
            assert(wf(c[i], (h - 1) as nat));
            lemma_insert(c[i], (h - 1) as nat, rem, x);
            lemma_insert_step(c, cnt, h, i, rem, x, insert(c[i], rem, x).unwrap());
        },
    }
}

/// Inserting into a list: `make_root` of the result is a well-formed tree
/// whose values are the old ones with `x` inserted at `r`.
pub proof fn theorem_insert(root: Node, h: nat, r: int, x: int)
    requires
        wf(root, h),
        0 <= r <= flat(root).len(),
    ensures
        wf(make_root(insert(root, r, x).unwrap()), height(make_root(insert(root, r, x).unwrap()))),
        flat(make_root(insert(root, r, x).unwrap())) == flat(root).insert(r, x),
{
    lemma_insert(root, h, r, x);
    lemma_make_root(insert(root, r, x).unwrap(), h);
}

pub proof fn lemma_make_root(j: J, h: nat)
    requires
        jwf(j, h),
    ensures
        wf(make_root(j), height(make_root(j))),
        flat(make_root(j)) == jflat(j),
{
    lemma_wf(j.node, h);
    if let Some((sn, sc)) = j.split {
        let c = seq![j.node, sn];
        assert(c =~= seq![j.node] + seq![sn]);
        lemma_fl_concat(seq![j.node], seq![sn]);
        lemma_fl_single(j.node);
        lemma_fl_single(sn);
        assert(wf(make_root(j), h + 1));
        lemma_wf(make_root(j), h + 1);
    }
}

// removing

proof fn lemma_concat_nodes(a: Node, b: Node, h: nat)
    requires
        wf(a, h),
        wf(b, h),
        num(a) + num(b) <= 16,
    ensures
        wf(concat_nodes(a, b), h),
        flat(concat_nodes(a, b)) == flat(a) + flat(b),
        num(concat_nodes(a, b)) == num(a) + num(b),
{
    match (a, b) {
        (Node::Branch(ca, na), Node::Branch(cb, nb)) => {
            let c = ca + cb;
            let cnt = na + nb;
            assert forall|j: int| 0 <= j < c.len() implies wf(#[trigger] c[j], (h - 1) as nat) && cnt[j] == flat(c[j]).len() && flat(c[j]).len() >= 1 by {
                if j < ca.len() {
                    assert(c[j] == ca[j] && cnt[j] == na[j]);
                } else {
                    assert(c[j] == cb[j - ca.len()] && cnt[j] == nb[j - ca.len()]);
                }
            }
            lemma_fl_concat(ca, cb);
        },
        _ => {},
    }
}

pub open spec fn rm_ok(n: Node, h: nat, r: int, m: Node) -> bool {
    &&& wf_rm(m, h)
    &&& flat(m) == flat(n).remove(r)
    &&& (num(m) == 0 <==> flat(m).len() == 0)
}

proof fn lemma_rm_wf(m: Node, h: nat)
    requires
        wf_rm(m, h),
        num(m) >= 1,
    ensures
        wf(m, h),
        count(m) == flat(m).len(),
        flat(m).len() >= 1 || m is Leaf,
{
    if let Node::Branch(c, cnt) = m {
        lemma_bwf_wf(c, cnt, h);
    }
    lemma_wf(m, h);
}

#[verifier::rlimit(30)]
proof fn lemma_remove_drop(c: Seq<Node>, cnt: Seq<int>, h: nat, i: int, rem: int, m: Node)
    requires
        wf(Node::Branch(c, cnt), h),
        0 <= i < c.len(),
        0 <= rem < flat(c[i]).len(),
        rm_ok(c[i], (h - 1) as nat, rem, m),
        num(m) == 0,
    ensures
        rm_ok(Node::Branch(c, cnt), h, flat_upto(c, i).len() + rem, remove_finish(c, cnt, i, m)),
{
    let hc = (h - 1) as nat;
    let num_c = c.len() as int;
    lemma_wf_bwf(c, cnt, h);
    lemma_fl_split3(c, i);
    let pre = c.subrange(0, i);
    let post = c.subrange(i + 1, num_c);
    let (a, b, cc) = (fl(pre), flat(c[i]), fl(post));
    let r = a.len() + rem;
    assert((a + b + cc).remove(r) =~= a + b.remove(rem) + cc);
    let res = remove_finish(c, cnt, i, m);
    // the child had one value, and is dropped
    let c1 = c.remove(i);
    let cnt1 = cnt.remove(i);
    assert(c1 =~= pre + post);
    lemma_fl_concat(pre, post);
    assert(b.remove(rem) =~= Seq::<int>::empty());
    assert forall|k: int| 0 <= k < c1.len() implies wf(#[trigger] c1[k], hc) && cnt1[k] == flat(c1[k]).len() && flat(c1[k]).len() >= 1 by {
        if k < i {
            assert(c1[k] == c[k]);
        } else {
            assert(c1[k] == c[k + 1]);
        }
    }
    assert(a + b.remove(rem) + cc =~= a + cc);
    if c1.len() > 0 {
        lemma_fl_split3(c1, 0);
    }
}

/// After merging child `first` with child `first + 1` into `merged`, the
/// children are still well-formed.
proof fn lemma_merged_children(c: Seq<Node>, cnt: Seq<int>, hc: nat, first: int, merged: Node)
    requires
        bwf(c, cnt, hc),
        0 <= first,
        first + 1 < c.len(),
        wf(merged, hc),
        flat(merged).len() >= 1,
    ensures
        bwf(c.remove(first + 1).update(first, merged), cnt.remove(first + 1).update(first, count(merged)), hc),
        fl(c.remove(first + 1).update(first, merged)) == fl(c.subrange(0, first)) + flat(merged) + fl(c.subrange(first + 2, c.len() as int)),
{
    lemma_wf(merged, hc);
    let c1 = c.remove(first + 1).update(first, merged);
    let cnt1 = cnt.remove(first + 1).update(first, count(merged));
    assert forall|k: int| 0 <= k < c1.len() implies wf(#[trigger] c1[k], hc) && cnt1[k] == flat(c1[k]).len() && flat(c1[k]).len() >= 1 by {
        if k < first {
            assert(c1[k] == c[k] && cnt1[k] == cnt[k]);
        } else if k > first {
            assert(c1[k] == c[k + 1] && cnt1[k] == cnt[k + 1]);
        }
    }
    let pre = c.subrange(0, first);
    let post2 = c.subrange(first + 2, c.len() as int);
    assert(c1 =~= pre + seq![merged] + post2);
    lemma_fl_concat(pre + seq![merged], post2);
    lemma_fl_concat(pre, seq![merged]);
    lemma_fl_single(merged);
}

#[verifier::rlimit(30)]
proof fn lemma_remove_merge_right(c: Seq<Node>, cnt: Seq<int>, h: nat, i: int, rem: int, m: Node)
    requires
        wf(Node::Branch(c, cnt), h),
        0 <= i,
        i + 1 < c.len(),
        0 <= rem < flat(c[i]).len(),
        rm_ok(c[i], (h - 1) as nat, rem, m),
        num(m) >= 1,
        num(m) < 8,
        num(m) + num(c[i + 1]) <= 16,
    ensures
        rm_ok(Node::Branch(c, cnt), h, flat_upto(c, i).len() + rem, remove_finish(c, cnt, i, m)),
{
    let hc = (h - 1) as nat;
    let num_c = c.len() as int;
    lemma_wf_bwf(c, cnt, h);
    lemma_rm_wf(m, hc);
    lemma_fl_split3(c, i);
    let pre = c.subrange(0, i);
    let post = c.subrange(i + 1, num_c);
    let (a, b, cc) = (fl(pre), flat(c[i]), fl(post));
    let nb = c[i + 1];
    assert(wf(nb, hc));
    lemma_concat_nodes(m, nb, hc);
    let merged = concat_nodes(m, nb);
    lemma_merged_children(c, cnt, hc, i, merged);
    let post2 = c.subrange(i + 2, num_c);
    assert(post =~= seq![nb] + post2);
    lemma_fl_concat(seq![nb], post2);
    lemma_fl_single(nb);
    let c1 = c.remove(i + 1).update(i, merged);
    assert(remove_finish(c, cnt, i, m) == Node::Branch(c1, cnt.remove(i + 1).update(i, count(merged))));
    assert(fl(c1) =~= (a + b + cc).remove(a.len() + rem));
    lemma_fl_split3(c1, 0);
}

#[verifier::rlimit(30)]
proof fn lemma_remove_merge_left(c: Seq<Node>, cnt: Seq<int>, h: nat, i: int, rem: int, m: Node)
    requires
        wf(Node::Branch(c, cnt), h),
        i >= 1,
        i + 1 == c.len(),
        0 <= rem < flat(c[i]).len(),
        rm_ok(c[i], (h - 1) as nat, rem, m),
        num(m) >= 1,
        num(m) < 8,
        num(m) + num(c[i - 1]) <= 16,
    ensures
        rm_ok(Node::Branch(c, cnt), h, flat_upto(c, i).len() + rem, remove_finish(c, cnt, i, m)),
{
    let hc = (h - 1) as nat;
    let num_c = c.len() as int;
    lemma_wf_bwf(c, cnt, h);
    lemma_rm_wf(m, hc);
    lemma_fl_split3(c, i);
    let pre = c.subrange(0, i);
    let (a, b) = (fl(pre), flat(c[i]));
    assert(c.subrange(i + 1, num_c) =~= Seq::<Node>::empty());
    let nb = c[i - 1];
    assert(wf(nb, hc));
    lemma_concat_nodes(nb, m, hc);
    let merged = concat_nodes(nb, m);
    lemma_merged_children(c, cnt, hc, i - 1, merged);
    let pre2 = c.subrange(0, i - 1);
    assert(pre =~= pre2 + seq![nb]);
    lemma_fl_concat(pre2, seq![nb]);
    lemma_fl_single(nb);
    assert(c.subrange(i + 1, num_c) =~= Seq::<Node>::empty());
    let c1 = c.remove(i).update(i - 1, merged);
    assert(remove_finish(c, cnt, i, m) == Node::Branch(c1, cnt.remove(i).update(i - 1, count(merged))));
    assert(fl(c.subrange(i + 1, num_c)) =~= Seq::<int>::empty());
    assert(fl(c1) =~= (a + b + fl(c.subrange(i + 1, num_c))).remove(a.len() + rem));
    lemma_fl_split3(c1, 0);
}

proof fn lemma_remove_merge(c: Seq<Node>, cnt: Seq<int>, h: nat, i: int, rem: int, m: Node)
    requires
        wf(Node::Branch(c, cnt), h),
        0 <= i < c.len(),
        0 <= rem < flat(c[i]).len(),
        rm_ok(c[i], (h - 1) as nat, rem, m),
        num(m) >= 1 && num(m) < 8 && c.len() > 1 && num(m) + num(c[if i + 1 >= c.len() { i - 1 } else { i + 1 }]) <= 16,
    ensures
        rm_ok(Node::Branch(c, cnt), h, flat_upto(c, i).len() + rem, remove_finish(c, cnt, i, m)),
{
    if i + 1 >= c.len() {
        lemma_remove_merge_left(c, cnt, h, i, rem, m);
    } else {
        lemma_remove_merge_right(c, cnt, h, i, rem, m);
    }
}

#[verifier::rlimit(30)]
proof fn lemma_remove_update(c: Seq<Node>, cnt: Seq<int>, h: nat, i: int, rem: int, m: Node)
    requires
        wf(Node::Branch(c, cnt), h),
        0 <= i < c.len(),
        0 <= rem < flat(c[i]).len(),
        rm_ok(c[i], (h - 1) as nat, rem, m),
        num(m) >= 1,
        !(num(m) >= 1 && num(m) < 8 && c.len() > 1 && num(m) + num(c[if i + 1 >= c.len() { i - 1 } else { i + 1 }]) <= 16),
    ensures
        rm_ok(Node::Branch(c, cnt), h, flat_upto(c, i).len() + rem, remove_finish(c, cnt, i, m)),
{
    let hc = (h - 1) as nat;
    let num_c = c.len() as int;
    lemma_wf_bwf(c, cnt, h);
    lemma_fl_split3(c, i);
    let pre = c.subrange(0, i);
    let post = c.subrange(i + 1, num_c);
    let (a, b, cc) = (fl(pre), flat(c[i]), fl(post));
    let r = a.len() + rem;
    assert((a + b + cc).remove(r) =~= a + b.remove(rem) + cc);
    let res = remove_finish(c, cnt, i, m);
    lemma_rm_wf(m, hc);
    let c1 = c.update(i, m);
    let cnt1 = cnt.update(i, count(m));
    assert(res == Node::Branch(c1, cnt1));
    assert forall|k: int| 0 <= k < c1.len() implies wf(#[trigger] c1[k], hc) && cnt1[k] == flat(c1[k]).len() && flat(c1[k]).len() >= 1 by {
        if k != i {
            assert(c1[k] == c[k] && cnt1[k] == cnt[k]);
        }
    }
    lemma_fl_split3(c1, i);
    assert(c1.subrange(0, i) =~= pre);
    assert(c1.subrange(i + 1, num_c) =~= post);
    lemma_fl_split3(c1, 0);
}

proof fn lemma_remove_finish(c: Seq<Node>, cnt: Seq<int>, h: nat, i: int, rem: int, m: Node)
    requires
        wf(Node::Branch(c, cnt), h),
        0 <= i < c.len(),
        0 <= rem < flat(c[i]).len(),
        rm_ok(c[i], (h - 1) as nat, rem, m),
    ensures
        rm_ok(Node::Branch(c, cnt), h, flat_upto(c, i).len() + rem, remove_finish(c, cnt, i, m)),
{
    if num(m) == 0 {
        lemma_remove_drop(c, cnt, h, i, rem, m);
    } else if num(m) >= 1 && num(m) < 8 && c.len() > 1 && num(m) + num(c[if i + 1 >= c.len() { i - 1 } else { i + 1 }]) <= 16 {
        lemma_remove_merge(c, cnt, h, i, rem, m);
    } else {
        lemma_remove_update(c, cnt, h, i, rem, m);
    }
}

pub proof fn lemma_remove(n: Node, h: nat, r: int)
    requires
        wf(n, h),
        0 <= r < flat(n).len(),
    ensures
        remove(n, r) is Some,
        rm_ok(n, h, r, remove(n, r).unwrap()),
    decreases n,
{
    match n {
        Node::Leaf(v) => {},
        Node::Branch(c, cnt) => {
            let num_c = c.len() as int;
            lemma_descend(c, cnt, h, r, false);
            let (i, rem) = cfr(cnt, num_c, 0, r, false);
            assert(wf(c[i], (h - 1) as nat));
            lemma_remove(c[i], (h - 1) as nat, rem);
            lemma_remove_finish(c, cnt, h, i, rem, remove(c[i], rem).unwrap());
        },
    }
}

proof fn lemma_collapse(n: Node, h: nat)
    requires
        wf(n, h),
    ensures
        wf(collapse(n), height(collapse(n))),
        flat(collapse(n)) == flat(n),
    decreases n,
{
    lemma_wf(n, h);
    if let Node::Branch(c, cnt) = n {
        if c.len() == 1 {
            assert(wf(c[0], (h - 1) as nat));
            lemma_collapse(c[0], (h - 1) as nat);
            lemma_fl_single(c[0]);
            assert(c =~= seq![c[0]]);
        }
    }
}

/// Removing from a list: the result is a well-formed tree whose values are
/// the old ones without the one at `r`.
pub proof fn theorem_remove(root: Node, h: nat, r: int)
    requires
        wf(root, h),
        0 <= r < flat(root).len(),
    ensures
        remove_root(root, r) is Some,
        wf(remove_root(root, r).unwrap(), height(remove_root(root, r).unwrap())),
        flat(remove_root(root, r).unwrap()) == flat(root).remove(r),
{
    if flat(root).len() == 1 {
        assert(flat(root).remove(0) =~= Seq::<int>::empty());
    } else {
        lemma_remove(root, h, r);
        let m = remove(root, r).unwrap();
        lemma_rm_wf(m, h);
        lemma_collapse(m, h);
    }
}

// joining and splitting

/// `btree_assemble_leaf`: one leaf, or two halves.
pub open spec fn assemble_leaf(vals: Seq<int>) -> J {
    let total = vals.len() as int;
    if total <= 16 {
        J { node: Node::Leaf(vals), count: total, split: None }
    } else {
        let l = total / 2;
        J { node: Node::Leaf(vals.subrange(0, l)), count: l, split: Some((Node::Leaf(vals.subrange(l, total)), total - l)) }
    }
}

/// `btree_assemble_branch`: one branch, or two halves.
pub open spec fn assemble_branch(c: Seq<Node>, cnt: Seq<int>) -> J {
    let total = c.len() as int;
    if total <= 16 {
        J { node: Node::Branch(c, cnt), count: sum(cnt, total), split: None }
    } else {
        let l = total / 2;
        J {
            node: Node::Branch(c.subrange(0, l), cnt.subrange(0, l)),
            count: sum(cnt.subrange(0, l), l),
            split: Some((Node::Branch(c.subrange(l, total), cnt.subrange(l, total)), sum(cnt.subrange(l, total), total - l))),
        }
    }
}

/// `btree_merge_nodes`: two nodes of the same height, `a` first.
pub open spec fn merge_nodes(a: Node, b: Node) -> J {
    match (a, b) {
        (Node::Leaf(va), Node::Leaf(vb)) => assemble_leaf(va + vb),
        (Node::Branch(ca, na), Node::Branch(cb, nb)) => assemble_branch(ca + cb, na + nb),
        _ => J { node: a, count: 0, split: None },
    }
}

/// `btree_join_right`: `b` joined into the rightmost spine of the taller `a`.
pub open spec fn join_right(a: Node, ha: int, b: Node, hb: int) -> Option<J>
    decreases a,
{
    match a {
        Node::Branch(c, cnt) => if c.len() == 0 {
            None
        } else {
            let last = c.len() - 1;
            let sub = if ha - 1 == hb {
                Some(merge_nodes(c[last], b))
            } else {
                join_right(c[last], ha - 1, b, hb)
            };
            match sub {
                None => None,
                Some(j) => Some(assemble_branch(replace_child(c, last, j), replace_count(cnt, last, j))),
            }
        },
        Node::Leaf(_) => None,
    }
}

/// `btree_join_left`: the shorter `a` joined into the leftmost spine of `b`.
pub open spec fn join_left(a: Node, ha: int, b: Node, hb: int) -> Option<J>
    decreases b,
{
    match b {
        Node::Branch(c, cnt) => if c.len() == 0 {
            None
        } else {
            let sub = if hb - 1 == ha {
                Some(merge_nodes(a, c[0]))
            } else {
                join_left(a, ha, c[0], hb - 1)
            };
            match sub {
                None => None,
                Some(j) => Some(assemble_branch(replace_child(c, 0, j), replace_count(cnt, 0, j))),
            }
        },
        Node::Leaf(_) => None,
    }
}

/// `btree_join`.
#[verifier::opaque]
pub open spec fn join(a: Node, b: Node) -> Option<Node> {
    let ha = height(a) as int;
    let hb = height(b) as int;
    let r = if ha == hb {
        Some(merge_nodes(a, b))
    } else if ha > hb {
        join_right(a, ha, b, hb)
    } else {
        join_left(a, ha, b, hb)
    };
    match r {
        Some(j) => Some(make_root(j)),
        None => None,
    }
}

/// `btree_subtree`: a run of sibling children as one tree.
#[verifier::opaque]
pub open spec fn subtree(c: Seq<Node>, cnt: Seq<int>) -> Node {
    if c.len() == 0 {
        Node::Leaf(Seq::empty())
    } else if c.len() == 1 {
        c[0]
    } else {
        assemble_branch(c, cnt).node
    }
}

/// `btree_split`: the trees of the values before and from `r`.
pub open spec fn split(n: Node, r: int) -> Option<(Node, Node)>
    decreases n,
{
    match n {
        Node::Leaf(v) => if 0 <= r <= v.len() {
            Some((Node::Leaf(v.subrange(0, r)), Node::Leaf(v.subrange(r, v.len() as int))))
        } else {
            None
        },
        Node::Branch(c, cnt) => {
            let num_c = c.len() as int;
            let (i, rem) = cfr(cnt, num_c, 0, r, true);
            if !(0 <= i < num_c) {
                None
            } else {
                match split(c[i], rem) {
                    None => None,
                    Some((cl, cr)) => {
                        let ls = subtree(c.subrange(0, i), cnt.subrange(0, i));
                        let rs = subtree(c.subrange(i + 1, num_c), cnt.subrange(i + 1, num_c));
                        match (join(ls, cl), join(cr, rs)) {
                            (Some(l), Some(rr)) => Some((l, rr)),
                            _ => None,
                        }
                    },
                }
            }
        },
    }
}

proof fn lemma_assemble_leaf(vals: Seq<int>)
    requires
        vals.len() <= 32,
    ensures
        jwf(assemble_leaf(vals), 0),
        jflat(assemble_leaf(vals)) == vals,
        vals.len() >= 1 ==> flat(assemble_leaf(vals).node).len() >= 1,
{
    let total = vals.len() as int;
    if total > 16 {
        assert(vals.subrange(0, total / 2) + vals.subrange(total / 2, total) =~= vals);
    }
}

proof fn lemma_assemble_branch(c: Seq<Node>, cnt: Seq<int>, hc: nat)
    requires
        bwf(c, cnt, hc),
        1 <= c.len() <= 32,
    ensures
        jwf(assemble_branch(c, cnt), hc + 1),
        jflat(assemble_branch(c, cnt)) == fl(c),
        flat(assemble_branch(c, cnt).node).len() >= 1,
{
    let total = c.len() as int;
    if total <= 16 {
        lemma_sum_len(c, cnt, total);
        lemma_fl_split3(c, 0);
    } else {
        let l = total / 2;
        let (cl, cr) = (c.subrange(0, l), c.subrange(l, total));
        let (nl, nr) = (cnt.subrange(0, l), cnt.subrange(l, total));
        assert(c =~= cl + cr);
        lemma_fl_concat(cl, cr);
        assert forall|j: int| 0 <= j < cl.len() implies wf(#[trigger] cl[j], hc) && nl[j] == flat(cl[j]).len() && flat(cl[j]).len() >= 1 by {
            assert(cl[j] == c[j]);
        }
        assert forall|j: int| 0 <= j < cr.len() implies wf(#[trigger] cr[j], hc) && nr[j] == flat(cr[j]).len() && flat(cr[j]).len() >= 1 by {
            assert(cr[j] == c[j + l]);
        }
        lemma_sum_len(cl, nl, l);
        lemma_sum_len(cr, nr, total - l);
        lemma_fl_split3(cl, 0);
        lemma_fl_split3(cr, 0);
    }
}

proof fn lemma_merge_nodes(a: Node, b: Node, h: nat)
    requires
        wf(a, h),
        wf(b, h),
    ensures
        jwf(merge_nodes(a, b), h),
        jflat(merge_nodes(a, b)) == flat(a) + flat(b),
        flat(a).len() + flat(b).len() >= 1 ==> flat(merge_nodes(a, b).node).len() >= 1,
{
    match (a, b) {
        (Node::Leaf(va), Node::Leaf(vb)) => {
            lemma_assemble_leaf(va + vb);
        },
        (Node::Branch(ca, na), Node::Branch(cb, nb)) => {
            let c = ca + cb;
            let cnt = na + nb;
            assert forall|j: int| 0 <= j < c.len() implies wf(#[trigger] c[j], (h - 1) as nat) && cnt[j] == flat(c[j]).len() && flat(c[j]).len() >= 1 by {
                if j < ca.len() {
                    assert(c[j] == ca[j] && cnt[j] == na[j]);
                } else {
                    assert(c[j] == cb[j - ca.len()] && cnt[j] == nb[j - ca.len()]);
                }
            }
            lemma_fl_concat(ca, cb);
            lemma_assemble_branch(c, cnt, (h - 1) as nat);
        },
        _ => {
            lemma_wf(a, h);
            lemma_wf(b, h);
        },
    }
}

proof fn lemma_join_right(a: Node, ha: nat, b: Node, hb: nat)
    requires
        wf(a, ha),
        wf(b, hb),
        ha > hb,
    ensures
        join_right(a, ha as int, b, hb as int) is Some,
        jwf(join_right(a, ha as int, b, hb as int).unwrap(), ha),
        jflat(join_right(a, ha as int, b, hb as int).unwrap()) == flat(a) + flat(b),
        flat(join_right(a, ha as int, b, hb as int).unwrap().node).len() >= 1,
    decreases a,
{
    if let Node::Branch(c, cnt) = a {
        let hc = (ha - 1) as nat;
        let last = c.len() - 1;
        lemma_wf_bwf(c, cnt, ha);
        assert(wf(c[last], hc));
        if ha - 1 == hb {
            lemma_merge_nodes(c[last], b, hc);
        } else {
            lemma_join_right(c[last], hc, b, hb);
        }
        let j = if ha - 1 == hb { merge_nodes(c[last], b) } else { join_right(c[last], hc as int, b, hb as int).unwrap() };
        lemma_replace_child(c, cnt, hc, last, j);
        lemma_assemble_branch(replace_child(c, last, j), replace_count(cnt, last, j), hc);
        lemma_fl_split3(c, last);
        assert(c.subrange(last + 1, c.len() as int) =~= Seq::<Node>::empty());
        assert(fl(c.subrange(last + 1, c.len() as int)) =~= Seq::<int>::empty());
        let pre = fl(c.subrange(0, last));
        assert(pre + (flat(c[last]) + flat(b)) + Seq::<int>::empty() =~= fl(c) + flat(b));
    }
}

proof fn lemma_join_left(a: Node, ha: nat, b: Node, hb: nat)
    requires
        wf(a, ha),
        wf(b, hb),
        hb > ha,
    ensures
        join_left(a, ha as int, b, hb as int) is Some,
        jwf(join_left(a, ha as int, b, hb as int).unwrap(), hb),
        jflat(join_left(a, ha as int, b, hb as int).unwrap()) == flat(a) + flat(b),
        flat(join_left(a, ha as int, b, hb as int).unwrap().node).len() >= 1,
    decreases b,
{
    if let Node::Branch(c, cnt) = b {
        let hc = (hb - 1) as nat;
        lemma_wf_bwf(c, cnt, hb);
        assert(wf(c[0], hc));
        if hb - 1 == ha {
            lemma_merge_nodes(a, c[0], hc);
        } else {
            lemma_join_left(a, ha, c[0], hc);
        }
        let j = if hb - 1 == ha { merge_nodes(a, c[0]) } else { join_left(a, ha as int, c[0], hc as int).unwrap() };
        lemma_replace_child(c, cnt, hc, 0, j);
        lemma_assemble_branch(replace_child(c, 0, j), replace_count(cnt, 0, j), hc);
        lemma_fl_split3(c, 0);
        assert(c.subrange(0, 0) =~= Seq::<Node>::empty());
        assert(fl(c.subrange(0, 0)) =~= Seq::<int>::empty());
        let post = fl(c.subrange(1, c.len() as int));
        assert(Seq::<int>::empty() + (flat(a) + flat(c[0])) + post =~= flat(a) + fl(c));
    }
}

/// Joining two lists gives a well-formed tree of their values, in order.
pub proof fn lemma_join(a: Node, ha: nat, b: Node, hb: nat)
    requires
        wf(a, ha),
        wf(b, hb),
    ensures
        join(a, b) is Some,
        wf(join(a, b).unwrap(), height(join(a, b).unwrap())),
        flat(join(a, b).unwrap()) == flat(a) + flat(b),
{
    reveal(join);
    lemma_wf(a, ha);
    lemma_wf(b, hb);
    if ha == hb {
        lemma_merge_nodes(a, b, ha);
        lemma_make_root(merge_nodes(a, b), ha);
    } else if ha > hb {
        lemma_join_right(a, ha, b, hb);
        lemma_make_root(join_right(a, ha as int, b, hb as int).unwrap(), ha);
    } else {
        lemma_join_left(a, ha, b, hb);
        lemma_make_root(join_left(a, ha as int, b, hb as int).unwrap(), hb);
    }
}

proof fn lemma_subtree(c: Seq<Node>, cnt: Seq<int>, hc: nat)
    requires
        bwf(c, cnt, hc),
        c.len() <= 16,
    ensures
        wf(subtree(c, cnt), height(subtree(c, cnt))),
        flat(subtree(c, cnt)) == fl(c),
{
    reveal(subtree);
    if c.len() == 0 {
    } else if c.len() == 1 {
        lemma_fl_single(c[0]);
        assert(c =~= seq![c[0]]);
        assert(wf(c[0], hc));
        lemma_wf(c[0], hc);
    } else {
        lemma_assemble_branch(c, cnt, hc);
        lemma_wf(assemble_branch(c, cnt).node, hc + 1);
    }
}

proof fn lemma_bwf_subrange(c: Seq<Node>, cnt: Seq<int>, hc: nat, a: int, b: int)
    requires
        bwf(c, cnt, hc),
        0 <= a <= b <= c.len(),
    ensures
        bwf(c.subrange(a, b), cnt.subrange(a, b), hc),
{
    let cs = c.subrange(a, b);
    let ns = cnt.subrange(a, b);
    assert forall|j: int| 0 <= j < cs.len() implies wf(#[trigger] cs[j], hc) && ns[j] == flat(cs[j]).len() && flat(cs[j]).len() >= 1 by {
        assert(cs[j] == c[j + a]);
    }
}

#[verifier::rlimit(30)]
proof fn lemma_split_step(c: Seq<Node>, cnt: Seq<int>, h: nat, i: int, rem: int, cl: Node, cr: Node)
    requires
        wf(Node::Branch(c, cnt), h),
        0 <= i < c.len(),
        0 <= rem <= flat(c[i]).len(),
        wf(cl, height(cl)),
        wf(cr, height(cr)),
        flat(cl) == flat(c[i]).subrange(0, rem),
        flat(cr) == flat(c[i]).subrange(rem, flat(c[i]).len() as int),
    ensures
        ({
            let num_c = c.len() as int;
            let ls = subtree(c.subrange(0, i), cnt.subrange(0, i));
            let rs = subtree(c.subrange(i + 1, num_c), cnt.subrange(i + 1, num_c));
            let r = flat_upto(c, i).len() + rem;
            &&& join(ls, cl) is Some
            &&& join(cr, rs) is Some
            &&& wf(join(ls, cl).unwrap(), height(join(ls, cl).unwrap()))
            &&& wf(join(cr, rs).unwrap(), height(join(cr, rs).unwrap()))
            &&& flat(join(ls, cl).unwrap()) == fl(c).subrange(0, r)
            &&& flat(join(cr, rs).unwrap()) == fl(c).subrange(r, fl(c).len() as int)
        }),
{
    let num_c = c.len() as int;
    let hc = (h - 1) as nat;
    lemma_wf_bwf(c, cnt, h);
    lemma_bwf_subrange(c, cnt, hc, 0, i);
    lemma_bwf_subrange(c, cnt, hc, i + 1, num_c);
    let ls = subtree(c.subrange(0, i), cnt.subrange(0, i));
    let rs = subtree(c.subrange(i + 1, num_c), cnt.subrange(i + 1, num_c));
    lemma_subtree(c.subrange(0, i), cnt.subrange(0, i), hc);
    lemma_subtree(c.subrange(i + 1, num_c), cnt.subrange(i + 1, num_c), hc);
    lemma_join(ls, height(ls), cl, height(cl));
    lemma_join(cr, height(cr), rs, height(rs));
    lemma_fl_split3(c, i);
    let (a, b, cc) = (fl(c.subrange(0, i)), flat(c[i]), fl(c.subrange(i + 1, num_c)));
    let all = a + b + cc;
    let r = a.len() + rem;
    assert(a + b.subrange(0, rem) =~= all.subrange(0, r));
    assert(b.subrange(rem, b.len() as int) + cc =~= all.subrange(r, all.len() as int));
}

/// Splitting a list at `r` gives well-formed trees of the values before
/// and from `r`. `LinkedArrayListSlice` is two splits.
pub proof fn lemma_split(n: Node, h: nat, r: int)
    requires
        wf(n, h),
        0 <= r <= flat(n).len(),
    ensures
        split(n, r) is Some,
        ({
            let (l, rr) = split(n, r).unwrap();
            &&& wf(l, height(l))
            &&& wf(rr, height(rr))
            &&& flat(l) == flat(n).subrange(0, r)
            &&& flat(rr) == flat(n).subrange(r, flat(n).len() as int)
        }),
    decreases n,
{
    if let Node::Branch(c, cnt) = n {
        let hc = (h - 1) as nat;
        lemma_descend(c, cnt, h, r, true);
        let (i, rem) = cfr(cnt, c.len() as int, 0, r, true);
        assert(wf(c[i], hc));
        lemma_split(c[i], hc, rem);
        let (cl, cr) = split(c[i], rem).unwrap();
        lemma_split_step(c, cnt, h, i, rem, cl, cr);
    }
}

/// An empty list is an empty leaf.
pub proof fn lemma_empty_list()
    ensures
        wf(Node::Leaf(Seq::empty()), 0),
        flat(Node::Leaf(Seq::empty())) == Seq::<int>::empty(),
{
}

} // verus!
