//! Where the B-trees live: nodes of sorted maps (`sorted.rs`) and linked
//! array lists (`linked_list.rs`) stored at positions, with children as
//! pointers, as `read_sorted_node` / `read_btree_node` read them.
//!
//! A stored tree materializes into the functional model those modules
//! verify. Every write the B-tree code makes goes through
//! `sorted_write_node` / `btree_write_node` (in place only if the node is
//! reusable, that is, from `frozen` on; otherwise appended),
//! `write_sorted_node` / `write_btree_node` (appended), or appends a key or
//! value. None of them writes a committed position ([`lemma_writes_keep`]),
//! and a committed tree materializes to the same tree in any store that kept
//! the committed positions ([`lemma_sorted_snapshot`],
//! [`lemma_list_snapshot`]). So every sorted map and linked array list
//! committed before a transaction gives the same entries, lookups, ranks
//! and indexes afterwards.

use vstd::prelude::*;
use crate::sorted;
use crate::linked_list;

verus! {

/// A stored sorted map node: entries, or child positions, separators and
/// counts.
pub enum SNodeH {
    Leaf(Seq<(int, int)>),
    Branch(Seq<int>, Seq<int>, Seq<int>),
}

/// A stored linked array list node: values, or child positions and counts.
pub enum LNodeH {
    Leaf(Seq<int>),
    Branch(Seq<int>, Seq<int>),
}

pub struct BStore {
    pub sorted: Map<int, SNodeH>,
    pub lists: Map<int, LNodeH>,
    pub next: int,
}

pub open spec fn bstore_ok(s: BStore, frozen: int) -> bool {
    &&& 0 <= frozen <= s.next
    &&& forall|x: int| #[trigger] s.sorted.contains_key(x) ==> 0 <= x < s.next
    &&& forall|x: int| #[trigger] s.lists.contains_key(x) ==> 0 <= x < s.next
}

/// `t` kept every committed position of `s`.
pub open spec fn kept(s: BStore, t: BStore, frozen: int) -> bool {
    &&& t.next >= s.next
    &&& forall|x: int| x < frozen && #[trigger] s.sorted.contains_key(x) ==> t.sorted.contains_key(x) && t.sorted[x] == s.sorted[x]
    &&& forall|x: int| x < frozen && #[trigger] s.lists.contains_key(x) ==> t.lists.contains_key(x) && t.lists[x] == s.lists[x]
}

// the write primitives

/// `sorted_write_node`: in place if the old node is reusable, else
/// appended. Returns the store and the node's position.
pub open spec fn sorted_write_node(s: BStore, n: SNodeH, old: int, frozen: int) -> (BStore, int) {
    if old >= frozen && s.sorted.contains_key(old) {
        (BStore { sorted: s.sorted.insert(old, n), ..s }, old)
    } else {
        write_sorted_node(s, n)
    }
}

/// `write_sorted_node`: appended.
pub open spec fn write_sorted_node(s: BStore, n: SNodeH) -> (BStore, int) {
    (BStore { sorted: s.sorted.insert(s.next, n), next: s.next + 1, ..s }, s.next)
}

/// `btree_write_node`.
pub open spec fn btree_write_node(s: BStore, n: LNodeH, old: int, frozen: int) -> (BStore, int) {
    if old >= frozen && s.lists.contains_key(old) {
        (BStore { lists: s.lists.insert(old, n), ..s }, old)
    } else {
        write_btree_node(s, n)
    }
}

/// `write_btree_node`.
pub open spec fn write_btree_node(s: BStore, n: LNodeH) -> (BStore, int) {
    (BStore { lists: s.lists.insert(s.next, n), next: s.next + 1, ..s }, s.next)
}

/// Appending anything else (keys, values): only the length grows.
pub open spec fn append_bytes(s: BStore, len: int) -> BStore {
    BStore { next: s.next + len, ..s }
}

pub proof fn lemma_writes_keep(s: BStore, frozen: int, sn: SNodeH, ln: LNodeH, old: int, len: int)
    requires
        bstore_ok(s, frozen),
        len >= 0,
    ensures
        kept(s, sorted_write_node(s, sn, old, frozen).0, frozen) && bstore_ok(sorted_write_node(s, sn, old, frozen).0, frozen),
        kept(s, write_sorted_node(s, sn).0, frozen) && bstore_ok(write_sorted_node(s, sn).0, frozen),
        kept(s, btree_write_node(s, ln, old, frozen).0, frozen) && bstore_ok(btree_write_node(s, ln, old, frozen).0, frozen),
        kept(s, write_btree_node(s, ln).0, frozen) && bstore_ok(write_btree_node(s, ln).0, frozen),
        kept(s, append_bytes(s, len), frozen) && bstore_ok(append_bytes(s, len), frozen),
{
}

pub proof fn lemma_kept_trans(s: BStore, t: BStore, u: BStore, frozen: int)
    requires
        kept(s, t, frozen),
        kept(t, u, frozen),
    ensures
        kept(s, u, frozen),
{
}

// reading sorted maps

/// The positions a stored sorted map node reaches, within `h` levels.
pub open spec fn sreach(s: BStore, p: int, h: nat, x: int) -> bool
    decreases h,
{
    x == p || (h > 0 && s.sorted.contains_key(p) && match s.sorted[p] {
        SNodeH::Branch(c, _, _) => exists|i: int| 0 <= i < c.len() && sreach(s, #[trigger] c[i], (h - 1) as nat, x),
        _ => false,
    })
}

/// Every position the tree reaches is stored and committed.
pub open spec fn scommitted(s: BStore, p: int, h: nat, frozen: int) -> bool {
    forall|x: int| #[trigger] sreach(s, p, h, x) ==> x < frozen && s.sorted.contains_key(x)
}

/// `read_sorted_node`, all the way down: the functional tree.
pub open spec fn smat(s: BStore, p: int, h: nat) -> sorted::Node
    decreases h, 0int,
{
    match s.sorted[p] {
        SNodeH::Leaf(e) => sorted::Node::Leaf(e),
        SNodeH::Branch(c, sep, cnt) => if h == 0 {
            sorted::Node::Leaf(Seq::empty())
        } else {
            sorted::Node::Branch(smat_children(s, c, (h - 1) as nat, c.len() as int), sep, cnt)
        },
    }
}

/// The first `j` children, materialized.
pub open spec fn smat_children(s: BStore, c: Seq<int>, h: nat, j: int) -> Seq<sorted::Node>
    decreases h, j + 1,
{
    if j <= 0 {
        Seq::empty()
    } else {
        smat_children(s, c, h, j - 1).push(smat(s, c[j - 1], h))
    }
}

/// A committed sorted map reads the same in any store that kept the
/// committed positions.
pub proof fn lemma_sorted_snapshot(s: BStore, t: BStore, p: int, h: nat, frozen: int)
    requires
        scommitted(s, p, h, frozen),
        kept(s, t, frozen),
    ensures
        smat(t, p, h) == smat(s, p, h),
        forall|x: int| #[trigger] sreach(t, p, h, x) == sreach(s, p, h, x),
        scommitted(t, p, h, frozen),
    decreases h,
{
    assert(sreach(s, p, h, p));
    assert(t.sorted[p] == s.sorted[p]);
    if let SNodeH::Branch(c, sep, cnt) = s.sorted[p] {
        if h > 0 {
            assert forall|i: int| 0 <= i < c.len() implies {
                &&& smat(t, #[trigger] c[i], (h - 1) as nat) == smat(s, c[i], (h - 1) as nat)
                &&& forall|x: int| #[trigger] sreach(t, c[i], (h - 1) as nat, x) == sreach(s, c[i], (h - 1) as nat, x)
            } by {
                assert forall|x: int| #[trigger] sreach(s, c[i], (h - 1) as nat, x) implies x < frozen && s.sorted.contains_key(x) by {
                    assert(sreach(s, p, h, x));
                }
                lemma_sorted_snapshot(s, t, c[i], (h - 1) as nat, frozen);
            }
            lemma_smat_children(s, t, c, (h - 1) as nat, c.len() as int);
            assert forall|x: int| #[trigger] sreach(t, p, h, x) == sreach(s, p, h, x) by {
                if sreach(s, p, h, x) && x != p {
                    let i = choose|i: int| 0 <= i < c.len() && sreach(s, #[trigger] c[i], (h - 1) as nat, x);
                    assert(sreach(t, c[i], (h - 1) as nat, x));
                }
                if sreach(t, p, h, x) && x != p {
                    let i = choose|i: int| 0 <= i < c.len() && sreach(t, #[trigger] c[i], (h - 1) as nat, x);
                    assert(sreach(s, c[i], (h - 1) as nat, x));
                }
            }
        }
    }
}

proof fn lemma_smat_children(s: BStore, t: BStore, c: Seq<int>, h: nat, j: int)
    requires
        0 <= j <= c.len(),
        forall|i: int| 0 <= i < c.len() ==> smat(t, #[trigger] c[i], h) == smat(s, c[i], h),
    ensures
        smat_children(t, c, h, j) == smat_children(s, c, h, j),
    decreases j,
{
    if j > 0 {
        lemma_smat_children(s, t, c, h, j - 1);
        assert(smat(t, c[j - 1], h) == smat(s, c[j - 1], h));
    }
}

/// So every query on a committed sorted map gives the same answer.
pub proof fn theorem_sorted_snapshot_queries(s: BStore, t: BStore, root: int, h: nat, frozen: int, k: int, r: int)
    requires
        scommitted(s, root, h, frozen),
        kept(s, t, frozen),
    ensures
        sorted::flat(smat(t, root, h)) == sorted::flat(smat(s, root, h)),
        sorted::get(smat(t, root, h), k) == sorted::get(smat(s, root, h), k),
        sorted::rank(smat(t, root, h), k) == sorted::rank(smat(s, root, h), k),
        sorted::get_by_index(smat(t, root, h), r) == sorted::get_by_index(smat(s, root, h), r),
{
    lemma_sorted_snapshot(s, t, root, h, frozen);
}

// reading linked array lists

pub open spec fn lreach(s: BStore, p: int, h: nat, x: int) -> bool
    decreases h,
{
    x == p || (h > 0 && s.lists.contains_key(p) && match s.lists[p] {
        LNodeH::Branch(c, _) => exists|i: int| 0 <= i < c.len() && lreach(s, #[trigger] c[i], (h - 1) as nat, x),
        _ => false,
    })
}

pub open spec fn lcommitted(s: BStore, p: int, h: nat, frozen: int) -> bool {
    forall|x: int| #[trigger] lreach(s, p, h, x) ==> x < frozen && s.lists.contains_key(x)
}

/// `read_btree_node`, all the way down.
pub open spec fn lmat(s: BStore, p: int, h: nat) -> linked_list::Node
    decreases h, 0int,
{
    match s.lists[p] {
        LNodeH::Leaf(v) => linked_list::Node::Leaf(v),
        LNodeH::Branch(c, cnt) => if h == 0 {
            linked_list::Node::Leaf(Seq::empty())
        } else {
            linked_list::Node::Branch(lmat_children(s, c, (h - 1) as nat, c.len() as int), cnt)
        },
    }
}

pub open spec fn lmat_children(s: BStore, c: Seq<int>, h: nat, j: int) -> Seq<linked_list::Node>
    decreases h, j + 1,
{
    if j <= 0 {
        Seq::empty()
    } else {
        lmat_children(s, c, h, j - 1).push(lmat(s, c[j - 1], h))
    }
}

/// A committed linked array list reads the same in any store that kept the
/// committed positions.
pub proof fn lemma_list_snapshot(s: BStore, t: BStore, p: int, h: nat, frozen: int)
    requires
        lcommitted(s, p, h, frozen),
        kept(s, t, frozen),
    ensures
        lmat(t, p, h) == lmat(s, p, h),
        forall|x: int| #[trigger] lreach(t, p, h, x) == lreach(s, p, h, x),
        lcommitted(t, p, h, frozen),
    decreases h,
{
    assert(lreach(s, p, h, p));
    assert(t.lists[p] == s.lists[p]);
    if let LNodeH::Branch(c, cnt) = s.lists[p] {
        if h > 0 {
            assert forall|i: int| 0 <= i < c.len() implies {
                &&& lmat(t, #[trigger] c[i], (h - 1) as nat) == lmat(s, c[i], (h - 1) as nat)
                &&& forall|x: int| #[trigger] lreach(t, c[i], (h - 1) as nat, x) == lreach(s, c[i], (h - 1) as nat, x)
            } by {
                assert forall|x: int| #[trigger] lreach(s, c[i], (h - 1) as nat, x) implies x < frozen && s.lists.contains_key(x) by {
                    assert(lreach(s, p, h, x));
                }
                lemma_list_snapshot(s, t, c[i], (h - 1) as nat, frozen);
            }
            lemma_lmat_children(s, t, c, (h - 1) as nat, c.len() as int);
            assert forall|x: int| #[trigger] lreach(t, p, h, x) == lreach(s, p, h, x) by {
                if lreach(s, p, h, x) && x != p {
                    let i = choose|i: int| 0 <= i < c.len() && lreach(s, #[trigger] c[i], (h - 1) as nat, x);
                    assert(lreach(t, c[i], (h - 1) as nat, x));
                }
                if lreach(t, p, h, x) && x != p {
                    let i = choose|i: int| 0 <= i < c.len() && lreach(t, #[trigger] c[i], (h - 1) as nat, x);
                    assert(lreach(s, c[i], (h - 1) as nat, x));
                }
            }
        }
    }
}

proof fn lemma_lmat_children(s: BStore, t: BStore, c: Seq<int>, h: nat, j: int)
    requires
        0 <= j <= c.len(),
        forall|i: int| 0 <= i < c.len() ==> lmat(t, #[trigger] c[i], h) == lmat(s, c[i], h),
    ensures
        lmat_children(t, c, h, j) == lmat_children(s, c, h, j),
    decreases j,
{
    if j > 0 {
        lemma_lmat_children(s, t, c, h, j - 1);
        assert(lmat(t, c[j - 1], h) == lmat(s, c[j - 1], h));
    }
}

/// So every query on a committed linked array list gives the same answer.
pub proof fn theorem_list_snapshot_queries(s: BStore, t: BStore, root: int, h: nat, frozen: int, r: int)
    requires
        lcommitted(s, root, h, frozen),
        kept(s, t, frozen),
    ensures
        linked_list::flat(lmat(t, root, h)) == linked_list::flat(lmat(s, root, h)),
        linked_list::get(lmat(t, root, h), r) == linked_list::get(lmat(s, root, h), r),
{
    lemma_list_snapshot(s, t, root, h, frozen);
}

} // verus!
