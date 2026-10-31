//! Machine-checked proofs about xitdb's on-disk formats and core
//! algorithms, checked by [Verus](https://github.com/verus-lang/verus).
//! See `verus/README.md` for what is proved and what isn't.

pub mod array_list;
pub mod encoding;
pub mod hamt;
