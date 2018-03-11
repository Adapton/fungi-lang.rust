/*!

Examples of data structures and algorithms in Fungi.

### Sequences

Sequences of natural numbers, represented as probabilistically-balanced binary trees (level trees):
- [`seq_max`](https://docs.rs/fungi-lang/0/src/fungi_lang/examples/seq_max.rs.html) 
finds the maximum element in a sequence.
 - [`seq_filter`](https://docs.rs/fungi-lang/0/src/fungi_lang/examples/seq_filter.rs.html)
filters a sequence of elements, producing a new (smaller) sequence.

### Sets

Sets of natural numbers, represented as probabilistically-balanced binary hash tries:

**TODO**

### Quickhull

Computes the convex hull, in sorted order, of an unordered sequence of points in 2D space.

**TODO**

*/

/// Find the maximum element in a sequence
///
/// [Fungi listing](https://docs.rs/fungi-lang/0/src/fungi_lang/examples/seq_max.rs.html)
pub mod seq_max;

/// Filter a sequence of elements, producing a new (smaller) sequence
///
/// [Fungi listing](https://docs.rs/fungi-lang/0/src/fungi_lang/examples/seq_filter.rs.html)
pub mod seq_filter;

pub mod trie;
