/*!

Examples of data structures and algorithms in Fungi.

### Basics

- [`basic_read_effects`](https://docs.rs/fungi-lang/0/src/fungi_lang/examples/basic_read_effects.rs.html)
demonstrate _read effects_, which track which reference cells and thunks a program observes and forces, respectively.
- [`basic_write_scope`](https://docs.rs/fungi-lang/0/src/fungi_lang/examples/basic_write_scope.rs.html)
demonstrate _write scopes_, which distinctly qualify written names for different dynamic calling contexts.

### Sequences

Sequences of natural numbers, represented as probabilistically-balanced binary trees (level trees):
- [`seq_max`](https://docs.rs/fungi-lang/0/src/fungi_lang/examples/seq_max.rs.html) 
finds the maximum element in a sequence.
 - [`seq_filter`](https://docs.rs/fungi-lang/0/src/fungi_lang/examples/seq_filter.rs.html)
filters a sequence of elements, producing a new (smaller) sequence.

### Sets

_In progress_

Sets of natural numbers, represented as probabilistically-balanced binary hash tries:
- [`trie_join`](https://docs.rs/fungi-lang/0/src/fungi_lang/examples/trie.rs.html) 
joins two sets (as tries) into a single set (as a trie).
 - [`trie_of_seq`](https://docs.rs/fungi-lang/0/src/fungi_lang/examples/trie.rs.html)
build a set of elements (as a hash trie) from a sequence of elements (as a level tree).

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


// --- In progress:
pub mod trie;


// --- Regression tests
pub mod basic_read_effects;
pub mod basic_write_effects;
pub mod basic_write_scope;

