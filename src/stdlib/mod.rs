/*!

Fungi standard library.

Based on collections in these papers:

- **Nominal memoization**: [_Incremental computation with names_, **OOPSLA 2015**](http://arxiv.org/abs/1503.07792).
- **Type and effect structures**: The draft [_Typed Adapton: Refinement types for incremental computation with precise names_](https://arxiv.org/abs/1610.00097).
*/

#[macro_use]

/// Sequences, as balanced level trees.
pub mod seq;
/// Vectors and *chunks* (named, referenced vectors).
pub mod vec;
/// Linked lists.
pub mod list;



// --- OLD -------------------------------------

// # Sequences in Fungi: 

// ## Linked lists vs Level trees
        
// In most functional languages, **linked lists** play a central role in
// organizing sequential data, the way that arrays play a central role in
// imperative languages.

// In Fungi, computations have the potential to be incremental, and as a
// result, we reconsider the role of linked lists in our functional
// programs.  In Fungi, linked-lists represent "iterators" --- lists
// sometimes organize sequences as their are processed or transformed ---
// but in Fungi, lists not the data structure for storing or editing that
// sequence data, or for aggregating it with folds or other iteration
// patterns.

// Instead, to organize sequences for accesses, updates or incremental
// folds, Fungi programs use balanced **level trees**.  In particular,
// before we iterate over a linked list, we create a balanced level tree
// from its elements to better organize later incremental reuse, via
// change propagation.

// ## Level trees

// Level trees are balanced, binary trees that represent sequences of
// elements, stored at their leaves.  A level tree permits O(log n) reads
// and writes to the sequence, where writes may overwrite, insert or
// remove elements from the sequence.

// When the editor updates a sequence, they often want to do so
// imperatively.  When the archivist updates a sequence, they do so
// functionally, such that the update preserves (and does not overwrite)
// existing store data.

// Below, we focus on the archivist's operations for sequences:
// Conversion to and from lists, and various flavors of folding (over
// level trees, not lists).

// During change propagation over the archivist's incremental folds, this
// balanced tree structure ensures that the (isomorphic) dependency graph
// it induces is shallow.  In particular, from any root of a fold to any
// thunk it calls (transitively), there are at most O(log n) transitive
// force edges to clean or dirty.

