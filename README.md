# Fungi: A typed functional language for programs that name their own cached dependency graphs [![Travis](https://api.travis-ci.org/Adapton/fungi-lang.rust.svg?branch=master)](https://travis-ci.org/Adapton/fungi-lang.rust)

Fungi provides two languages: A functional language for the
**Archivist**, and an imperative language for the **Editor**, who is
permitted to mutate the Archivist's input, and then indicate where the
output of archivist computations should be incrementally repaired, on
demand.

The semantics of Fungi programs are _effectful_, as they allocate
programmer-named values and computations, and read these objects from
memory later.  However, due to Fungi's type and effect system for
names, **the behavior of Fungi archivists is functional**: the key
invariant of its type-and-effects system.

In particular, Fungi provides language affordances for
 - _first-class names_, 
 - _first class name-functions_, 
 - input/output collections whose types are indexed by _sets of names_ (e.g., to uniquely identify positions in a list), and 
 - functions whose types are indexed by what cached data and computations they read and write.

## Fungi is a core calculus, and target language

Fungi serves as the target language for [IODyn](https://github.com/cuplv/iodyn-lang.rust).  Unlike IODyn, the incremental features of Fungi are explicit.

## Status:

 - We have implemented the AST structure, concrete syntax (via Rust macros for now); see `src/tgt_ast.rs`, and `test/tgt_ast.rs`
 - We are beginning the basic type system, and then, the refinement types and decision procedures.
 - For technical background and formal definitions, see the [latest draft of the technical report](https://arxiv.org/abs/1610.00097).
 - We are presently implementing these formalisms; the deductive proof rules for index equivalence and apartness do not indicate an obvious algorithm, or obvious encoding into SMT.  Creating these decision procedures is a key research challenge.

## Resources:

 - [Visualization tools for Fungi programs](https://github.com/Adapton/fungi-vis)

