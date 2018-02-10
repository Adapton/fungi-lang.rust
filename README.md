# Fungi: A typed functional language for programs that name their own cached dependency graphs [![Travis](https://api.travis-ci.org/Adapton/fungi-lang.rust.svg?branch=master)](https://travis-ci.org/Adapton/fungi-lang.rust)

Fungi serves as the target language for [IODyn](https://github.com/cuplv/iodyn-lang.rust).  Unlike IODyn, the incremental features of Fungi are explicit.  In particular, Fungi provides language affordances for
 - _first-class names_, 
 - _first class name-functions_, 
 - input/output collections whose types are indexed by _sets of names_ (e.g., to uniquely identify positions in a list), and 
 - functions whose types are indexed by what cached data and computations they read and write.
 Though the semantics of Fungi are effectful, wherein it allocates programmer-named values and computations, and reads these objects from memory later, **the behavior of Fungi is functional**: the key invariant of its type-and-effects system.
 
 More precisely, Fungi provides two languages: One for the **Archivist** (the functional subset), and an imperative "wrapper" language for the **Editor**, who is permitted to mutate the Archivist's input, and then indicate where the output of archivist computations should be incrementally repaired, on demand.

## (Status:)

 - We have implemented the AST structure, concrete syntax (via Rust macros for now); see `src/ast.rs`, and `test/ast.rs`
 - We are beginning the basic type system, and then, the refinement types and decision procedures.
 - For technical background and formal definitions, see the [latest draft of the technical report](https://arxiv.org/abs/1610.00097).
 - We are presently implementing these formalisms; the deductive proof rules for index equivalence and apartness do not indicate an obvious algorithm, or obvious encoding into SMT.  Creating these decision procedures is a key research challenge.
