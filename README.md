# <img src="http://adapton.org/fungi-lang-logo/Fungi-lang-logo.png" alt="Logo" style="width: 64px;"/> Fungi: A typed functional language for programs that name their own cached dependency graphs [![Travis](https://api.travis-ci.org/Adapton/fungi-lang.rust.svg?branch=master)](https://travis-ci.org/Adapton/fungi-lang.rust)

## Fungi programs are incremental computations

Fungi provides two sub-languages for expressing the interactions of
incremental computations, which it divides into two roles:

1. A _functional language_ for the **Archivist** role, and
2. An _imperative language_ for the **Editor** role.

Computation performed in the archivist role computes output from input
that the editor mutates over time.

## Fungi programs name their data and subcomputations

The semantics of Fungi programs are _effectful_, as they allocate
**programmer-named** values and computations, and read these objects from
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

 - We have implemented the AST structure, concrete syntax (via Rust macros for now); see `src/ast.rs`, and `test/ast.rs`
 - We are beginning the basic type system, and then, the refinement types and decision procedures.
 - For technical background and formal definitions, see the [latest draft of the technical report](https://arxiv.org/abs/1610.00097).
 - We are presently implementing these formalisms; the deductive proof rules for index equivalence and apartness do not indicate an obvious algorithm, or obvious encoding into SMT.  Creating these decision procedures is a key research challenge.

## Resources:

 - [Visualization tools for Fungi programs](https://github.com/Adapton/fungi-vis)

