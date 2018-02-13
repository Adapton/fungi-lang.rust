# <img src="http://adapton.org/fungi-lang-logo/Fungi-lang-logo-64.png" alt="Logo" style="width: 64px;"/> Fungi: A typed functional language for programs that name their own cached dependency graphs [![Travis](https://api.travis-ci.org/Adapton/fungi-lang.rust.svg?branch=master)](https://travis-ci.org/Adapton/fungi-lang.rust)

## Fungi _computes incrementally_

[**Incremental computing**](https://en.wikipedia.org/wiki/Incremental_computing)
consists of successively re-computing related outputs from related inputs.

**Fungi** provides a pair of related, complementary sub-languages for
expressing the interactions of incremental computations, which it
organizes into a pair of complementary **computation roles**:

1. A _**functional** language_ for the **Archivist role**, and
2. An _**imperative** language_ for the **Editor role**.

The archivist role computes incremental output from input on demand,
and the editor role incrementally mutates this input over time, and
may also change demand for output in the process (e.g., placing or
removing focus on different outputs).

## Fungi programs name their (incremental) data and subcomputations

The semantics of Fungi programs are _effectful_, as they allocate
**programmer-named** values and computations, and read these objects
from memory later.  However, due to the Fungi **type and effect
system** for names, **the behavior of Fungi archivists is
functional**: the key invariant of its type-and-effects system.

In particular, Fungi provides language affordances for  
- [_first-class names_](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Val.html#variant.Name),  
- [_first class name-functions_](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Val.html#variant.NameFn),  
- [nominal, incremental collections](https://docs.rs/fungi-lang/0/fungi_lang/stdlib/index.html), 
  whose types are indexed by [_sets of names_](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.IdxTm.html) 
  (e.g., to uniquely name positions in a list, or elements in a set, etc.), and  
- [nominal, incremental functions over collections](https://docs.rs/fungi-lang/0/fungi_lang/stdlib/index.html), 
  whose types are indexed by **read and write effects**, as name sets.  

## Fungi is a core calculus, and target language

Fungi programs are demand-driven incremental computations, following
the core calculi and run-time semantics of
[Adapton](http://adapton.org).  Unlike prior Adapton-related projects,
Fungi provides affordances, in the form of a type system, for
reasoning about names statically.

Fungi serves as the target language for
[IODyn](https://github.com/cuplv/iodyn-lang.rust).  Unlike IODyn, the
incremental features of Fungi are explicit.

## Status:

 - We have implemented the [AST structure](https://docs.rs/fungi-lang/0/fungi_lang/ast/index.html).
 - We have implemented [big-step evaluation](https://docs.rs/fungi-lang/0/fungi_lang/eval/index.html).
 - Currently, we implementing a [bidirectional type system](https://docs.rs/fungi-lang/0/fungi_lang/bitype/index.html),
   and eventually, the refinement types and associated decision
   procedures.
   - For technical background and formal definitions, see the [latest draft of the technical report](https://arxiv.org/abs/1610.00097).
   - We are presently implementing these formalisms; the deductive
     proof rules for index equivalence and apartness do not indicate
     an obvious algorithm, or obvious encoding into SMT.  Creating
     these decision procedures is a key research challenge.

## Resources:

 - [Rust Implementation: Documentation](https://docs.rs/fungi-lang)  
 - [Rust Implementation: Crate](https://crates.io/crates/fungi-lang)  
 - [Visualization tools for Fungi programs](https://github.com/Adapton/fungi-vis)  


## Other links:

 - [Adapton](http://adapton.org)  
 - [IODyn](https://github.com/cuplv/iodyn-lang.rust)  
