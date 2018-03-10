# <img src="http://adapton.org/fungi-lang-logo/Fungi-lang-logo-64.png" alt="Logo" style="width: 64px;"/> Fungi: A typed functional language for programs that name their own cached dependency graphs [![Travis](https://api.travis-ci.org/Adapton/fungi-lang.rust.svg?branch=master)](https://travis-ci.org/Adapton/fungi-lang.rust)

## Fungi programs _compute incrementally_

[**Incremental
computing**](https://en.wikipedia.org/wiki/Incremental_computing)
consists of successively running a program while it computes related
outputs from related inputs that change over time.  Often, these input
changes arise from an external source, such as a human, or another
computer program.

**Fungi** provides a pair of complementary sub-languages for
expressing the interactions of incremental computations, which it
organizes into two **computation roles**:

1. The **Archivist role** computes output from input using a
   _**functional** language_, and

2. the **Editor role** uses an _**imperative** language_ to
   incrementally mutate this input over time, and change demand for
   output in the process (e.g., placing or removing focus on different
   outputs of the archivists' functions).


## Fungi programs name their (incremental) data and subcomputations

The semantics of Fungi programs are _effectful_, as they allocate
**programmer-named** values and computations, and read these objects
from memory later.  However, due to the Fungi **type and effect
system** for names, **the behavior of Fungi archivists is
functional**: the key invariant of its type-and-effects system.

In particular, Fungi provides language affordances for  
- [_first-class names_](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Val.html#variant.Name),  
- [_first class name-functions_](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Val.html#variant.NameFn),  
- nominal, incremental collections, 
  whose types are indexed by [_sets of names_](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.IdxTm.html) 
  (e.g., to uniquely name positions in a list, or elements in a set, etc.), and  
- [nominal, incremental functions over these collections](https://docs.rs/fungi-lang/0/fungi_lang/examples/index.html), 
  whose types are indexed by **read and write effects**, as name sets.  

## Fungi is a core calculus, and target language

Fungi gives a **typed**, **general-purpose core caluclus** for
**demand-driven incremental computations**, following the core calculi
and run-time semantics of [Adapton](http://adapton.org).  Unlike prior
Adapton-related projects, Fungi provides additional language
affordances for describing names, both statically and dynamically, but
especially statically, before the incremental program runs.

Fungi serves as a typed target language for
[IODyn](https://github.com/cuplv/iodyn-lang.rust).  Unlike IODyn,
which offers an **implicit** incremental language, the incremental
features of Fungi are intentionally made **explicit**.

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
