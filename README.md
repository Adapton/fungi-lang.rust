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

 - [Example programs in Fungi](https://docs.rs/fungi-lang/0/fungi_lang/examples/index.html).
   - We have implemented a prototype of the [bidirectional type system](https://docs.rs/fungi-lang/0/fungi_lang/bitype/index.html),
     including the refinement types and associated [decision procedures for effects](https://docs.rs/fungi-lang/0/fungi_lang/decide/effect/index.html).
   - For technical background and formal definitions, see the [latest draft of the technical report](https://arxiv.org/abs/1610.00097).

## Fungi Resources:

 - Rust Implementation of Fungi:
    - [Documentation](https://docs.rs/fungi-lang)  
    - [Crate website](https://crates.io/crates/fungi-lang)  
 - [Visualization tools for Fungi programs](https://github.com/Adapton/fungi-vis)  

## Related Resources:

 - [Adapton](http://adapton.org) provides the semantic foundation for Fungi's approach to incremental computation.  
 - [IODyn](https://github.com/cuplv/iodyn-lang.rust) is an implicitly-incremental language, targetting Fungi via a type-directed translation  
