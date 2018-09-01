# <img src="http://adapton.org/fungi-lang-logo/Fungi-lang-logo-64.png" alt="Logo" style="width: 64px;"/> Fungi: Typed incremental computation with names [![Travis](https://api.travis-ci.org/Adapton/fungi-lang.rust.svg?branch=master)](https://travis-ci.org/Adapton/fungi-lang.rust)

Fungi is a Rust-based DSL that offers a **_typed functional language_ for _incremental computation with names_**.

## [Example programs in Fungi](https://docs.rs/fungi-lang/0/fungi_lang/examples/index.html)

## Fungi Developer Resources:
 - Rust Implementation of Fungi:
    - [Documentation](https://docs.rs/fungi-lang)  
    - [Crate website](https://crates.io/crates/fungi-lang)  
 - [Visualization tools for Fungi programs](https://github.com/Adapton/fungi-vis)  

# Background

(See also: [Fungi technical report](https://arxiv.org/abs/1808.07826))

**Fungi is a typed functional language for incremental computation with names.** 

Incremental computations attempt to exploit input **similarities over
time**, reusing work that is unaffected by input changes.
To maximize this reuse in a general-purpose programming setting, 
programmers need a mechanism to identify dynamic allocations 
(of data and subcomputations) that **correspond over time**.
Fungi offers a notion of **names**, which is formal, general, and statically verifiable.

Fungi's type-and-effect system permits the programmer
to encode (program-specific) local invariants about names,
and to use these invariants to establish **global uniqueness** for their
composed programs, the property of using names correctly.
We prove (on paper) that well-typed Fungi programs respect global uniqueness.  We implement Fungi in Rust, as a "deeply-embedded" language, including Fungi's bidirectional type system and incremental evaluation semantics.

## Fungi programs _compute incrementally_

[**Incremental
computing**](https://en.wikipedia.org/wiki/Incremental_computing)
consists of successively running a program while it computes related
outputs from related inputs that change over time.  Often, these input
changes arise from an external source, such as a human, or another
computer program.

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
affordances for describing names, both dynamically, and through sound static approximations.

### Future work: Implicitly-incremental programs _translate_ to Fungi programs:

In the future, Fungi will serve as a typed target language for
[IODyn](https://github.com/cuplv/iodyn-lang.rust).  Unlike IODyn,
which offers an **implicit** incremental language, the incremental
features of Fungi are intentionally made **explicit**.

## Related Projects:

 - [Adapton](http://adapton.org) provides the semantic foundation for Fungi's approach to incremental computation.  
 - [IODyn](https://github.com/cuplv/iodyn-lang.rust) is an implicitly-incremental language, targetting Fungi via a type-directed translation  
