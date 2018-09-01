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

## Related Projects:

 - [Adapton](http://adapton.org) provides the semantic foundation for Fungi's approach to incremental computation.  
 - [IODyn](https://github.com/cuplv/iodyn-lang.rust) is an implicitly-incremental language, targetting Fungi via a type-directed translation
