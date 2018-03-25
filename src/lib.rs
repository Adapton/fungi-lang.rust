/*! **Fungi language:** *reference implementation in Rust.*
 
See also:
[example Fungi programs](https://docs.rs/fungi-lang/0.1.43/fungi_lang/examples/index.html)
in this Rust implementation.

# Syntax

Fungi's 
[abstract syntax](https://docs.rs/fungi-lang/0/fungi_lang/ast/index.html) 
consists of Rust data types; we implement
its 
[concrete syntax](https://docs.rs/fungi-lang/0/fungi_lang/parse/index.html) 
with Rust macros:

 - [`ast`](https://docs.rs/fungi-lang/0/fungi_lang/ast/index.html)
--- Abstract syntax (Rust datatypes)
 - [`parse`](https://docs.rs/fungi-lang/0/fungi_lang/parse/index.html)
--- Concrete syntax (Rust macros)

(See [examples](https://docs.rs/fungi-lang/0.1.43/fungi_lang/examples/index.html))

# Statics

Fungi's statics relate Fungi programs with their types and effects.

To accomplish this, Fungi gives a "type-level" semantics for relating
types, and their index- and name terms.
Specifically, this theory includes various supportive notions:  
 - [`expand`](https://docs.rs/fungi-lang/0/fungi_lang/expand/index.html)
--- expand type-level definitions,
 - [`subst`](https://docs.rs/fungi-lang/0/fungi_lang/subst/index.html)
--- perform type-level variable substitution, 
 - [`normal`](https://docs.rs/fungi-lang/0/fungi_lang/normal/index.html)
--- perform type-level term normalization,
 - [`decide`](https://docs.rs/fungi-lang/0/fungi_lang/decide/index.html)
--- decide relationships about types, and about type indices.
   - [`equiv`](https://docs.rs/fungi-lang/0/fungi_lang/decide/equiv/index.html) -- decides term _equivalence_ relationships
   - [`apart`](https://docs.rs/fungi-lang/0/fungi_lang/decide/apart/index.html) -- decides term _apartness_ relationships
   - [`subset`](https://docs.rs/fungi-lang/0/fungi_lang/decide/subset/index.html) -- decide name _subsets_, and _subtyping_ relationships
   - [`effect`](https://docs.rs/fungi-lang/0/fungi_lang/decide/effect/index.html) -- decide _effect sequencing_ and _subtracting_ relationships
  
These notions are each in support of  
 - [`bitype`](https://docs.rs/fungi-lang/0/fungi_lang/bitype/index.html)
--- bi-directional type checking for program terms (expressions and values).

In particular, the `bitype` module synthesizes and checks the types of
Fungi program terms, and thus provides the most common "entry points"
into the implementation of Fungi's statics.

# Dynamics

Fungi's dynamics execute Fungi programs, under varying notions of execution.

Fungi's program executions use [Adapton in
Rust](http://github.com/Adapton/adapton.rust). 
We define two 
reference implementations for Fungi's dynamics: 
[_small-step reduction_](https://docs.rs/fungi-lang/0/fungi_lang/reduce/index.html),
and 
[_big-step evaluation_](https://docs.rs/fungi-lang/0/fungi_lang/eval/index.html):

- [`reduce`](https://docs.rs/fungi-lang/0/fungi_lang/reduce/index.html)
-- program dynamics as _small-step reduction_
- [`eval`](https://docs.rs/fungi-lang/0/fungi_lang/eval/index.html)
-- program dynamics as _big-step evaluation_

These approaches have many [_common definitions_](https://docs.rs/fungi-lang/0/fungi_lang/dynamics/index.html):

- [`dynamics`](https://docs.rs/fungi-lang/0/fungi_lang/dynamics/index.html)
-- common definitions: name term evaluation, run-time values, and environments.

## Dynamics: practicum

_Summary_: Use program _reduction_ (_not_ evaluation) in all practical
settings.

For the sake of completeness, we provide two execution definitions.
However, the implementation of [small-step
reduction](https://docs.rs/fungi-lang/0/fungi_lang/reduce/index.html)
is _significantly_ more practical than the version of [big-step
evaluation](https://docs.rs/fungi-lang/0/fungi_lang/eval/index.html) given here.

In particular, program _reduction_ avoids using (Rust-level) stack
space, whereas the simple evaluation definition here uses the
(Rust-level) stack space in proportion to the depth of the full
evaluation derivation.  These derivations can be _deep_ for recursive,
looping programs, where their depth is often the same, asymptotically,
as their running time. On the other hand, this definition of
evaluation is simple, and easy to read and understand --- the goal of
its reference implementation; readers are encouraged to 
[read it](https://docs.rs/fungi-lang/0/fungi_lang/eval/index.html), _not_ run it (except for very small programs).

*/
#![recursion_limit="512"]
#![doc(html_logo_url = "http://adapton.org/fungi-lang-logo/Fungi-lang-logo.png",
       html_root_url = "https://docs.rs/fungi-lang/")]

#[macro_use] extern crate adapton;


// === Syntax ===
//
pub mod ast;
//#[doc(hidden)]
#[macro_use]
pub mod parse;

// == Statics ===
//
pub mod subst;
pub mod expand;
pub mod normal;
pub mod decide;
pub mod bitype;

// === Dynamics ====
// 
pub mod dynamics;
pub mod eval;
pub mod reduce;

// === Debugging/Instrumentation/Visualization ====
// 
#[macro_use]
pub mod vis;

// Note to readers: The standard library is a stale "sketch" of Fungi
// code; see `examples` modules for up-to-date examples.
#[doc(hidden)] pub mod stdlib; 

pub mod examples;

// Translation
// ------------------
// pub mod translate;
