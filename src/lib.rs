/*! **Fungi language:** *reference implementation in Rust.*

# Syntax

Fungi's [abstract syntax](XXX) consists of Rust data types; we implement
its [concrete syntax](XXX) with Rust macros:

 - `ast`   --- Abstract syntax (Rust datatypes)
 - `parse` --- Concrete syntax (Rust macros)

# Statics

Fungi's statics relate Fungi programs with their types and effects.

To accomplish this, Fungi gives a "type-level" semantics for relating
types, and their index- and name terms.
Specifically, this theory includes various supportive components:  
 - `subst`  --- type-level variable substitution, 
 - `expand` --- expansion of type-level definitions,
 - `normal` --- type-level term normalization,
 - `decide` --- decision procedures for relating types and type indices,  
  
These notions are each in support of  
 - `bitype` --- bi-directional type checking for program terms (expressions and values).

In particular, the `bitype` module synthesizes and checks the types of
Fungi program terms, and thus provides the most common "entry points"
into the implementation of Fungi's statics.

# Dynamics

TODO

*/
#![recursion_limit="512"]
#![doc(html_logo_url = "http://adapton.org/fungi-lang-logo/Fungi-lang-logo.png",
       html_root_url = "https://docs.rs/fungi-lang/")]

#[macro_use] extern crate adapton;


// === Syntax ===
//
pub mod ast;
#[doc(hidden)]
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
