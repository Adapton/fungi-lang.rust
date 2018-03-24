#![recursion_limit="512"]
#![doc(html_logo_url = "http://adapton.org/fungi-lang-logo/Fungi-lang-logo.png",
       html_root_url = "https://docs.rs/fungi-lang/")]

#[macro_use] extern crate adapton;

extern crate serde;
extern crate serde_json;
#[macro_use] extern crate serde_derive;

// // Source language (IODyn)
// // ------------------------
// #[macro_use] pub mod ast;
// pub mod bitype;
// pub mod prims;
// pub mod eval;

// Target language (Typed Adapton)
// --------------------------------
pub mod ast;
pub mod dynamics;
#[doc(hidden)]
#[macro_use]
pub mod parse;
pub mod normal;
pub mod subst;
pub mod expand;
pub mod bitype;
pub mod decide;
pub mod eval;
#[macro_use]
pub mod vis;
pub mod serialize;

// Note to readers: The standard library is a stale "sketch" of Fungi
// code; see `examples` modules for up-to-date examples.
#[doc(hidden)] pub mod stdlib; 

pub mod examples;

// Translation
// ------------------
// pub mod translate;
