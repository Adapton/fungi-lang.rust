#![recursion_limit="512"]
#![doc(html_logo_url = "http://adapton.org/fungi-lang-logo/Fungi-lang-logo.png",
       html_root_url = "https://docs.rs/fungi-lang/")]

#[macro_use] extern crate adapton;

// // Source language (IODyn)
// // ------------------------
// #[macro_use] pub mod ast;
// pub mod bitype;
// pub mod prims;
// pub mod eval;

// Target language (Typed Adapton)
// --------------------------------
pub mod ast;
#[doc(hidden)]
#[macro_use]
pub mod parse;
pub mod normal;
pub mod subst;
pub mod bitype;
pub mod decide;
pub mod eval;
pub mod vis;
pub mod stdlib;

// Translation
// ------------------
// pub mod translate;
