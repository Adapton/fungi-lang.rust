#[macro_use] extern crate adapton;

// Source language (IODyn)
// ------------------------
#[macro_use] pub mod ast;
pub mod bitype;
pub mod prims;
pub mod eval;

// Target language (Typed Adapton)
// --------------------------------
pub mod tgt_ast;
pub mod tgt_bitype;
pub mod tgt_eval;

// Translation
// ------------------
// pub mod translate;
