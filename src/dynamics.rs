/*! Syntax for dynamic, evaluation-time structures.

Syntax that is not statically written in the program by the
programmer, but arises dynamically, from running programs.  

We separate these structures into a module in order to import it
elsewhere, without importing other aspects of the evaluation
semantics.  For practical reasons, these AST structures still must be
mentioned in the static structure.  Namely, the `Exp::HostEval` form
holds a function over these types, providing a "trapdoor" for
libraries to extend the core evaluation rules below with custom ones
(e.g., for standard library primitives, such as vectors).

*/
use ast::*;
use adapton::engine;
use std::rc::Rc;

/// TODO-Sometime: Prune the environments (using free variables as filters)
pub type Env = Vec<(String,RtVal)>;

/// Run-time values.  Same as ast_tgt::Val, except that (1) there are
/// no variables ("closed") and (2) unlike values written by user in
/// their program, run-time values may contain run-time structures,
/// such as _actual_ thunks and references, a la `Art`s from Adapton
/// library.
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum RtVal {
    Unit,
    Pair(RtValRec, RtValRec),
    Inj1(RtValRec),
    Inj2(RtValRec),
    Roll(RtValRec),
    NameFn(NameTm),
    
    Nat(usize),
    Str(String),
    Bool(bool),
    
    /// Special-case thunk values: For implementing fix with environment-passing style
    ThunkAnon(Env, Exp),
    
    /// AST Names; we convert to Adapton engine names when we use the engine API
    Name(Name),
    
    /// Refs from Adapton engine; they each contain a run-time value
    Ref(engine::Art<RtVal>),
    
    /// Thunks from Adapton engine; they each _evaluate to_ a terminal expression
    Thunk(engine::Art<ExpTerm>),
}

pub type RtValRec = Rc<RtVal>;

/// Terminal expressions (a la CBPV), but in environment-passing
/// style, where lambdas are associatd with closing environments.
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ExpTerm {
    Lam(Env, Var, Rc<Exp>),
    HostFn(HostEvalFn, Vec<RtVal>),
    Ret(RtVal),
}

/// Name Term Values.  The value forms (name and lambda) for the Name
/// Term sub-language (STLC + names).
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum NameTmVal {
    Name(Name),
    Lam(Var,NameTm),
}
