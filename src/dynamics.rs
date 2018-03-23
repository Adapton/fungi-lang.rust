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

/// Run-time values. Compare to [ast::Val](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Val.html).
///
/// Same as [Val](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Val.html),
/// except that these values are (1) closed and (2) may contain run
/// time-only structures, from the Adapton entine:
///
/// - there are no variables ("closed") and
///
/// - unlike values written by user in their program, run-time values
/// may contain run-time structures, such as _actual_ thunks and
/// references, a la `Art`s from Adapton library.
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum RtVal {
    /// Unit value
    Unit,
    /// Pair of run-time values
    Pair(RtValRec, RtValRec),
    /// First injection of run-time value
    Inj1(RtValRec),
    /// Second injection of run-time value
    Inj2(RtValRec),
    /// Rolled run-time value (with a recursive type)
    Roll(RtValRec),
    /// Dynamic name term
    NameFn(NameTm),
    /// Natural number
    Nat(usize),
    /// String
    Str(String),
    /// Boolean
    Bool(bool),    
    /// Special-case thunk values: For implementing `fix` with environment-passing style
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
    /// Lambda expression, with a closing environment
    Lam(Env, Var, Rc<Exp>),
    /// Rust-level lambda function, with Fungi-level argument values
    HostFn(HostEvalFn, Vec<RtVal>),
    /// Produce the given run-time value
    Ret(RtVal),
}

/// Name Term Values.  The value forms (name and lambda) for the Name
/// Term sub-language (STLC + names).
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum NameTmVal {
    /// (Closed) name term
    Name(Name),
    /// (Closed) name function
    Lam(Var,NameTm),
}
