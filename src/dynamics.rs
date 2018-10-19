/*! Syntax for dynamic, evaluation-time structures.

Notably, some of these syntantic forms are absent from programs
written by the programmer; rather, they only arise _dynamically_, from
_running_ these programs, and in some cases, by using Adapton engine.

However, since they are common to multiple operational semantics
(`eval` and `reduce`), we separate these dynamic structures from any
one particular evaluation semantics.

For practical reasons, these AST structures still must be mentioned in
the static structure.  Namely, the `Exp::HostEval` form holds a
function over these types, providing a "trapdoor" for libraries to
extend the core evaluation rules below with custom ones (e.g., for
standard library primitives, such as vectors).
See also: The [ExpTerm](https://docs.rs/fungi-lang/0/fungi_lang/dynamics/enum.ExpTerm.html) type.

*/
use crate::shared::Shared;
use crate::ast::*;
use adapton::engine;
// use serialize::ArtDef;

use std::rc::Rc;

//use serde::Serialize;

/// TODO-Sometime: Prune the environments (using free variables as filters)
#[derive(Clone,Eq,PartialEq,Hash,Debug,Serialize)]
pub enum Env {
    Empty,
    Cons(Var,RtVal,EnvRec)
}
#[derive(Clone,Eq,PartialEq,Hash,Serialize)]
//pub struct EnvRec { rec:Rc<Env> }
pub struct EnvRec { rec:Shared<Env> }

pub fn env_emp() -> EnvRec {
    EnvRec{rec:Shared::new(Env::Empty)}
}

pub fn env_find(env:&EnvRec, x:&Var) -> Option<RtVal> {
    match *env.rec {
        Env::Empty => None,
        Env::Cons(ref y, ref v, ref env) => {
            if x == y {
                return Some(v.clone())
            } else {
                return env_find(&*env, x)
            }
        }
    }
}

pub fn env_push(env:&EnvRec, x:&Var, v:RtVal) -> EnvRec {
    EnvRec{rec:Shared::new(Env::Cons(x.clone(), v, env.clone()))}
}

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
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
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
    ThunkAnon(EnvRec, Exp),
    /// AST Names; we convert to Adapton engine names when we use the engine API
    Name(Name),
    /// Refs from Adapton engine; they each contain a run-time value
    #[serde(skip_serializing)] // #[serde(with="ArtDef")]
    Ref(Ref),
    /// Thunks from Adapton engine; they each _evaluate to_ a terminal expression
    #[serde(skip_serializing)] // #[serde(with="ArtDef")]
    Thunk(Thk),
    /// Existential packings; at run-time, we forget the choice of indices
    Pack(RtValRec),
    /// "Host objects": native Rust objects
    #[serde(skip_serializing)] // #[serde(with="ArtDef")]
    HostObj(HostObj),
}
/// Run-time values
pub type RtValRec = Rc<RtVal>;

/// The Rust type of all Fungi references
pub type Ref = engine::Art<RtVal>;

/// The Rust type of all Fungi thunks
pub type Thk = engine::Art<ExpTerm>;

/// Terminal expressions (a la CBPV), but in environment-passing
/// style, where (closed) lambda terms have closing environments.
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum ExpTerm {
    /// Lambda expression, with a closing environment
    Lam(EnvRec, Var, Rc<Exp>),
    /// Rust-level lambda function, with Fungi-level argument values
    HostFn(HostEvalFn, Vec<RtVal>),
    /// Produce the given run-time value
    Ret(RtVal),
}

/// Wrapper for `Ret` constructor.
pub fn ret(v:RtVal) -> ExpTerm {
    ExpTerm::Ret(v)
}

/// Name Term Values.  The value forms (name and lambda) for the Name
/// Term sub-language (STLC + names).
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum NameTmVal {
    /// (Closed) name term
    Name(Name),
    /// (Closed) name function
    Lam(Var,NameTm),
}

/// project/pattern-match the name of namespace, defined as the
/// sub-term `M` in the following nameterm (lambda) form:
///
/// ```text
///  #x:Nm. M * x
/// ```
///
/// where `M * x` is the binary name formed from uknown name `x` and
/// `M`, the name of the "namespace".
///
pub fn proj_namespace_name(n:NameTmVal) -> Option<NameTm> {
    match n {
        NameTmVal::Name(_) => None,
        NameTmVal::Lam(x,m) => {
            match m {
                NameTm::Bin(m1, m2) => {
                    match (*m2).clone() {
                        NameTm::Var(y) => {
                            if x == y { Some((*m1).clone()) }
                            else { None }
                        }
                        _ => None,
                    }
                },
                _ => None,
            }
        },
    }
}

/// Convert a name term value back into (the same) name term
pub fn nametm_of_nametmval(v:NameTmVal) -> NameTm {
    use crate::ast::Sort;
    match v {
        NameTmVal::Name(n)  => NameTm::Name(n),
        // eval doesn't use sorts, unit is fine
        NameTmVal::Lam(x,m) => NameTm::Lam(x,Sort::Unit,Rc::new(m))
    }
}

/// Substitute a name term value for a free variable in another term
pub fn nametm_subst_rec(nmtm:Rc<NameTm>, x:&Var, v:&NameTm) -> Rc<NameTm> {
    Rc::new(nametm_subst((*nmtm).clone(), x, v))
}
/// Substitute a name term value for a free variable in another term
pub fn nametm_subst(nmtm:NameTm, x:&Var, v:&NameTm) -> NameTm {
    match nmtm {
        NameTm::Name(n) => NameTm::Name(n),
        NameTm::WriteScope => NameTm::WriteScope,
        NameTm::Bin(nt1, nt2) => {
            NameTm::Bin(nametm_subst_rec(nt1, x, v),
                        nametm_subst_rec(nt2, x, v))
        }
        NameTm::App(nt1, nt2) => {
            NameTm::App(nametm_subst_rec(nt1, x, v),
                        nametm_subst_rec(nt2, x, v))
        }
        NameTm::ValVar(x) => {
            panic!("Unexpected value variable: {}", x)
        }
        NameTm::Var(y) => {
            if *x == y { v.clone() }
            else { NameTm::Var(y) }
        }
        NameTm::Lam(y,s,nt) => {
            if *x == y { NameTm::Lam(y,s,nt) }
            else { NameTm::Lam(y, s, nametm_subst_rec(nt, x, v)) }
        }
        NameTm::NoParse(_) => unreachable!(),
        NameTm::Ident(_) => unreachable!(),
    }
}

/// Evaluate a name term, dynamically (see also: `normal` module)
pub fn nametm_eval_rec(nmtm:Rc<NameTm>) -> NameTmVal {
    nametm_eval((*nmtm).clone())
}

/// Evaluate a name term, dynamically (see also: `normal` module)
pub fn nametm_eval(nmtm:NameTm) -> NameTmVal {
    match nmtm {
        NameTm::Var(x) => { panic!("dynamic type error (open term, with free var {})", x) }
        NameTm::ValVar(x) => { panic!("dynamic type error (open term, with free (value) var {})", x) }
        NameTm::Name(n) => NameTmVal::Name(n),
        NameTm::Lam(x, _, nt) => NameTmVal::Lam(x, (*nt).clone()),
        NameTm::WriteScope => unimplemented!("write scope"),
        NameTm::Bin(nt1, nt2) => {
            let nt1 = nametm_eval_rec(nt1);
            let nt2 = nametm_eval_rec(nt2);
            match (nt1, nt2) {
                (NameTmVal::Name(n1),
                 NameTmVal::Name(n2)) => {
                    NameTmVal::Name(Name::Bin(Rc::new(n1), Rc::new(n2)))
                },
                _ => { panic!("dynamic type error (bin name term)") }
            }
        }
        NameTm::App(nt1, nt2) => {
            let nt1 = nametm_eval_rec(nt1);
            let nt2 = nametm_eval_rec(nt2);
            match nt1 {
                NameTmVal::Lam(x, nt3) => {
                    let ntv = nametm_of_nametmval(nt2);
                    let nt4 = nametm_subst(nt3, &x, &ntv);
                    nametm_eval(nt4)
                },
                _ => { panic!("dynamic type error (bin name term)") }
            }
        }
        NameTm::NoParse(_) => unreachable!(),
        NameTm::Ident(_) => unreachable!(),
    }
}

/// Name conversion. Convert an `ast` name into a run-time (adapton
/// library) name.
pub fn engine_name_of_ast_name(n:Name) -> engine::Name {
    match n {
        Name::Leaf   => engine::name_unit(),
        Name::Sym(s) => engine::name_of_string(s),
        Name::Num(n) => engine::name_of_usize(n),
        Name::Bin(n1, n2) => {
            let en1 = engine_name_of_ast_name((*n1).clone());
            let en2 = engine_name_of_ast_name((*n2).clone());
            engine::name_pair(en1,en2)
        }
        Name::NoParse(_) => unimplemented!()
    }
}

/// Given a closing environment and an `ast` value (with zero or
/// more variables) producing a closed, run-time value.
///
/// panics if the environment fails to close the given value's
/// variables.
pub fn close_val(env:&EnvRec, v:&Val) -> RtVal {
    use crate::ast::Val::*;
    match *v {
        HostObj(ref o) => RtVal::HostObj(o.clone()),
        
        // variable case:
        Var(ref x) => {
            match env_find(env, x) {
                None => panic!("close_val: free variable: {}\n\tenv:{:?}", x, env),
                Some(v) => v
            }
        }
        // other cases: base cases, and structural recursion:
        Name(ref n)    => RtVal::Name(n.clone()),

        // XXX/TODO --- Descend into name terms and continue substitution...?
        // OR -- Do we have an invariant that these terms are closed?
        NameFn(ref nf) => RtVal::NameFn(nf.clone()), 
        
        Unit         => RtVal::Unit,
        Bool(ref b)  => RtVal::Bool(b.clone()),
        Nat(ref n)   => RtVal::Nat(n.clone()),
        Str(ref s)   => RtVal::Str(s.clone()),

        // anonymous thunk case: clone and save the environment (and exp):
        ThunkAnon(ref e) => RtVal::ThunkAnon(env.clone(), (**e).clone()),

        // inductive cases
        Inj1(ref v1) => RtVal::Inj1(close_val_rec(env, v1)),
        Inj2(ref v1) => RtVal::Inj2(close_val_rec(env, v1)),
        Roll(ref v1) => RtVal::Roll(close_val_rec(env, v1)),
        Pack(ref _a, ref v) => 
            RtVal::Pack(close_val_rec(env, v)),
        Pair(ref v1, ref v2) =>
            RtVal::Pair(close_val_rec(env, v1),
                        close_val_rec(env, v2)),
        // Forget annotation
        Anno(ref v,_) => close_val(env, v),
        NoParse(ref s) => unreachable!("closing value consists of unparsed text: `{}`", s),

    }
}

/// See `close_val`
pub fn close_val_rec(env:&EnvRec, v:&Rc<Val>) -> Rc<RtVal> {
    Rc::new(close_val(env, &**v))
}

///////////////////////////////////////////////////
use std::fmt;
use std::env as std_env;

thread_local!(static FUNGI_VERBOSE_ENVREC:
              bool =
              match std_env::var("FUNGI_VERBOSE_ENVREC") {
                  Ok(ref s) if s == "1" => true,
                  _ => false
              });

impl fmt::Debug for EnvRec {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        FUNGI_VERBOSE_ENVREC.with(|b| {
            if *b {
                // use the verbose (default, derived) formatter
                self.rec.fmt(f)
            } else {                
                // do not recur; save space/time
                write!(f, "...")
            }
        })
    }
}
