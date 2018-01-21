//! Big-step evaluation semantics for IODyn Target AST, via Adapton in
//! Rust.
//!
//! Gives the incremental semantics of programs, using an external
//! library (Adapton in Rust) to create and maintain the DCG.
//!
//! ## Design discussion
//!
//! The Rust types and functions below demonstrate how closely the
//! IODyn Target AST corresponds to the primitive notions of Adapton,
//! namely refs, thunks and their operations get and force,
//! respectively.
//!
//! In particular, the semantics of `ref` and `thunk` are _entirely_
//! encapsiluated by the Adapton run-time library, leaving the
//! dynamics semantics for other expression forms to `eval` to define.
//!
//! In some sense, the language built around the `ref` and `thunk`
//! primitives is somewhat arbitrary; given this choice, we choose
//! CBPV STLC with products and sums, as usual.  Other choices are
//! guided by our choice of "CBPV + environment-passing-style", as
//! discussed further in this module's comments.
//!
//! ## Val vs RtVal
//!
//! We distinguish between programmer-written values (Val) and closed,
//! run-time values (RtVal).  Environments map variables to (closed)
//! run-time values.
//!
//! ## Exp vs TermExp
//!
//! We distinguish between (open) expressions and (fully evaluated)
//! terminal expressions, which are closed.

use adapton::macros::*;
use adapton::engine;
use adapton::engine::{thunk,cell,force,ArtIdChoice};

use ast::{Var};
use tgt_ast::{Exp,Val,Name,NameTm};
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
    Nat(usize),
    Str(String),
    Unit,
    Pair(RtValRec, RtValRec),
    Inj1(RtValRec),
    Inj2(RtValRec),
    NameFn(NameTm),

    // Special-case thunk values: For implementing fix with environment-passing style
    FixThunk(Env, Exp),
    
    // Name, Ref, Thunk: Run-time objects from Adapton library (names, refs, thunks):

    // Names from Adapton engine
    Name(engine::Name),
    // Refs from Adapton engine; they each contain a run-time value
    Ref(engine::Art<RtVal>),
    // Thunks from Adapton engine; they each _evaluate to_ a terminal expression
    Thunk(engine::Art<ExpTerm>),
}
pub type RtValRec = Rc<RtVal>;

/// Terminal expressions (a la CBPV), but in environment-passing
/// style, where lambdas are associatd with closing environments.
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ExpTerm {
    Lam(Env, Var, Rc<Exp>),
    Ret(RtVal),
}

/// Name conversion. Convert Tgt-AST name into a run-time (adapton
/// library) name.
fn name_of_name(_n:&Name) -> engine::Name {
    panic!("")
}

/// Given a closing environment and an Tgt-AST value (with zero or
/// more variables) producing a closed, run-time value.
///
/// panics if the environment fails to close the given value's
/// variables.
fn close_val(env:&Env, v:&Val) -> RtVal {
    use tgt_ast::Val::*;
    match *v {
        // variable case:
        Var(ref _x)   => //env.get(x).unwrap().clone(),
            panic!("TODO"),
        
        // other cases: base cases, and structural recursion:
        Name(ref n)    => RtVal::Name(name_of_name(n)),
        NameFn(ref nf) => RtVal::NameFn(nf.clone()), // XXX/TODO --- Descend into name terms and continue substitution...?
        
        Unit         => RtVal::Unit,
        Nat(ref n)   => RtVal::Nat(n.clone()),
        Str(ref s)   => RtVal::Str(s.clone()),

        // These shouldn't happen; they are really run-time values!
        Ref(ref _p)   => unreachable!(),
        Thunk(ref _p) => unreachable!(),

        // inductive cases
        Inj1(ref v1) => RtVal::Inj1(close_val_rec(env, v1)),
        Inj2(ref v1) => RtVal::Inj2(close_val_rec(env, v1)),
        Pair(ref v1, ref v2) =>
            RtVal::Pair(close_val_rec(env, v1),
                        close_val_rec(env, v2)),
        // Forget annotation
        Anno(ref v,_) => close_val(env, v),
    }
}

fn close_val_rec(env:&Env, v:&Rc<Val>) -> Rc<RtVal> {
    Rc::new(close_val(env, &**v))
}

/// Dynamic type errors ("stuck cases" for evaluation)
///
/// For each place in the `eval` function where a dynamic type error
/// may arise that prevents us from progressing, we give a constructor
/// with the relevant information (first for documentation purposes,
/// and secondly for future error messages).
#[derive(Clone,Debug,Eq,PartialEq)]
pub enum EvalTyErr {
    // let case
    LetNonRet(ExpTerm),
    // app case
    AppNonLam(ExpTerm),
    // split case
    SplitNonPair(RtVal),
    // if case
    IfNonBool(RtVal),
    // case case
    CaseNonInj(RtVal),
    // thunk case
    ThunkNonName(RtVal),
    ForceNonThunk(RtVal),
    // ref case
    RefNonName(RtVal),
    GetNonRef(RtVal),
}

fn eval_type_error<A>(err:EvalTyErr, env:Env, e:Exp) -> A {
    panic!("eval_type_error: {:?}:\n\tenv:{:?}\n\te:{:?}\n", err, env, e)
}

/// Big-step evaluation
///
/// Under the given closing environment, evaluate the given Tgt-AST
/// expression, producing a terminal expression (a la CBPV), typically
/// with run-time values.
///
/// Adapton primitives: The primitives `thunk`, `ref`, `force` and
/// `get` each use the Adapton run-time library in a simple way that
/// directly corresponds with the given expression form.
///
/// CPBV consequences: Due to CBPV style, most cases are simple (0 or
/// 1 recursive calls).  The only two cases that have multiple
/// recursive calls are `let` and `app`, which necessarily each have
/// two recursive calls to `eval`. In CBV style, many more cases would
/// require multiple recursive calls to eval.
///
pub fn eval(mut env:Env, e:Exp) -> ExpTerm {
    match e.clone() {       
        Exp::Lam(x, e)    => { ExpTerm::Lam(env, x, e) }
        Exp::Ret(v)       => { ExpTerm::Ret(close_val(&env, &v)) }
        Exp::Anno(e1,_ct) => { eval(env, (*e1).clone()) }
        Exp::Fix(f,e1) => {
            let env_saved = env.clone();
            env.push((f, RtVal::FixThunk(env_saved, (*e).clone())));
            eval(env, (*e1).clone())
        }
        Exp::Thunk(v, e1) => {
            match close_val(&env, &v) {
                RtVal::Name(n) => {
                    let t = thunk!([Some(n)]? eval ; env:env, e:(*e1).clone() );
                    ExpTerm::Ret(RtVal::Thunk(t))
                },
                v => eval_type_error(EvalTyErr::ThunkNonName(v), env, e)
            }
        }
        Exp::Ref(v1, v2) => {
            match close_val(&env, &v1) {
                RtVal::Name(n) => {
                    let v2 = close_val(&env, &v2);
                    let r = cell(n, v2);
                    ExpTerm::Ret(RtVal::Ref(r))
                },
                v => eval_type_error(EvalTyErr::RefNonName(v), env, e)
            }
        }
        Exp::Let(x,e1,e2) => {
            match eval(env.clone(), (*e1).clone()) {
                ExpTerm::Ret(v) => {
                    env.push((x, v));
                    eval(env, (*e2).clone())
                },
                term => eval_type_error(EvalTyErr::LetNonRet(term), env, e)
            }
        }
        Exp::App(e1, v) => {
            match eval(env.clone(), (*e1).clone()) {
                ExpTerm::Lam(mut env, x, e2) => {
                    let v = close_val(&env, &v);
                    env.push((x, v));
                    eval(env, (*e2).clone())
                },
                term => eval_type_error(EvalTyErr::AppNonLam(term), env, e)
            }
        }
        Exp::Split(v, x, y, e1) => {
            match close_val(&env, &v) {
                RtVal::Pair(v1, v2) => {
                    env.push((x, (*v1).clone()));
                    env.push((y, (*v2).clone()));
                    eval(env, (*e1).clone())
                },
                v => eval_type_error(EvalTyErr::SplitNonPair(v), env, e)
            }
        }
        Exp::Case(v, x, ex, y, ey) => {
            match close_val(&env, &v) {
                RtVal::Inj1(v) => {
                    env.push((x, (*v).clone()));
                    eval(env, (*ex).clone())
                },
                RtVal::Inj2(v) => {
                    env.push((y, (*v).clone()));
                    eval(env, (*ey).clone())
                },
                v => eval_type_error(EvalTyErr::SplitNonPair(v), env, e)
            }
        }
        Exp::Get(v) => {
            match close_val(&env, &v) {
                RtVal::Ref(a) => { ExpTerm::Ret(get!(a)) },
                v => eval_type_error(EvalTyErr::GetNonRef(v), env, e)
            }
        }
        Exp::Force(v) => {
            match close_val(&env, &v) {
                RtVal::Thunk(a)         => { force(&a) },
                RtVal::FixThunk(env, e) => { eval(env, e) },
                v => eval_type_error(EvalTyErr::ForceNonThunk(v), env, e)                    
            }
        }
        Exp::Scope(_v, _e) => {
            panic!("")
        }
        Exp::NameApp(_, _) => {
            panic!("")
        }
        Exp::DebugLabel(_,e) => {
            // XXX/TODO -- Insert label/text/message into Adapton's trace structure
            return eval(env, (*e).clone())
        }
        Exp::Unimp => unimplemented!(),
    }
}
