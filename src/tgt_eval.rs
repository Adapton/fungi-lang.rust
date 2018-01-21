//! Big-step reference evaluation semantics, for IODyn Target AST.
//!
//! Gives the incremental semantics of programs, using an external
//! library (Adapton in Rust) to create and maintain the DCG.

use adapton::macros::*;
use adapton::engine;
use adapton::engine::{thunk,cell,force,ArtIdChoice};

use ast::{Var};
use tgt_ast::{Exp,Val,Name,NameTm};
use std::rc::Rc;

/// TODO-Sometime: Prune the environments (using free variables as filters)
pub type Env = Vec<(String,RtVal)>;

/// Run-time values: Closed (no variables); and, may contain run-time
/// structures (e.g., `Art`s from Adapton library).
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
    
    // Run-time objects from Adapton library (names, refs, thunks):
    Name(engine::Name),
    Ref(engine::Art<RtVal>),
    Thunk(engine::Art<ExpTerm>),
}
pub type RtValRec = Rc<RtVal>;

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ExpTerm {
    Lam(Env, Var, Rc<Exp>),
    Ret(RtVal),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct State {
    next_name:usize
}

fn name_of_name(_n:&Name) -> engine::Name {
    panic!("")
}

// panics if the environment fails to close the given value's variables
/// Substitution on all values
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

fn eval_type_error<A>(err:EvalTyErr, st:State, env:Env, e:Exp) -> A {
    panic!("eval_type_error: {:?}:\n\tstate:{:?}\n\tenv:{:?}\n\te:{:?}\n", err, st, env, e)
}

pub fn eval_st(env:Env, e:Exp, st:State) -> ExpTerm {
    eval(st, env, e)
}

pub fn eval(st:State, mut env:Env, e:Exp) -> ExpTerm {
    match e.clone() {       
        Exp::Lam(x, e)    => { ExpTerm::Lam(env, x, e) }
        Exp::Ret(v)       => { ExpTerm::Ret(close_val(&env, &v)) }
        Exp::Anno(e1,_ct) => { eval(st, env, (*e1).clone()) }
        Exp::Fix(f,e1) => {
            let env_saved = env.clone();
            env.push((f, RtVal::FixThunk(env_saved, (*e1).clone())));
            eval(st, env, (*e1).clone())
        }
        Exp::Thunk(v, e1) => {
            match close_val(&env, &v) {
                RtVal::Name(n) => {
                    let t = thunk!([Some(n)]? eval_st ; env:env, e:(*e1).clone() ;; st:st);
                    ExpTerm::Ret(RtVal::Thunk(t))
                },
                v => eval_type_error(EvalTyErr::ThunkNonName(v), st, env, e)
            }
        }
        Exp::Ref(v1, v2) => {
            match close_val(&env, &v1) {
                RtVal::Name(n) => {
                    let v2 = close_val(&env, &v2);
                    let r = cell(n, v2);
                    ExpTerm::Ret(RtVal::Ref(r))
                },
                v => eval_type_error(EvalTyErr::RefNonName(v), st, env, e)
            }
        }
        Exp::Let(x,e1,e2) => {
            match eval(st.clone(), env.clone(), (*e1).clone()) {
                ExpTerm::Ret(v) => {
                    env.push((x, v));
                    eval(st, env, (*e2).clone())
                },
                term => eval_type_error(EvalTyErr::LetNonRet(term), st, env, e)
            }
        }
        Exp::App(e1, v) => {
            match eval(st.clone(), env.clone(), (*e1).clone()) {
                ExpTerm::Lam(mut env, x, e2) => {
                    let v = close_val(&env, &v);
                    env.push((x, v));
                    eval(st, env, (*e2).clone())
                },
                term => eval_type_error(EvalTyErr::AppNonLam(term), st, env, e)
            }
        }
        Exp::Split(v, x, y, e1) => {
            match close_val(&env, &v) {
                RtVal::Pair(v1, v2) => {
                    env.push((x, (*v1).clone()));
                    env.push((y, (*v2).clone()));
                    eval(st, env, (*e1).clone())
                },
                v => eval_type_error(EvalTyErr::SplitNonPair(v), st, env, e)
            }
        }
        // Exp::If(v,e0,e1) => {
        //     match close_val(&env, &v) {
        //         Val::Bool(false) => eval(st, env, (*e0).clone()),
        //         Val::Bool(true) => eval(st, env, (*e1).clone()),
        //         v => eval_type_error(EvalTyErr::IfNonBool(v), st, env, e)
        //     }
        // }
        Exp::Case(v, x, ex, y, ey) => {
            match close_val(&env, &v) {
                RtVal::Inj1(v) => {
                    env.push((x, (*v).clone()));
                    eval(st, env, (*ex).clone())
                },
                RtVal::Inj2(v) => {
                    env.push((y, (*v).clone()));
                    eval(st, env, (*ey).clone())
                },
                v => eval_type_error(EvalTyErr::SplitNonPair(v), st, env, e)
            }
        }
        Exp::Get(v) => {
            match close_val(&env, &v) {
                RtVal::Ref(a) => { ExpTerm::Ret(get!(a)) },
                v => eval_type_error(EvalTyErr::GetNonRef(v), st, env, e)
            }
        }
        Exp::Force(v) => {
            match close_val(&env, &v) {
                RtVal::Thunk(a)         => { force(&a) },
                RtVal::FixThunk(env, e) => { eval(st, env, e) },
                v => eval_type_error(EvalTyErr::ForceNonThunk(v), st, env, e)                    
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
            return eval(st, env, (*e).clone())
        }
        Exp::Unimp => unimplemented!(),
    }
}
