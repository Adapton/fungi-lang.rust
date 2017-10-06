//! Big-step reference evaluation semantics, for IODyn AST.
//!
//! Gives (non-incremental) reference semantics, using native Rust
//! collections in place of the IODyn collections.  Does not use
//! explicit names, nor the Adapton-based IODyn collections library.

use ast::{Name,Var,Exp,Val,Pointer,PrimApp};
use std::collections::hash_map::HashMap;
use std::rc::Rc;

pub type Env   = HashMap<String,Val>;
pub type Store = HashMap<Pointer,StoreObj>;

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum ExpTerm {
    Lam(Env, Var, Rc<Exp>),
    Ret(Val),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct State {
    store:Store,
    next_pointer:Name
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum StoreObj {
    Cell(Val),
    Thunk(Env,Exp)
}

//fn first_name() -> Name { Name::Leaf }
fn next_name(nm:Name) -> Name { Name::Bin(Rc::new(Name::Leaf),Rc::new(nm)) }

fn allocate_pointer(st:State, so:StoreObj) -> (State, Pointer) {
    let mut st = st;
    let ptr = st.next_pointer.clone();
    st.next_pointer = next_name(ptr.clone());
    drop(st.store.insert(Pointer(ptr.clone()), so));
    (st, Pointer(ptr))
}

// panics if the environment fails to close the given value's variables
fn close_val(env:&Env, v:&Val) -> Val {
    use ast::Val::*;
    match *v {
        // variable case:
        Var(ref x)   => env.get(x).unwrap().clone(),

        // other cases: base cases, and structural recursion:
        Unit         => Unit,
        Nat(ref n)   => Nat(n.clone()),
        Str(ref s)   => Str(s.clone()),
        Ref(ref p)   => Ref(p.clone()),
        Thunk(ref p) => Thunk(p.clone()),

        // TODO: system invariant: collections always contain _closed_
        // values; hence, no need to recur into them to close them
        // here (which would be prohibitively expensive).  In this
        // way, they are akin to "store-allocated" structures
        // represented by pointers (viz., ref cells and thunks).
        Seq(ref s)   => Seq(s.clone()),
        Stack(ref s) => Stack(s.clone()),
        Queue(ref q) => Queue(q.clone()),
        Hashmap(ref m) => Hashmap(m.clone()),
        Kvlog(ref l) => Kvlog(l.clone()),
        Graph(ref g) => Graph(g.clone()),

        // inductive cases
        Injl(ref v1) => Injl(close_val_rec(env, v1)),
        Injr(ref v1) => Injr(close_val_rec(env, v1)),
        Anno(ref v1, ref t)  => Anno(close_val_rec(env, v1), t.clone()),
        Pair(ref v1, ref v2) => Pair(close_val_rec(env, v1), close_val_rec(env, v2)),
    }
}

fn close_val_rec(env:&Env, v:&Rc<Val>) -> Rc<Val> {
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
    SplitNonPair(Val),
    // case case
    CaseNonInj(Val),
    // force cases
    ForceNonThunk(Val),
    ForceDangling(Pointer),
    ForceCell(Pointer),
    // get cases
    GetNonRef(Val),
    GetDangling(Pointer),
    GetThunk(Pointer),
}

fn eval_type_error<A>(err:EvalTyErr, st:State, env:Env, e:Exp) -> A {
    panic!("eval_type_error: {:?}:\n\tstate:{:?}\n\tenv:{:?}\n\te:{:?}\n", err, st, env, e)
}

fn st_get(st:&State, p:&Pointer) -> Option<StoreObj> {
    st.store.get(p).map(|x|x.clone())
}

pub fn eval_prim(st:State, env:Env, p:PrimApp) -> (State, ExpTerm) {
    drop((st,env,p));
    unimplemented!()
}

pub fn eval(st:State, env:Env, e:Exp) -> (State, ExpTerm) {
    match e.clone() {
        Exp::Lam(x, e)    => { (st, ExpTerm::Lam(env, x, e)) }
        Exp::Ret(v)       => { (st, ExpTerm::Ret(close_val(&env, &v))) }
        Exp::Anno(e1,_ct) => { eval(st, env, (*e1).clone()) }
        Exp::Name(_nm,e1) => { eval(st, env, (*e1).clone()) }
        Exp::Fix(f,e1) => {
            let (st, ptr) = allocate_pointer(st, StoreObj::Thunk(env.clone(), (*e1).clone()));
            let mut env = env;
            env.insert(f, Val::Thunk(ptr));
            eval(st, env, (*e1).clone())
        }
        Exp::Thunk(e1) => {
            let (st, ptr) = allocate_pointer(st, StoreObj::Thunk(env.clone(), (*e1).clone()));
            (st, ExpTerm::Ret(Val::Thunk(ptr)))
        }
        Exp::Ref(v) => {
            let (st, ptr) = allocate_pointer(st, StoreObj::Cell(close_val(&env, &v)));
            (st, ExpTerm::Ret(Val::Ref(ptr)))
        }
        Exp::Let(x,e1,e2) => {
            match eval(st, env.clone(), (*e1).clone()) {
                (st, ExpTerm::Ret(v)) => {
                    let mut env = env;
                    env.insert(x, v);
                    eval(st, env, (*e2).clone())
                },
                (st, term) => eval_type_error(EvalTyErr::LetNonRet(term), st, env, e)
            }
        }
        Exp::App(e1, v) => {
            match eval(st, env.clone(), (*e1).clone()) {
                (st, ExpTerm::Lam(env, x, e2)) => {
                    let mut env = env;
                    env.insert(x, v);
                    eval(st, env, (*e2).clone())
                },
                (st, term) => eval_type_error(EvalTyErr::AppNonLam(term), st, env, e)
            }
        }
        Exp::Split(v, x, y, e1) => {
            match close_val(&env, &v) {
                Val::Pair(v1, v2) => {
                    let mut env = env;
                    env.insert(x, (*v1).clone());
                    env.insert(y, (*v2).clone());
                    eval(st, env, (*e1).clone())
                },
                v => eval_type_error(EvalTyErr::SplitNonPair(v), st, env, e)
            }
        }
        Exp::Case(v, x, ex, y, ey) => {
            match close_val(&env, &v) {
                Val::Injl(v) => {
                    let mut env = env;
                    env.insert(x, (*v).clone());
                    eval(st, env, (*ex).clone())
                },
                Val::Injr(v) => {
                    let mut env = env;
                    env.insert(y, (*v).clone());
                    eval(st, env, (*ey).clone())
                },
                v => eval_type_error(EvalTyErr::SplitNonPair(v), st, env, e)
            }
        }
        Exp::PrimApp(p) => { eval_prim(st, env, p) }
        Exp::Get(v) => {
            match close_val(&env, &v) {
                Val::Ref(ptr) => match st_get(&st, &ptr) {
                    Some(StoreObj::Cell(v))    => { (st, ExpTerm::Ret(v)) }
                    Some(StoreObj::Thunk(_,_)) => eval_type_error(EvalTyErr::GetThunk(ptr), st, env, e),
                    None                       => eval_type_error(EvalTyErr::GetDangling(ptr), st, env, e),
                },
                v => eval_type_error(EvalTyErr::GetNonRef(v), st, env, e)
            }
        }
        Exp::Force(v) => {
            match close_val(&env, &v) {
                Val::Thunk(ptr) => match st_get(&st, &ptr) {
                    Some(StoreObj::Thunk(env2,e2)) => eval(st, env2, e2),
                    Some(StoreObj::Cell(_v))       => eval_type_error(EvalTyErr::ForceCell(ptr), st, env, e),
                    None                           => eval_type_error(EvalTyErr::ForceDangling(ptr), st, env, e),
                },
                v => eval_type_error(EvalTyErr::ForceNonThunk(v), st, env, e)
            }
        }
    }
}
