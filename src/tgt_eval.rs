//! Big-step reference evaluation semantics, for IODyn Target AST.
//!
//! Gives the incremental semantics of programs, using an external
//! library (Adapton in Rust) to create and maintain the DCG.

use std::cell::RefCell;
use ast::{Name,Pointer,Var};
use tgt_ast::{Exp,Val};
//use ast::cons::{val_pair, val_option};
use std::collections::hash_map::HashMap;
use std::rc::Rc;

pub type Env   = HashMap<String,Val>;
//pub type Store = HashMap<Pointer,StoreObj>;

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum ExpTerm {
    Lam(Env, Var, Rc<Exp>),
    Ret(Val),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct State {
//    store:Store,
    next_pointer:Name
}

// #[derive(Clone,Debug,Eq,PartialEq)]
// pub enum StoreObj {
//     Cell(Val),
//     Thunk(Env,Exp)
// }

//fn first_name() -> Name { Name::Leaf }
fn next_name(nm:Name) -> Name { Name::Bin(Rc::new(Name::Leaf),Rc::new(nm)) }

// fn allocate_pointer(st:State, so:StoreObj) -> (State, Pointer) {
//     let mut st = st;
//     let ptr = st.next_pointer.clone();
//     st.next_pointer = next_name(ptr.clone());
//     drop(st.store.insert(Pointer(ptr.clone()), so));
//     (st, Pointer(ptr))
// }

// panics if the environment fails to close the given value's variables
/// Substitution on all values
fn close_val(env:&Env, v:&Val) -> Val {
    use tgt_ast::Val::*;
    match *v {
        // variable case:
        Var(ref x)   => env.get(x).unwrap().clone(),

        // other cases: base cases, and structural recursion:
        Name(ref n)    => Name(n.clone()), // XXX/TODO --- Descend into name terms and continue substitution..?.
        NameFn(ref nf) => NameFn(nf.clone()), // XXX/TODO --- Descend into name terms and continue substitution...?
        
        Unit         => Unit,
        Nat(ref n)   => Nat(n.clone()),
        Str(ref s)   => Str(s.clone()),
        Ref(ref p)   => Ref(p.clone()),
        Thunk(ref p) => Thunk(p.clone()),

        // inductive cases
        Inj1(ref v1) => Inj1(close_val_rec(env, v1)),
        Inj2(ref v1) => Inj2(close_val_rec(env, v1)),
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
    // if case
    IfNonBool(Val),
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

//fn st_get(st:&State, p:&Pointer) -> Option<StoreObj> {
//    st.store.get(p).map(|x|x.clone())
//}

// pub fn eval_prim(st:State, env:&Env, p:PrimApp) -> (State, ExpTerm) {
//     match p {
//         PrimApp::StackEmpty => {
//             let v_empty = Val::Stack(Stack{
//                  stack:Rc::new(RefCell::new(Vec::new()))
//              });
//             (st, ExpTerm::Ret(v_empty))
//         },
//         PrimApp::StackPush(Val::Stack(so), v_elm) => {
//             so.stack.borrow_mut().push(close_val(env, &v_elm));
//             (st, ExpTerm::Ret(Val::Stack(so)))
//         },
//         PrimApp::StackPop(Val::Stack(so)) => {
//             let v_op : Val = val_option(so.stack.borrow_mut().pop());
//             (st, ExpTerm::Ret(val_pair(Val::Stack(so), v_op )))
//         },
//         _ => unimplemented!()
//     }
// }

pub fn eval(st:State, env:Env, e:Exp) -> (State, ExpTerm) {
    match e.clone() {       
        Exp::Lam(x, e)    => { (st, ExpTerm::Lam(env, x, e)) }
        Exp::Ret(v)       => { (st, ExpTerm::Ret(close_val(&env, &v))) }
        Exp::Anno(e1,_ct) => { eval(st, env, (*e1).clone()) }
//        Exp::Label(_nm,e1) => { eval(st, env, (*e1).clone()) }
//        Exp::TrHint(_h,e1) => { eval(st, env, (*e1).clone()) }
//        Exp::Archivist(e) => { unimplemented!("eval archivist") }
        Exp::Fix(f,e1) => {
            //let (st, ptr) = allocate_pointer(st, StoreObj::Thunk(env.clone(), (*e1).clone()));
            let (st, ptr) = panic!("");
            let mut env = env;
            env.insert(f, Val::Thunk(ptr));
            eval(st, env, (*e1).clone())
        }
        Exp::Thunk(e1) => {
            //let (st, ptr) = allocate_pointer(st, StoreObj::Thunk(env.clone(), (*e1).clone()));
            let (st, ptr) = panic!("");
            (st, ExpTerm::Ret(Val::Thunk(ptr)))
        }
        Exp::Ref(v) => {
            //let (st, ptr) = allocate_pointer(st, StoreObj::Cell(close_val(&env, &v)));
            let (st, ptr) = panic!("");
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
        // Exp::If(v,e0,e1) => {
        //     match close_val(&env, &v) {
        //         Val::Bool(false) => eval(st, env, (*e0).clone()),
        //         Val::Bool(true) => eval(st, env, (*e1).clone()),
        //         v => eval_type_error(EvalTyErr::IfNonBool(v), st, env, e)
        //     }
        // }
        Exp::Case(v, x, ex, y, ey) => {
            match close_val(&env, &v) {
                Val::Inj1(v) => {
                    let mut env = env;
                    env.insert(x, (*v).clone());
                    eval(st, env, (*ex).clone())
                },
                Val::Inj2(v) => {
                    let mut env = env;
                    env.insert(y, (*v).clone());
                    eval(st, env, (*ey).clone())
                },
                v => eval_type_error(EvalTyErr::SplitNonPair(v), st, env, e)
            }
        }
//        Exp::PrimApp(p) => { panic!("eval_prim(st, &env, p)") }
        Exp::Get(v) => {
            match close_val(&env, &v) {
                Val::Ref(ptr) => {
                    panic!("")
                },
                v => eval_type_error(EvalTyErr::GetNonRef(v), st, env, e)
            }
        }
        Exp::Force(v) => {
            match close_val(&env, &v) {
                Val::Thunk(ptr) => {
                    panic!("")
                },
                v => eval_type_error(EvalTyErr::ForceNonThunk(v), st, env, e)                    
            }
        }
        Exp::Scope(v, e) => {
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
