/*! Evaluation semantics.

This module gives the incremental semantics of Fungi programs as a
"big-step" evaluation function, 
[`eval`](https://docs.rs/fungi-lang/0/src/fungi_lang/eval.rs.html).

To do so, it uses an external library ([Adapton in
Rust](http://adapton.org)) to create and maintain the "demanded
computation graph" (the DCG), that underpins change propagation.

See also: 
[`reduce`](https://docs.rs/fungi-lang/0/src/fungi_lang/reduce.rs.html).

*/

// ## Implementation discussion
//
// The Rust types and functions below demonstrate how closely the
// IODyn Target AST corresponds to the primitive notions of Adapton,
// namely `ref`s and `thunk`s, and their observation/demand
// operations, `get` and `force`, respectively.
//
// In particular, the semantics of `ref` and `thunk` are _entirely_
// encapsulated by the Adapton run-time library, leaving the
// dynamics semantics for other expression forms to `eval` to define.
// In this sense, the language built around the `ref` and `thunk`
// primitives is open-ended.
//
// Given this language choice, as usual, we choose STLC in CBPV, with
// product and sum types.  Other language/semantics design choices in
// this module are guided by our choice of "CBPV +
// environment-passing-style", as discussed further in this module's
// comments.
//
// ## Val vs RtVal
//
// We distinguish between programmer-written values (Val) and closed,
// run-time values (RtVal).  Environments map variables to (closed)
// run-time values.
//
// ## Exp vs TermExp
//
// We distinguish between (open) expressions and (fully evaluated)
// terminal expressions, which are closed.

use adapton::macros::*;
use adapton::engine::{thunk,NameChoice};
use adapton::engine;

use ast::{Exp,PrimApp,Name,NameTm};
use std::rc::Rc;
use dynamics::*;

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
    // unroll case
    UnrollNonRoll(RtVal),
    // thunk case
    ThunkNonName(RtVal),    
    ForceNonThunk(RtVal),
    RefThunkNonThunk(RtVal),
    // ref case
    RefNonName(RtVal),
    GetNonRef(RtVal),
    // write scope case
    WriteScopeWithoutName0,
    WriteScopeWithoutName1,
    WriteScopeWithoutName2,
    // name fn app
    NameFnApp0,
    NameFnApp1,
    // name bin
    PrimAppNameBin(RtVal,RtVal),
    // nat operations
    PrimAppNatLt(RtVal,RtVal),
    PrimAppNatEq(RtVal,RtVal),
    PrimAppNatLte(RtVal,RtVal),
    PrimAppNatPlus(RtVal,RtVal),
}

fn eval_type_error<A>(err:EvalTyErr, env:Env, e:Exp) -> A {
    panic!("eval_type_error: {:?}:\n\tenv:{:?}\n\te:{:?}\n", err, env, e)
}


/// Big-step evaluation
///
/// Under the given closing environment, evaluate the given Tgt-AST
/// expression, producing a terminal expression (a la CBPV), typically
/// with run-time values.
//
// # Implementation Discussion
//
// Adapton primitives: The primitives `thunk`, `ref`, `force` and
// `get` each use the Adapton run-time library in a simple way that
// directly corresponds with the given expression form.
//
// CPBV consequences: Due to CBPV style, most cases are simple (0 or 1
// recursive calls).  The only two cases that have multiple recursive
// calls are `let` and `app`, which necessarily each have two
// recursive calls to `eval`. In CBV style, many more cases would
// require multiple recursive calls to eval.
//
pub fn eval(mut env:Env, e:Exp) -> ExpTerm {
    match e.clone() {
        // basecase 1a: lambdas are terminal computations
        Exp::Lam(x, e)   => { ExpTerm::Lam(env, x, e) }
        // basecase 1b: host functions are terminal computations
        Exp::HostFn(hef) => { ExpTerm::HostFn(hef, vec![]) }
        // basecase 2: returns are terminal computations
        Exp::Ret(v)      => { ExpTerm::Ret(close_val(&env, &v)) }

        // ignore types at run time:
        Exp::DefType(_x, _a, e)  => { return eval(env, (*e).clone()) }
        Exp::AnnoC(e1,_ct)       => { return eval(env, (*e1).clone()) }
        Exp::AnnoE(e1,_et)       => { return eval(env, (*e1).clone()) }

        // XXX/TODO: Extend context with values/thunks from these definitions:
        Exp::UseAll(_, e)        => { return eval(env, (*e).clone()) }
        Exp::Decls(_, e)         => { return eval(env, (*e).clone()) }
        
        // save a copy of e as thunk f in e
        Exp::Fix(f,e1) => {
            let env_saved = env.clone();
            env.push((f, RtVal::ThunkAnon(env_saved, e)));
            return eval(env, (*e1).clone())
        }
        Exp::Unroll(v, x, e1) => {
            match close_val(&env, &v) {
                RtVal::Roll(v) => {
                    env.push((x,(*v).clone()));
                    return eval(env, (*e1).clone())
                },
                v => eval_type_error(EvalTyErr::UnrollNonRoll(v), env, e)
            }
        }
        Exp::Unpack(_i,_x,_v,_e) => { unimplemented!("eval unpack") }
        Exp::Thunk(v, e1) => {
            match close_val(&env, &v) {
                RtVal::Name(n) => { // create engine thunk named n
                    // suspending evaluation of expression e1:
                    let n = Some(engine_name_of_ast_name(n));
                    let t = thunk!([n]? eval ; env:env, e:(*e1).clone() );
                    ExpTerm::Ret(RtVal::Thunk(t))
                },
                v => eval_type_error(EvalTyErr::ThunkNonName(v), env, e)
            }
        }
        Exp::Ref(v1, v2) => {
            match close_val(&env, &v1) {
                RtVal::Name(n) => { // create engine ref named n, holding v2
                    let n = engine_name_of_ast_name(n);
                    let v2 = close_val(&env, &v2);
                    let r = engine::cell(n, v2);
                    ExpTerm::Ret(RtVal::Ref(r))
                },
                v => eval_type_error(EvalTyErr::RefNonName(v), env, e)
            }
        }
        Exp::Let(x,e1,e2) => {
            match eval(env.clone(), (*e1).clone()) {
                ExpTerm::Ret(v) => {
                    env.push((x, v));
                    return eval(env, (*e2).clone())
                },
                term => eval_type_error(EvalTyErr::LetNonRet(term), env, e)
            }
        }
        Exp::App(e1, v) => {
            let v = close_val(&env, &v);
            match eval(env.clone(), (*e1).clone()) {
                ExpTerm::Lam(mut env, x, e2) => {
                    env.push((x, v));
                    return eval(env, (*e2).clone())
                },
                ExpTerm::HostFn(hef, mut args) => {
                    // Call-by-push-value!
                    args.push(v);
                    if args.len() < hef.arity {
                        // keep pushing args:
                        return ExpTerm::HostFn(hef, args)
                    } else {
                        // done pushing args:
                        assert_eq!(args.len(), hef.arity);
                        return (hef.eval)(args)
                    }
                },
                term => eval_type_error(EvalTyErr::AppNonLam(term), env, e)
            }
        }
        Exp::IdxApp(_e1, _i) => { unimplemented!("Index application") }
        Exp::Split(v, x, y, e1) => {
            match close_val(&env, &v) {
                RtVal::Pair(v1, v2) => {
                    env.push((x, (*v1).clone()));
                    env.push((y, (*v2).clone()));
                    return eval(env, (*e1).clone())
                },
                v => eval_type_error(EvalTyErr::SplitNonPair(v), env, e)
            }
        }
        Exp::IfThenElse(v, e1, e2) => {
            match close_val(&env, &v) {
                RtVal::Bool(b) => {
                    if b { return eval(env, (*e1).clone()) }
                    else { return eval(env, (*e2).clone()) }
                }
                v => eval_type_error(EvalTyErr::IfNonBool(v), env, e)
            }
        }
        Exp::Case(v, x, ex, y, ey) => {
            match close_val(&env, &v) {
                RtVal::Inj1(v) => {
                    env.push((x, (*v).clone()));
                    return eval(env, (*ex).clone())
                },
                RtVal::Inj2(v) => {
                    env.push((y, (*v).clone()));
                    return eval(env, (*ey).clone())
                },
                v => eval_type_error(EvalTyErr::SplitNonPair(v), env, e)
            }
        }
        Exp::Get(v) => {
            match close_val(&env, &v) {
                RtVal::Ref(a) => { ExpTerm::Ret(engine::force(&a)) },
                v => eval_type_error(EvalTyErr::GetNonRef(v), env, e)
            }
        }
        Exp::Force(v) => {
            match close_val(&env, &v) {
                RtVal::Thunk(a)          => { engine::force(&a) },
                RtVal::ThunkAnon(env, e) => { return eval(env, e) },
                v => eval_type_error(EvalTyErr::ForceNonThunk(v), env, e)                    
            }
        }
        Exp::PrimApp(PrimApp::RefThunk(v)) => {
            fn val_of_retval (et:ExpTerm) -> RtVal {
                match et {
                    ExpTerm::Ret(v) => v,
                    _ => unreachable!()
                }
            };
            match close_val(&env, &v) {
                RtVal::Thunk(a) => {
                    let r = engine::thunk_map(a, Rc::new(val_of_retval));
                    let v = engine::force(&r);
                    ExpTerm::Ret(
                        RtVal::Pair(Rc::new(RtVal::Ref(r)),
                                    Rc::new(v)))
                },
                v => eval_type_error(EvalTyErr::RefThunkNonThunk(v), env, e)
            }
        }
        Exp::WriteScope(v, e1) => {
            // Names vs namespace functions: Here, v is a name
            // function value, but the current Adapton engine
            // implementation of namespaces, aka "write scopes",
            // requires that each is given by a name, which is always
            // prepended to any allocated names; the engine lacks the
            // more general notion of a "name function" (which can
            // express more general name constructions than just
            // "prepend").  For now, we "translate" namespace
            // functions into names, by projecting out their "names"
            // from an eta-expanded prepend operation.  If we fail to
            // find this pattern, we fail (TODO: enforce statically?).
            match close_val(&env, &v) {
                RtVal::NameFn(n) =>
                    match proj_namespace_name(nametm_eval(n)) {
                        None => eval_type_error(EvalTyErr::WriteScopeWithoutName1, env, e),
                        Some(n) => {
                            match nametm_eval(n) {
                                NameTmVal::Name(n) => {
                                    let ns_name = engine_name_of_ast_name(n);
                                    engine::ns(ns_name, ||{ eval(env, (*e1).clone()) })
                                },                                    
                                _ => eval_type_error(EvalTyErr::WriteScopeWithoutName2, env, e),
                            }
                        }
                    },
                _ => eval_type_error(EvalTyErr::WriteScopeWithoutName0, env, e),
            }
        }
        Exp::NameFnApp(v1, v2) => {
            // (value-injected) name function application: apply
            // (injected) name function v1 to (injected) name v2; the
            // evaluation itself happens in the name term sublanguage,
            // via nametm_eval.  The result is an (injected) name.
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                ( RtVal::NameFn(nf), RtVal::Name(n) ) => {
                    match nametm_eval(NameTm::App(Rc::new(nf),
                                                  Rc::new(NameTm::Name(n)))) {
                        NameTmVal::Name(n) => ExpTerm::Ret(RtVal::Name(n)),
                        _ => eval_type_error(EvalTyErr::NameFnApp1, env, e),
                    }
                },
                _ => eval_type_error(EvalTyErr::NameFnApp0, env, e),
            }
        }
        Exp::DebugLabel(label, msg, e) => {
            let label : Option<engine::Name> =
                label.map( engine_name_of_ast_name );
            engine::reflect_dcg::debug_effect(label, msg);
            return eval(env, (*e).clone())
        }
        Exp::Unimp => unimplemented!(),
        Exp::NoParse(s) => panic!("Evaluation reached unparsed program text: `{}`", s),

        // Names: Primitive operation for 
        
        Exp::PrimApp(PrimApp::NameBin(v1,v2)) => {
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                (RtVal::Name(n1),RtVal::Name(n2)) => {
                    ExpTerm::Ret(RtVal::Name(Name::Bin(Rc::new(n1), Rc::new(n2))))
                },
                (v1, v2) => eval_type_error(EvalTyErr::PrimAppNameBin(v1,v2), env, e),
            }
        }
        
        //
        // In-built primitives for basetypes (naturals, bools, etc.)
        //
        
        Exp::PrimApp(PrimApp::NatPlus(v1,v2)) => {
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Nat(n1 + n2))
                },
                (v1, v2) => eval_type_error(EvalTyErr::PrimAppNatPlus(v1,v2), env, e),
            }
        }        
        Exp::PrimApp(PrimApp::NatEq(v1,v2)) => {
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Bool(n1 == n2))
                },
                (v1, v2) => eval_type_error(EvalTyErr::PrimAppNatEq(v1,v2), env, e),
            }
        }
        Exp::PrimApp(PrimApp::NatLt(v1,v2)) => {
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Bool(n1 < n2))
                },
                (v1, v2) => eval_type_error(EvalTyErr::PrimAppNatLt(v1,v2), env, e),
            }
        }
        Exp::PrimApp(PrimApp::NatLte(v1,v2)) => {
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Bool(n1 <= n2))
                },
                (v1, v2) => eval_type_error(EvalTyErr::PrimAppNatLte(v1,v2), env, e),
            }
        }

        
    }
}
