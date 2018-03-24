/*! Reduction semantics.

This module gives the incremental semantics of Fungi programs as a
"small-step" reduction function, 
[`reduce`](https://docs.rs/fungi-lang/0/src/fungi_lang/reduce.rs.html).

To do so, it uses an external library ([Adapton in
Rust](http://adapton.org)) to create and maintain the "demanded
computation graph" (the DCG), that underpins change propagation.

See also: 
[`eval`](https://docs.rs/fungi-lang/0/fungi_lang/eval.rs.html).

*/

use adapton::macros::*;
use adapton::engine::{thunk,NameChoice};
use adapton::engine;

use ast::{Var,Exp,PrimApp,Name,NameTm};
use std::rc::Rc;
use dynamics::*;

/// Stack frame
pub struct Frame {
    pub env: Env,
    pub cont: Cont,
}

/// Local continuations
pub enum Cont {
    /// Continues an arrow-typed computation by applying a value to the function
    App(RtVal),
    /// Continues a value-producing computation by let-binding the produced value
    Let(Var,Exp),
}

/// Configuration for reduction: A stack, environment and expression.
pub struct Config {
    /// The Stack continues the expression with local continuations (one per frame)
    pub stk: Vec<Frame>,
    /// The environment closes the expression's free variables
    pub env: Env,
    /// The expression gives the "active program"
    ///
    /// This "active program" is closed by the environment, and
    /// continued by the local continuations (and closing
    /// environments) stored on the stack.
    pub exp: Exp,
}

/// Dynamic type errors ("stuck cases" for reduction)
///
/// For each place in the `reduce` function where a dynamic type error
/// may arise that prevents us from progressing, we give a constructor
/// with the relevant information (first for documentation purposes,
/// and secondly for future error messages).
#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Error {
    LamNonAppCont,
    RetNonLetCont,
    RefNonName,
}

// fn type_error<A>(err:Error, env:Env, e:Exp) -> A {
//     panic!("type_error: {:?}:\n\tenv:{:?}\n\te:{:?}\n", err, env, e)
// }

fn set_exp(c:&mut Config, e:Rc<Exp>) {
    c.exp = (*e).clone()
}
fn set_env(c:&mut Config, x:Var, v:RtVal) {
    c.env.push((x,v))
}

fn produce_value(c:&mut Config, v:RtVal) -> Result<(),Error> {
    match c.stk.pop().unwrap().cont {
        Cont::Let(x, e) => {
            set_env(c, x, v);
            c.exp = e;
            Result::Ok(())
        }
        _ => Result::Err(Error::RetNonLetCont),
    }
}

/// Step: perform a single small-step reduction.
///
/// In the given reduction configuation, reduce the current expression
/// by one step.
///
pub fn step(c:&mut Config) -> Result<(),Error> {
    match c.exp.clone() {
        Exp::Fix(f, e1) => {
            let t = RtVal::ThunkAnon(c.env.clone(), c.exp.clone());
            set_env(c, f, t);
            set_exp(c, e1);
            Result::Ok(())
        }
        Exp::App(e, v) => {
            let v = close_val(&c.env, &v);
            c.stk.push(Frame{
                env:c.env.clone(),
                cont:Cont::App(v),
            });
            set_exp(c, e);
            Result::Ok(())
        }
        Exp::Lam(x, e) => {
            match c.stk.pop().unwrap().cont {
                Cont::App(v) => {
                    set_env(c, x, v);
                    set_exp(c, e);
                    Result::Ok(())
                }
                _ => Result::Err(Error::LamNonAppCont),
            }
        }
        Exp::Let(x, e1, e2) => {
            c.stk.push(Frame{
                env:c.env.clone(),
                cont:Cont::Let(x, (*e2).clone())
            });
            set_exp(c, e1);
            Result::Ok(())
        }        
        Exp::Ret(v) => {
            let v = close_val(&c.env, &v);
            produce_value(c, v)
        }
        Exp::Ref(v1, v2) => {
            match close_val(&c.env, &v1) {
                RtVal::Name(n) => { // create engine ref named n, holding v2
                    let n = engine_name_of_ast_name(n);
                    let v2 = close_val(&c.env, &v2);
                    let r = engine::cell(n, v2);
                    produce_value(c, RtVal::Ref(r))
                },
                _ => Result::Err(Error::RefNonName)
            }
        }
        
        
        _ => unimplemented!()
    }
}

/*    
        Exp::HostFn(hef) => { ExpTerm::HostFn(hef, vec![]) }
        // basecase 2: returns are terminal computations
        Exp::Ret(v)      => { ExpTerm::Ret(close_val(&env, &v)) }

        // ignore types at run time:
        Exp::DefType(_x, _a, e)  => { return reduce(env, (*e).clone()) }
        Exp::AnnoC(e1,_ct)       => { return reduce(env, (*e1).clone()) }
        Exp::AnnoE(e1,_et)       => { return reduce(env, (*e1).clone()) }

        // XXX/TODO: Extend context with values/thunks from these definitions:
        Exp::UseAll(_, e)        => { return reduce(env, (*e).clone()) }
        Exp::Decls(_, e)         => { return reduce(env, (*e).clone()) }
        
        // save a copy of e as thunk f in e
        Exp::Fix(f,e1) => {
            let env_saved = env.clone();
            env.push((f, RtVal::ThunkAnon(env_saved, e)));
            return reduce(env, (*e1).clone())
        }
        Exp::Unroll(v, x, e1) => {
            match close_val(&env, &v) {
                RtVal::Roll(v) => {
                    env.push((x,(*v).clone()));
                    return reduce(env, (*e1).clone())
                },
                v => type_error(Error::UnrollNonRoll(v), env, e)
            }
        }
        Exp::Unpack(_i,_x,_v,_e) => { unimplemented!("reduce unpack") }
        Exp::Thunk(v, e1) => {
            match close_val(&env, &v) {
                RtVal::Name(n) => { // create engine thunk named n
                    // suspending reduceuation of expression e1:
                    let n = Some(engine_name_of_ast_name(n));
                    let t = thunk!([n]? reduce ; env:env, e:(*e1).clone() );
                    ExpTerm::Ret(RtVal::Thunk(t))
                },
                v => type_error(Error::ThunkNonName(v), env, e)
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
                v => type_error(Error::RefNonName(v), env, e)
            }
        }
        Exp::Let(x,e1,e2) => {
            match reduce(env.clone(), (*e1).clone()) {
                ExpTerm::Ret(v) => {
                    env.push((x, v));
                    return reduce(env, (*e2).clone())
                },
                term => type_error(Error::LetNonRet(term), env, e)
            }
        }
        Exp::App(e1, v) => {
            let v = close_val(&env, &v);
            match reduce(env.clone(), (*e1).clone()) {
                ExpTerm::Lam(mut env, x, e2) => {
                    env.push((x, v));
                    return reduce(env, (*e2).clone())
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
                term => type_error(Error::AppNonLam(term), env, e)
            }
        }
        Exp::IdxApp(_e1, _i) => { unimplemented!("Index application") }
        Exp::Split(v, x, y, e1) => {
            match close_val(&env, &v) {
                RtVal::Pair(v1, v2) => {
                    env.push((x, (*v1).clone()));
                    env.push((y, (*v2).clone()));
                    return reduce(env, (*e1).clone())
                },
                v => type_error(Error::SplitNonPair(v), env, e)
            }
        }
        Exp::IfThenElse(v, e1, e2) => {
            match close_val(&env, &v) {
                RtVal::Bool(b) => {
                    if b { return reduce(env, (*e1).clone()) }
                    else { return reduce(env, (*e2).clone()) }
                }
                v => type_error(Error::IfNonBool(v), env, e)
            }
        }
        Exp::Case(v, x, ex, y, ey) => {
            match close_val(&env, &v) {
                RtVal::Inj1(v) => {
                    env.push((x, (*v).clone()));
                    return reduce(env, (*ex).clone())
                },
                RtVal::Inj2(v) => {
                    env.push((y, (*v).clone()));
                    return reduce(env, (*ey).clone())
                },
                v => type_error(Error::SplitNonPair(v), env, e)
            }
        }
        Exp::Get(v) => {
            match close_val(&env, &v) {
                RtVal::Ref(a) => { ExpTerm::Ret(engine::force(&a)) },
                v => type_error(Error::GetNonRef(v), env, e)
            }
        }
        Exp::Force(v) => {
            match close_val(&env, &v) {
                RtVal::Thunk(a)          => { engine::force(&a) },
                RtVal::ThunkAnon(env, e) => { return reduce(env, e) },
                v => type_error(Error::ForceNonThunk(v), env, e)                    
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
                v => type_error(Error::RefThunkNonThunk(v), env, e)
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
                        None => type_error(Error::WriteScopeWithoutName1, env, e),
                        Some(n) => {
                            match nametm_eval(n) {
                                NameTmVal::Name(n) => {
                                    let ns_name = engine_name_of_ast_name(n);
                                    engine::ns(ns_name, ||{ reduce(env, (*e1).clone()) })
                                },                                    
                                _ => type_error(Error::WriteScopeWithoutName2, env, e),
                            }
                        }
                    },
                _ => type_error(Error::WriteScopeWithoutName0, env, e),
            }
        }
        Exp::NameFnApp(v1, v2) => {
            // (value-injected) name function application: apply
            // (injected) name function v1 to (injected) name v2; the
            // reduceuation itself happens in the name term sublanguage,
            // via nametm_eval.  The result is an (injected) name.
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                ( RtVal::NameFn(nf), RtVal::Name(n) ) => {
                    match nametm_eval(NameTm::App(Rc::new(nf),
                                                  Rc::new(NameTm::Name(n)))) {
                        NameTmVal::Name(n) => ExpTerm::Ret(RtVal::Name(n)),
                        _ => type_error(Error::NameFnApp1, env, e),
                    }
                },
                _ => type_error(Error::NameFnApp0, env, e),
            }
        }
        Exp::DebugLabel(label, msg, e) => {
            let label : Option<engine::Name> =
                label.map( engine_name_of_ast_name );
            engine::reflect_dcg::debug_effect(label, msg);
            return reduce(env, (*e).clone())
        }
        Exp::Unimp => unimplemented!(),
        Exp::NoParse(s) => panic!("Reduceuation reached unparsed program text: `{}`", s),

        // Names: Primitive operation for 
        
        Exp::PrimApp(PrimApp::NameBin(v1,v2)) => {
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                (RtVal::Name(n1),RtVal::Name(n2)) => {
                    ExpTerm::Ret(RtVal::Name(Name::Bin(Rc::new(n1), Rc::new(n2))))
                },
                (v1, v2) => type_error(Error::PrimAppNameBin(v1,v2), env, e),
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
                (v1, v2) => type_error(Error::PrimAppNatPlus(v1,v2), env, e),
            }
        }        
        Exp::PrimApp(PrimApp::NatEq(v1,v2)) => {
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Bool(n1 == n2))
                },
                (v1, v2) => type_error(Error::PrimAppNatEq(v1,v2), env, e),
            }
        }
        Exp::PrimApp(PrimApp::NatLt(v1,v2)) => {
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Bool(n1 < n2))
                },
                (v1, v2) => type_error(Error::PrimAppNatLt(v1,v2), env, e),
            }
        }
        Exp::PrimApp(PrimApp::NatLte(v1,v2)) => {
            match (close_val(&env, &v1), close_val(&env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Bool(n1 <= n2))
                },
                (v1, v2) => type_error(Error::PrimAppNatLte(v1,v2), env, e),
            }
        }

        
    }
}
*/
