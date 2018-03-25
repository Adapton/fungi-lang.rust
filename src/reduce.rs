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
use std::rc::Rc;

use adapton::macros::*;
use adapton::engine::{thunk,NameChoice};
use adapton::engine;

use ast::*;
use dynamics::*;

/// Stack frame
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Frame {
    pub env: Env,
    pub cont: Cont,
}

/// Local continuations
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Cont {
    /// Continues an arrow-typed computation by applying a value to the function
    App(RtVal),
    /// Continues a value-producing computation by let-binding the produced value
    Let(Var,Exp),
}

/// Configuration for reduction: A stack, environment and expression.
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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

fn config_from_env_exp(env:Env, exp:Exp) -> Config {
    Config{
        stk:vec![],
        env:env,
        exp:exp,
    }
}

/// Dynamic type errors ("stuck cases" for reduction)
///
/// For each place in the `reduce` function where a dynamic type error
/// may arise that prevents us from progressing, we give a constructor
/// with the relevant information (first for documentation purposes,
/// and secondly for future error messages).
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Error {
    Irreducible,
    LamNonAppCont,
    HostEvalFnNonAppCont,
    RetNonLetCont,
    RefNonName,
    ThunkNonName,
    SplitNonPair,
    CaseNonInj,
    IfNonBool,
    GetNonRef,
    ForceNonThunk,
    NatPrim,
    NameBin,
    UnrollNonRoll,
    WriteScope,
    NameFnApp,
    RefThunkNonThunk,
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
fn set_env_rec(c:&mut Config, x:Var, v:Rc<RtVal>) {
    c.env.push((x,(*v).clone()))
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
fn consume_value(c:&mut Config, restore_env:Option<Env>,
                 x:Var, e:Rc<Exp>) -> Result<(),Error>
{
    match c.stk.pop().unwrap().cont {
        Cont::App(v) => {
            set_env(c, x, v);
            if let Some(env) = restore_env {
                c.env = env;
            };
            continue_rec(c, e)
        }
        _ => Result::Err(Error::LamNonAppCont),
    }
}
fn do_hostevalfn(c:&mut Config,
                 hef:HostEvalFn,
                 mut args:Vec<RtVal>) -> Result<(),Error>
{
    // pop the configuration's stack, pushing its arguments onto the
    // argument vector for the host evaluation function.
    loop {
        if args.len() == hef.arity {
            let te = (hef.eval)(args);
            return continue_te(c, te);
        }
        match c.stk.pop().unwrap().cont {
            Cont::App(v) => {
                args.push(v);
                continue
            }
            _ => return Result::Err(Error::HostEvalFnNonAppCont),
        }
    }
}
fn continue_rec(c:&mut Config, e:Rc<Exp>) -> Result<(),Error> {
    set_exp(c, e);
    Result::Ok(())
}
fn continue_with(c:&mut Config, e:Exp) -> Result<(),Error> {
    c.exp = e;
    Result::Ok(())
}
fn continue_te(c:&mut Config, te:ExpTerm) -> Result<(),Error> {
    match te {
        ExpTerm::Ret(v) => produce_value(c, v),
        ExpTerm::Lam(env,x,e) => consume_value(c,Some(env),x,e),
        ExpTerm::HostFn(hef, args) => do_hostevalfn(c,hef,args)
    }
}

/// Perform small steps of reduction until irreducible.
///
/// Reduces the current configuration until it is irreducible.
/// Typically (barring that no error occurs), this will both push and
/// pop the configuration's stack, and will consume its initial stack
/// frames, entirely.
///
pub fn reduce(c:Config) -> ExpTerm {
    let mut mc = c;
    loop {
        match step(&mut mc) {
            Ok(()) => continue,
            Err(Error::Irreducible) => break,
            Err(err) => panic!("{:?}", err),
        }
    }
    return match mc.exp {
        Exp::Lam(x, e)   => ExpTerm::Lam(mc.env, x, e),
        Exp::HostFn(hef) => ExpTerm::HostFn(hef, vec![]),
        Exp::Ret(v)      => ExpTerm::Ret(close_val(&mc.env, &v)),
        _                => unreachable!()
    }
}

/// Perform a single small-step reduction.
///
/// In the given reduction configuation, reduce the current expression
/// by one step.
///
pub fn step(c:&mut Config) -> Result<(),Error> {
    match c.exp.clone() {
        Exp::DefType(_, _, e)  |
        Exp::AnnoC(e, _)       |
        Exp::AnnoE(e, _)       |
        Exp::UseAll(_, e)      |
        Exp::IdxApp(e, _)      |
        Exp::Decls(_, e)      =>
        { continue_rec(c, e) }
        
        Exp::Fix(f, e1) => {
            let t = RtVal::ThunkAnon(c.env.clone(), c.exp.clone());
            set_env(c, f, t);
            continue_rec(c, e1)
        }
        Exp::App(e, v) => {
            let v = close_val(&c.env, &v);
            c.stk.push(Frame{
                env:c.env.clone(),
                cont:Cont::App(v),
            });
            continue_rec(c, e)
        }
        Exp::HostFn(hef) => {
            do_hostevalfn(c,hef,vec![])
        }
        Exp::Lam(x, e) => {
            consume_value(c, None, x, e)
        }
        Exp::Let(x, e1, e2) => {
            c.stk.push(Frame{
                env:c.env.clone(),
                cont:Cont::Let(x, (*e2).clone())
            });
            continue_rec(c, e1)
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
        Exp::Get(v) => {
            match close_val(&c.env, &v) {
                RtVal::Ref(a) => {
                    let v = engine::force(&a);
                    produce_value(c, v)
                },
                _ => Result::Err(Error::GetNonRef)
            }
        }
        Exp::Force(v) => {
            match close_val(&c.env, &v) {
                RtVal::Thunk(a) => {
                    let te = engine::force(&a);
                    continue_te(c, te)
                },
                RtVal::ThunkAnon(env, e) => {
                    c.env = env;
                    continue_with(c, e)
                }
                _ => Result::Err(Error::ForceNonThunk)
            }
        }
        
        Exp::Split(v, x, y, e1) => {
            match close_val(&c.env, &v) {
                RtVal::Pair(v1, v2) => {
                    set_env_rec(c, x, v1);
                    set_env_rec(c, y, v2);
                    continue_rec(c, e1)
                },
                _ => Result::Err(Error::SplitNonPair)
            }
        }
        Exp::IfThenElse(v, e1, e2) => {
            match close_val(&c.env, &v) {
                RtVal::Bool(b) => {
                    if b { continue_rec(c, e1) }
                    else { continue_rec(c, e2) }
                }
                _ => Result::Err(Error::IfNonBool)
            }
        }
        Exp::Case(v, x, ex, y, ey) => {
            match close_val(&c.env, &v) {
                RtVal::Inj1(v) => {
                    set_env_rec(c, x, v);
                    continue_rec(c, ex)
                },
                RtVal::Inj2(v) => {
                    set_env_rec(c, y, v);
                    continue_rec(c, ey)
                },
                _ => Result::Err(Error::CaseNonInj)
            }
        }
        Exp::Unroll(v, x, e1) => {
            match close_val(&c.env, &v) {
                RtVal::Roll(v) => {
                    set_env_rec(c, x, v);
                    continue_rec(c, e1)
                },
                _ => Result::Err(Error::UnrollNonRoll)
            }
        }
        Exp::Unpack(_i,_x,_v,_e) => {
            unimplemented!()
        }
        Exp::Thunk(v, e1) => {
            match close_val(&c.env, &v) {
                RtVal::Name(n) => { // create engine thunk named n
                    // suspending evaluation of expression e1:
                    let n = Some(engine_name_of_ast_name(n));
                    let t = thunk!([n]? reduce ;
                                   c:config_from_env_exp(
                                       c.env.clone(),
                                       (*e1).clone()
                                   ));
                    produce_value(c, RtVal::Thunk(t))
                },
                _ => Result::Err(Error::ThunkNonName)
            }
        }
        Exp::DebugLabel(label, msg, e) => {
            let label : Option<engine::Name> =
                label.map( engine_name_of_ast_name );
            engine::reflect_dcg::debug_effect(label, msg);
            continue_rec(c, e)
        }
        Exp::Unimp => { unimplemented!() }
        Exp::NoParse(s) => { panic!("Evaluation reached unparsed program text: `{}`", s) }
        Exp::PrimApp(PrimApp::NameBin(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Name(n1),RtVal::Name(n2)) => {
                    produce_value(c, RtVal::Name(Name::Bin(Rc::new(n1), Rc::new(n2))))
                },
                _ => Result::Err(Error::NameBin)
            }
        }
        Exp::WriteScope(v, e1) => {
            match close_val(&c.env, &v) {
                RtVal::NameFn(n) =>
                    match proj_namespace_name(nametm_eval(n)) {
                        None => Result::Err(Error::WriteScope),
                        Some(n) => {
                            match nametm_eval(n) {
                                NameTmVal::Name(n) => {
                                    let ns_name = engine_name_of_ast_name(n);
                                    let te = engine::ns(ns_name, ||{ reduce(config_from_env_exp(c.env.clone(), (*e1).clone())) });
                                    continue_te(c, te)
                                },                                    
                                _ => Result::Err(Error::WriteScope),
                            }
                        }
                    },
                _ => Result::Err(Error::WriteScope),
            }
        }
        Exp::NameFnApp(v1, v2) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                ( RtVal::NameFn(nf), RtVal::Name(n) ) => {
                    match nametm_eval(NameTm::App(Rc::new(nf),
                                                  Rc::new(NameTm::Name(n)))) {
                        NameTmVal::Name(n) =>
                            continue_te(c, ExpTerm::Ret(RtVal::Name(n))),
                        _ => Err(Error::NameFnApp),
                    }
                },
                _ => Err(Error::NameFnApp),
            }
        }
        
        //
        // In-built primitives for basetypes (naturals, bools, etc.)
        //
        
        Exp::PrimApp(PrimApp::NatPlus(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    produce_value(c, RtVal::Nat(n1 + n2))
                },
                _ => Result::Err(Error::NatPrim)
            }
        }        
        Exp::PrimApp(PrimApp::NatEq(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    produce_value(c, RtVal::Bool(n1 == n2))
                },
                _ => Result::Err(Error::NatPrim)
            }
        }
        Exp::PrimApp(PrimApp::NatLt(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    produce_value(c, RtVal::Bool(n1 < n2))
                },
                _ => Result::Err(Error::NatPrim)
            }
        }
        Exp::PrimApp(PrimApp::NatLte(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    produce_value(c, RtVal::Bool(n1 <= n2))
                },
                _  => Result::Err(Error::NatPrim)
            }
        }
        Exp::PrimApp(PrimApp::RefThunk(v)) => {
            fn val_of_retval (et:ExpTerm) -> RtVal {
                match et {
                    ExpTerm::Ret(v) => v,
                    _ => unreachable!()
                }
            };
            match close_val(&c.env, &v) {
                RtVal::Thunk(a) => {
                    let r = engine::thunk_map(a, Rc::new(val_of_retval));
                    let v = engine::force(&r);
                    continue_te(c, ExpTerm::Ret(
                        RtVal::Pair(Rc::new(RtVal::Ref(r)),
                                    Rc::new(v))))
                },
                _ => Err(Error::RefThunkNonThunk)
            }
        }
        
        /*_ => unimplemented!()*/
    }
}

/*    
        Exp::HostFn(hef) => { ExpTerm::HostFn(hef, vec![]) }
        // basecase 2: returns are terminal computations
        Exp::Ret(v)      => { ExpTerm::Ret(close_val(&c.env, &v)) }

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
            match close_val(&c.env, &v) {
                RtVal::Roll(v) => {
                    env.push((x,(*v).clone()));
                    return reduce(env, (*e1).clone())
                },
                v => type_error(Error::UnrollNonRoll(v), env, e)
            }
        }
        Exp::Unpack(_i,_x,_v,_e) => { unimplemented!("reduce unpack") }
        Exp::Thunk(v, e1) => {
            match close_val(&c.env, &v) {
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
            match close_val(&c.env, &v1) {
                RtVal::Name(n) => { // create engine ref named n, holding v2
                    let n = engine_name_of_ast_name(n);
                    let v2 = close_val(&c.env, &v2);
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
            let v = close_val(&c.env, &v);
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
            match close_val(&c.env, &v) {
                RtVal::Pair(v1, v2) => {
                    env.push((x, (*v1).clone()));
                    env.push((y, (*v2).clone()));
                    return reduce(env, (*e1).clone())
                },
                v => type_error(Error::SplitNonPair(v), env, e)
            }
        }
        Exp::IfThenElse(v, e1, e2) => {
            match close_val(&c.env, &v) {
                RtVal::Bool(b) => {
                    if b { return reduce(env, (*e1).clone()) }
                    else { return reduce(env, (*e2).clone()) }
                }
                v => type_error(Error::IfNonBool(v), env, e)
            }
        }
        Exp::Case(v, x, ex, y, ey) => {
            match close_val(&c.env, &v) {
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
            match close_val(&c.env, &v) {
                RtVal::Ref(a) => { ExpTerm::Ret(engine::force(&a)) },
                v => type_error(Error::GetNonRef(v), env, e)
            }
        }
        Exp::Force(v) => {
            match close_val(&c.env, &v) {
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
            match close_val(&c.env, &v) {
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
            match close_val(&c.env, &v) {
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
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
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
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
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
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Nat(n1 + n2))
                },
                (v1, v2) => type_error(Error::PrimAppNatPlus(v1,v2), env, e),
            }
        }        
        Exp::PrimApp(PrimApp::NatEq(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Bool(n1 == n2))
                },
                (v1, v2) => type_error(Error::PrimAppNatEq(v1,v2), env, e),
            }
        }
        Exp::PrimApp(PrimApp::NatLt(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Bool(n1 < n2))
                },
                (v1, v2) => type_error(Error::PrimAppNatLt(v1,v2), env, e),
            }
        }
        Exp::PrimApp(PrimApp::NatLte(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    ExpTerm::Ret(RtVal::Bool(n1 <= n2))
                },
                (v1, v2) => type_error(Error::PrimAppNatLte(v1,v2), env, e),
            }
        }

        
    }
}
*/
