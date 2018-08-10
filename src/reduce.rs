/*! Reduction semantics.

This module gives the incremental semantics of Fungi programs as a
"small-step" reduction function, 
[`reduce`](https://docs.rs/fungi-lang/0/src/fungi_lang/reduce.rs.html).

To do so, it uses an external library ([Adapton in
Rust](http://adapton.org)) to create and maintain the "demanded
computation graph" (the DCG), that underpins change propagation.

See also: 
[`eval`](https://docs.rs/fungi-lang/0/src/fungi_lang/eval.rs.html).

 */

use std::rc::Rc;
use std::env as std_env;
use vt100;
    
use adapton::macros::*;
use adapton::engine::{thunk,NameChoice};
use adapton::engine;

use ast::*;
use dynamics::*;

/// Stack frame
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Frame {
    pub env: EnvRec,
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

/// System configuration: global flags, etc
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct SysCfg {
    pub verbose: bool,
}

/// Configuration for reduction: A stack, environment and expression.
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Config {
    /// System configuration, for global flags, etc
    pub sys: SysCfg,
    /// The Stack continues the expression with local continuations (one per frame)
    pub stk: Vec<Frame>,
    /// The environment closes the expression's free variables
    pub env: EnvRec,
    /// The expression gives the "active program"
    ///
    /// This "active program" is closed by the environment, and
    /// continued by the local continuations (and closing
    /// environments) stored on the stack.
    pub exp: Exp,
}

/// Cases for which `step` fails to reduce the program
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum StepError {
    /// Ordinary program termination
    ///
    /// Though a "step error" (`step` cannot reduce the
    /// configuration), this outcome signals ordinary termination of
    /// the program.  In particular, `step` cannot reduce a terminal
    /// expression in a configuration with an empty stack: there are
    /// no continuations to follow; these configurations have "halted"
    /// (terminated).
    ///
    Halt(ExpTerm),
    /// Irreducible, ill-typed program configurations
    ///
    /// All other errors (aside from an empty stack) are _unexpected_
    /// in a well-typed Fungi program, and correspond to reduction
    /// getting "stuck" in a state that is not well-typed.
    Stuck(Stuck)
}

/// Dynamic type errors ("stuck cases" for reduction)
///
/// For each place in the `reduce` function where a dynamic type error
/// may arise that prevents us from progressing, we give a constructor
/// with the relevant information (first for documentation purposes,
/// and secondly for future error messages).
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Stuck {
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
    UnpackNonPack,
    WriteScope,
    NameFnApp,
    RefThunkNonThunk,
}

fn stuck_err<X>(s:Stuck) -> Result<X,StepError> {
    Err(StepError::Stuck(s))
}
fn set_exp(c:&mut Config, e:Rc<Exp>) {
    //debug_set_exp(c, &e);
    c.exp = (*e).clone()        
}
fn set_env(c:&mut Config, x:Var, v:RtVal) {
    debug_bind(c, &x, &v);
    c.env = env_push(&c.env, &x, v)
}
fn set_env_rec(c:&mut Config, x:Var, v:Rc<RtVal>) {
    set_env(c, x, (*v).clone())
}
fn use_all(c:&mut Config, d:UseAllModule) {
    update_env_with_decls(c, ((*d.module).decls).clone())
}
fn update_env_with_decls(c:&mut Config, d:Decls) {
    let mut decls = d;
    loop {
        match decls {
            Decls::End => { break }
            Decls::NoParse(s) => { panic!("cannot process unparsed decls:\n\t`{}`", s) }
            Decls::Doc(_, d) |
            Decls::NmTm(_, _, d) |
            Decls::IdxTm(_, _, d) |
            Decls::Type(_, _, d) => {
                decls = (*d).clone();
                continue;
            }
            Decls::UseAll(uam, d) => {
                use_all(c, uam);
                decls = (*d).clone();
                continue;
            }
            Decls::Val(x,_,v,d) => {
                let v = close_val(&c.env, &v);
                set_env(c, x, v);
                decls = (*d).clone();
                continue;
            }
            Decls::Fn(x,_,e,d) => {
                match e {
                    // If the expression is a host function, do not introduce a fix expression.
                    Exp::HostFn(_) => {
                        let fnv = Val::ThunkAnon(Rc::new(e));
                        let v = close_val(&c.env, &fnv);
                        set_env(c, x, v);
                        decls = (*d).clone();                        
                        continue;
                    },
                    _ => {
                        let fnv = Val::ThunkAnon(Rc::new(Exp::Fix(x.clone(),Rc::new(e))));
                        let v = close_val(&c.env, &fnv);
                        set_env(c, x, v);
                        decls = (*d).clone();                        
                        continue;
                    }
                }
            }
        }
    }
}
// do a let-like thing
fn produce_value(c:&mut Config,
                 v:RtVal)
                 -> Result<(),StepError>
{
    if c.stk.is_empty() {
        Err(StepError::Halt(
            ExpTerm::Ret(v)))
    }
    else {
        if c.sys.verbose {
            debug_ret(c, &v);
            db_region_close!();
        };
        let fr = c.stk.pop().unwrap();
        match fr.cont {
            Cont::Let(x, e) => {
                c.env = fr.env;
                set_env(c, x, v);
                c.exp = e;
                Ok(())
            }
            _ => stuck_err(Stuck::RetNonLetCont),
        }
    }
}
// do a lambda-like thing
fn consume_value(c:&mut Config,
                 restore_env:Option<EnvRec>,
                 x:Var, e:Rc<Exp>)
                 -> Result<(),StepError>
{
    if c.stk.is_empty() {
        Err(StepError::Halt(
            ExpTerm::Lam(restore_env.unwrap_or(env_emp()), x, e)))
    }
    else { match c.stk.pop().unwrap().cont {
        Cont::App(v) => {
            set_env(c, x, v);
            if let Some(env) = restore_env {
                c.env = env;
            };
            continue_rec(c, e)
        }
        _ => stuck_err(Stuck::LamNonAppCont),
    }}
}
// do a lambda-like thing
fn do_hostevalfn(c:&mut Config,
                 hef:HostEvalFn,
                 mut args:Vec<RtVal>) -> Result<(),StepError>
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
            _ => return stuck_err(Stuck::HostEvalFnNonAppCont),
        }
    }
}
// continue by updating the next expression to run
fn continue_rec(c:&mut Config, e:Rc<Exp>) -> Result<(),StepError> {
    set_exp(c, e);
    Ok(())
}
// continue reduction by using a terminal expression and its reduction context
fn continue_te(c:&mut Config, te:ExpTerm) -> Result<(),StepError> {
    match te {
        ExpTerm::Ret(v) => produce_value(c, v),
        ExpTerm::Lam(env,x,e) => consume_value(c,Some(env),x,e),
        ExpTerm::HostFn(hef, args) => do_hostevalfn(c,hef,args)
    }
}

pub fn system_config() -> SysCfg {
    SysCfg{
        verbose: {
            match std_env::var("FUNGI_VERBOSE_REDUCE") {
                Ok(ref s) if s == "1" => true,
                _ => false
            }
        }
    }
}

pub fn reduce_db(stk:Vec<Frame>, env:EnvRec, exp:Exp) -> ExpTerm {
    use db;
    let sys = system_config();
    let seam_count = db::seam_count_bump();
    if sys.verbose {
        fgi_db!("{}seam-{} {}",
                vt100::SeamBegin{}, seam_count,
                vt100::SeamLineBegin{}); // TODO add a counter
        fgi_db!("{}fungi_lang::reduce{}::reduce {}{}",
                vt100::FgiReduceEngine{}, vt100::Kw{},
                vt100::Exp{}, util::display_truncate(&exp));
        db_region_open!(true, vt100::SeamEnterBracket);
    };
    let t = reduce(&sys, stk, env, exp);
    if sys.verbose {
        db_region_close!();
        fgi_db!("{}halt: {}{}",
                vt100::Lo{},                            
                vt100::ExpTerm{}, util::display_truncate(&t));        
        fgi_db!("{}seam-{} {}",
                vt100::SeamEnd{}, seam_count,
                vt100::SeamLineEnd{}); // TODO add a counter
    };
    return t
}

/// Perform reduction steps (via `step`) until irreducible.
///
/// Reduces the current configuration until it is irreducible.  This
/// process will (generally) both push and pop the configuration's
/// stack; it will entirely consume the initial stack frames, if any,
/// before returning control.
///
pub fn reduce(sys:&SysCfg, stk:Vec<Frame>, env:EnvRec, exp:Exp) -> ExpTerm {
    let mut c = Config{
        sys:sys.clone(),
        stk:stk,
        env:env,
        exp:exp
    };
    loop {
        match step(&mut c) {
            Err(StepError::Halt(t)) => return t,
            Ok(()) => continue,
            Err(err) => panic!("{:?}", err),
        }
    }
}

/// Perform a single small-step reduction.
///
/// In the given reduction configuation, reduce the current expression
/// by one step.
///
pub fn step(c:&mut Config) -> Result<(),StepError> {
    if c.sys.verbose {
        fgi_db!("{}step: {}{}",
                vt100::Lo{},
                vt100::Exp{}, util::display_truncate(&c.exp))
    };
    match c.exp.clone() {
        Exp::DefType(_, _, e)  |
        Exp::AnnoC(e, _)       |
        Exp::AnnoE(e, _)       |
        Exp::IdxApp(e, _)    => {
            continue_rec(c, e)
        }
        Exp::Decls(d, e) => {
            update_env_with_decls(c, (*d).clone());
            continue_rec(c, e)
        }
        Exp::UseAll(m, e) => {
            use_all(c, m);
            continue_rec(c, e)            
        }        
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
            if c.sys.verbose {
                fgi_db!("{}let {}{} {}= {}...",
                        vt100::Kw{}, vt100::ValVar{}, x,
                        vt100::VDash{}, vt100::Exp{}
                );
                db_region_open!();
            }
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
        Exp::RefAnon(v) => {
            let v = close_val(&c.env, &v);
            let r = engine::put(v);
            produce_value(c, RtVal::Ref(r))
        }
        Exp::Ref(v1, v2) => {
            match close_val(&c.env, &v1) {
                RtVal::Name(n) => { // create engine ref named n, holding v2
                    let n = engine_name_of_ast_name(n);
                    let cv2 = close_val(&c.env, &v2);
                    let r = engine::cell(n, cv2);
                    let rv = RtVal::Ref(r);
                    if c.sys.verbose {
                        fgi_db!("{}adapton::engine{}::{}ref{}({}{}{}, {}{}{}) {}~~> {}{}",
                                vt100::AdaptonEngine{}, vt100::PathSep{}, vt100::Kw{},
                                vt100::ParamBegin{},
                                vt100::Val{}, v1,
                                vt100::ParamSep{},
                                vt100::Val{}, v2,
                                vt100::ParamEnd{},
                                vt100::BigStep{},
                                vt100::RtVal{}, rv);
                    }
                    produce_value(c, rv)
                },
                _ => stuck_err(Stuck::RefNonName)
            }
        }
        Exp::Get(v) => {
            match close_val(&c.env, &v) {
                RtVal::Ref(a) => {
                    let v = engine::force(&a);
                    produce_value(c, v)
                },
                _ => stuck_err(Stuck::GetNonRef)
            }
        }
        Exp::Force(v) => {
            match close_val(&c.env, &v) {
                RtVal::Thunk(a) => {
                    if c.sys.verbose {
                        fgi_db!("{}adapton::engine{}::{}force {}{}",
                                vt100::AdaptonEngine{}, vt100::PathSep{}, vt100::Kw{},
                                vt100::Val{}, v);
                    }
                    let te = engine::force(&a);
                    continue_te(c, te)
                },
                RtVal::ThunkAnon(env, e) => {
                    c.env = env;
                    continue_rec(c, Rc::new(e))
                }
                _ => stuck_err(Stuck::ForceNonThunk)
            }
        }
        
        Exp::Split(v, x, y, e1) => {
            match close_val(&c.env, &v) {
                RtVal::Pair(v1, v2) => {
                    set_env_rec(c, x, v1);
                    set_env_rec(c, y, v2);
                    continue_rec(c, e1)
                },
                _ => stuck_err(Stuck::SplitNonPair)
            }
        }
        Exp::IfThenElse(v, e1, e2) => {
            match close_val(&c.env, &v) {
                RtVal::Bool(b) => {
                    if b { continue_rec(c, e1) }
                    else { continue_rec(c, e2) }
                }
                _ => stuck_err(Stuck::IfNonBool)
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
                _ => stuck_err(Stuck::CaseNonInj)
            }
        }
        Exp::Unroll(v, x, e1) => {
            match close_val(&c.env, &v) {
                RtVal::Roll(v) => {
                    set_env_rec(c, x, v);
                    continue_rec(c, e1)
                },
                v => {
                    // XXX: Sometimes, we may "unroll" earlier?
                    set_env(c, x, v);
                    continue_rec(c, e1)
                }
            }
        }
        Exp::Unpack(_i, x, v, e1) => {
            match close_val(&c.env, &v) {
                RtVal::Pack(v) => {
                    set_env_rec(c, x, v);
                    continue_rec(c, e1)
                },
                _ => stuck_err(Stuck::UnpackNonPack)
            }                
        }
        Exp::Thunk(v, e1) => {
            match close_val(&c.env, &v) {
                RtVal::Name(n) => { // create engine thunk named n
                    // suspending evaluation of expression e1:
                    let n = Some(engine_name_of_ast_name(n));
                    let t = thunk!([n]? reduce_db ;
                                   stk:vec![],
                                   env:c.env.clone(),
                                   exp:(*e1).clone()
                    );
                    produce_value(c, RtVal::Thunk(t))
                },
                _ => stuck_err(Stuck::ThunkNonName)
            }
        }
        Exp::Doc(doc, e) => {
            debug_doc(c, &doc);
            engine::reflect_dcg::debug_effect(None, Some(doc));
            continue_rec(c, e)            
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
                _ => stuck_err(Stuck::NameBin)
            }
        }
        Exp::WriteScope(v, e1) => {
            if c.sys.verbose {
                fgi_db!("{}ws {}{} {}{{ {}... {}}}",
                        vt100::Kw{},
                        vt100::Val{}, v,
                        vt100::ParamBegin{}, vt100::Exp{}, vt100::ParamEnd{}
                );
                db_region_open!();
            };
            match close_val(&c.env, &v) {
                RtVal::Name(n) => {
                    let ns_name = engine_name_of_ast_name(n);
                    let te = engine::ns(ns_name, ||{
                        reduce(&c.sys, vec![],
                               c.env.clone(),
                               (*e1).clone())
                    });
                    if c.sys.verbose {
                        db_region_close!();
                    }
                    continue_te(c, te)
                },                                    
                RtVal::NameFn(n) =>
                    match proj_namespace_name(nametm_eval(n)) {
                        None => stuck_err(Stuck::WriteScope),
                        Some(n) => {
                            match nametm_eval(n) {
                                NameTmVal::Name(n) => {
                                    let ns_name = engine_name_of_ast_name(n);
                                    let te = engine::ns(ns_name, ||{
                                        reduce(&c.sys, vec![],
                                               c.env.clone(),
                                               (*e1).clone())
                                    });
                                    if c.sys.verbose {
                                        db_region_close!();
                                    }
                                    continue_te(c, te)
                                },                                    
                                _ => stuck_err(Stuck::WriteScope),
                            }
                        }
                    },
                _ => stuck_err(Stuck::WriteScope),
            }
        }
        Exp::NameFnApp(v1, v2) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                ( RtVal::NameFn(nf), RtVal::Name(n) ) => {
                    match nametm_eval(NameTm::App(Rc::new(nf),
                                                  Rc::new(NameTm::Name(n)))) {
                        NameTmVal::Name(n) =>
                            continue_te(c, ExpTerm::Ret(RtVal::Name(n))),
                        _ => stuck_err(Stuck::NameFnApp),
                    }
                },
                _ => stuck_err(Stuck::NameFnApp),
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
                _ => stuck_err(Stuck::NatPrim)
            }
        }        
        Exp::PrimApp(PrimApp::NatEq(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    produce_value(c, RtVal::Bool(n1 == n2))
                },
                _ => stuck_err(Stuck::NatPrim)
            }
        }
        Exp::PrimApp(PrimApp::NatLt(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    produce_value(c, RtVal::Bool(n1 < n2))
                },
                _ => stuck_err(Stuck::NatPrim)
            }
        }
        Exp::PrimApp(PrimApp::NatLte(v1,v2)) => {
            match (close_val(&c.env, &v1), close_val(&c.env, &v2)) {
                (RtVal::Nat(n1),RtVal::Nat(n2)) => {
                    produce_value(c, RtVal::Bool(n1 <= n2))
                },
                _  => stuck_err(Stuck::NatPrim)
            }
        }
        Exp::PrimApp(PrimApp::RefThunk(v)) => {
            fn val_of_retval (et:ExpTerm) -> RtVal {
                match et {
                    ExpTerm::Ret(v) => v,
                    et => unreachable!("expected ExpTerm::Ret(_), but instead got: `{:?}`", et)
                }
            };
            match close_val(&c.env, &v) {
                RtVal::Thunk(a) => {
                    let r = engine::thunk_map(a, Rc::new(val_of_retval));
                    if c.sys.verbose {
                        fgi_db!("{}adapton::engine{}::{}force {}{}",
                                vt100::AdaptonEngine{}, vt100::PathSep{}, vt100::Kw{},
                                vt100::Val{}, v);
                    }
                    //db_region_open!();
                    let v = engine::force(&r);
                    //db_region_close!();
                    continue_te(c, ExpTerm::Ret(
                        RtVal::Pair(Rc::new(RtVal::Ref(r)),
                                    Rc::new(v))))
                },
                _ => stuck_err(Stuck::RefThunkNonThunk)
            }
        }
    }
}

//////////////////////////////////////////////////////////////////////
// Pretty VT100-style Debugging output
// (Enable with `export FUNGI_VERBOSE_REDUCE=1` at shell)
//////////////////////////////////////////////////////////////////////
use util;

fn debug_doc(c:&mut Config, s:&String) {
    if c.sys.verbose {
        fgi_db!("{}# {}",
                vt100::DocOut{}, s)
    }
}
// fn debug_set_exp(c:&mut Config, e:&Rc<Exp>) {
//     if c.sys.verbose {
//         fgi_db!("{}set_exp: {}{}",
//                 vt100::Lo{},
//                 vt100::Exp{}, util::display_truncate(e))
//     }    
// }
fn debug_bind(c:&mut Config, x:&Var, v:&RtVal) {
    if c.sys.verbose {
        fgi_db!("{}bind: {}{} {}:= {}{}",
                vt100::Lo{},
                vt100::ValVar{}, x,
                vt100::VDash,
                vt100::RtVal{}, util::display_truncate(v))
    }
}

fn debug_ret(c:&mut Config, v:&RtVal) {
    if c.sys.verbose {
        fgi_db!("{} ret: {}{}",
                vt100::Lo{},
                vt100::RtVal{}, util::display_truncate(v))
    }
}
