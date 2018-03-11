//! Visualization of ASTs, typings, evaluation, etc.

use std::rc::Rc;

use ast::{Name, Exp, Val, PrimApp};
use bitype;
use eval;
use adapton::reflect;
use adapton::engine::manage;

use std::fs::File;
use std::io::Write;

pub fn label_exp(e: Exp, ct: &mut usize) -> Exp {
    rewrite_exp(&e, ct)
}

fn rewrite_exp_rec(e: &Rc<Exp>, ct: &mut usize) -> Rc<Exp> {
    Rc::new(rewrite_exp(&**e, ct))
}

fn rewrite_val_rec(v: &Rc<Val>, ct: &mut usize) -> Rc<Val> {
    Rc::new(rewrite_val(&**v, ct))
}

fn rewrite_exp(exp: &Exp, ct: &mut usize) -> Exp {
    let new_exp = match *exp {
        Exp::AnnoC(ref e, ref t) => Exp::AnnoC(rewrite_exp_rec(e, ct), t.clone()),
        Exp::AnnoE(ref e, ref t) => Exp::AnnoE(rewrite_exp_rec(e, ct), t.clone()),
        Exp::Force(ref v) => Exp::Force(rewrite_val(v, ct)),
        Exp::Thunk(ref v, ref e) => Exp::Thunk(rewrite_val(v, ct), rewrite_exp_rec(e, ct)),
        Exp::Unroll(ref v, ref s, ref e) => Exp::Unroll(rewrite_val(v, ct), s.clone(), rewrite_exp_rec(e, ct)),
        Exp::Fix(ref s, ref e) => Exp::Fix(s.clone(), rewrite_exp_rec(e, ct)),
        Exp::Ret(ref v) => Exp::Ret(rewrite_val(v, ct)),
        Exp::DefType(ref s, ref t, ref e) => Exp::DefType(s.clone(), t.clone(), rewrite_exp_rec(e, ct)),
        Exp::Let(ref s, ref e1, ref e2) => Exp::Let(s.clone(), rewrite_exp_rec(e1, ct), rewrite_exp_rec(e2, ct)),
        Exp::Lam(ref s, ref e) => Exp::Lam(s.clone(), rewrite_exp_rec(e, ct)),
        Exp::HostFn(ref hef) => Exp::HostFn(hef.clone()), // <-- no rewrites; no internal structure
        Exp::App(ref e, ref v) => Exp::App(rewrite_exp_rec(e, ct), rewrite_val(v, ct)),
        Exp::Split(ref v, ref s1, ref s2, ref e) => Exp::Split(rewrite_val(v, ct), s1.clone(), s2.clone(), rewrite_exp_rec(e, ct)),
        Exp::Case(ref v, ref s1, ref e1, ref s2, ref e2) => Exp::Case(rewrite_val(v, ct), s1.clone(), rewrite_exp_rec(e1, ct), s2.clone(), rewrite_exp_rec(e2, ct)),
        Exp::IfThenElse(ref v, ref e1, ref e2) => Exp::IfThenElse(rewrite_val(v, ct), rewrite_exp_rec(e1, ct), rewrite_exp_rec(e2, ct)),
        Exp::Ref(ref v1, ref v2) => Exp::Ref(rewrite_val(v1, ct), rewrite_val(v2, ct)),
        Exp::Get(ref v) => Exp::Get(rewrite_val(v, ct)),
        Exp::WriteScope(ref v, ref e) => Exp::WriteScope(rewrite_val(v, ct), rewrite_exp_rec(e, ct)),
        Exp::NameFnApp(ref v1, ref v2) => Exp::NameFnApp(rewrite_val(v1, ct), rewrite_val(v2, ct)),
        Exp::PrimApp(ref p) => Exp::PrimApp(rewrite_prim_app(p, ct)),
        Exp::DebugLabel(ref on, ref s, ref e) => Exp::DebugLabel(on.clone(), s.clone(), rewrite_exp_rec(e, ct)),
        ref e => e.clone(),
    };
    *ct += 1;
    Exp::DebugLabel(Some(Name::Num(*ct)), None, Rc::new(new_exp))
}

fn rewrite_val(val: &Val, ct: &mut usize) -> Val {
    match *val {
        Val::Pair(ref v1, ref v2) => Val::Pair(rewrite_val_rec(v1, ct), rewrite_val_rec(v2, ct)),
        Val::Inj1(ref v) => Val::Inj1(rewrite_val_rec(v, ct)),
        Val::Inj2(ref v) => Val::Inj2(rewrite_val_rec(v, ct)),
        Val::Roll(ref v) => Val::Roll(rewrite_val_rec(v, ct)),
        Val::Anno(ref v, ref t) => Val::Anno(rewrite_val_rec(v, ct), t.clone()),
        Val::ThunkAnon(ref e) => Val::ThunkAnon(rewrite_exp_rec(e, ct)),
        ref v => v.clone(),
    }
}

fn rewrite_prim_app(prim: &PrimApp, ct: &mut usize) -> PrimApp {
    match *prim {
        PrimApp::NatLte(ref v1, ref v2) => PrimApp::NatLte(rewrite_val(v1, ct), rewrite_val(v2, ct)),
        PrimApp::NatLt(ref v1, ref v2) => PrimApp::NatLt(rewrite_val(v1, ct), rewrite_val(v2, ct)),
        PrimApp::NatEq(ref v1, ref v2) => PrimApp::NatEq(rewrite_val(v1, ct), rewrite_val(v2, ct)),
        PrimApp::NatPlus(ref v1, ref v2) => PrimApp::NatPlus(rewrite_val(v1, ct), rewrite_val(v2, ct)),
        PrimApp::NameBin(ref v1, ref v2) => PrimApp::NameBin(rewrite_val(v1, ct), rewrite_val(v2, ct)),
        PrimApp::RefThunk(ref v) => PrimApp::RefThunk(rewrite_val(v, ct)),
    }
}

#[derive(Clone,Debug)]
pub struct Bundle {
    pub input: String,
    pub program: bitype::ExpDer,
    pub traces: Vec<reflect::trace::Trace>,
}

impl Bundle {
    pub fn exp_rule(&self) -> bitype::ExpRule {
        (*self.program.rule).clone()
    }
}

#[macro_export]
macro_rules! fgi_bundle {
    [$($e:tt)+] => {{
        let exp = label_exp(fgi_exp![$($e)+], &mut 0);
        let program = synth_exp(&Ext::empty(), &Ctx::Empty, &exp);
        // let (term, traces) = capture_traces(move || eval(vec![], exp));
        Bundle {
            input: stringify!($($e)+).to_owned(),
            program: program,
            // traces: traces,
            traces: vec![],
        }
    }}
}

/// Fungi program listing that we test.
///
/// These program listings give, e.g., tutorial examples or examples
/// from technical reports.
///
/// Under the hood, this macro creates a helper function that runs in
/// a separate thread and returns whether the given Fungi program
/// listing parses and type checks.
///
#[macro_export]
macro_rules! fgi_listing_test {
    [$($e:tt)+] => {{
        fn help() -> Result<(),String> {
            use std::rc::Rc;
            use ast::*;
            use bitype::*;
            use vis::*;        
            let bundle : Bundle = fgi_bundle![
                $($e)+
            ];
            let path = format!("target/{}.fgb", module_path!());
            write_bundle(path.as_str(), &bundle);
            match bundle.program.clas {
                Ok(_)    => { return Ok(()) },                           
                Err(err) => { Err(format!("{:?}", err)) }
            }
        };
        use std::thread;
        let child =
            thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || {
                help()
            });
        assert!(child.unwrap().join().unwrap().is_ok());
    }}
}

pub fn capture_traces<F>(f: F) -> (eval::ExpTerm, Vec<reflect::trace::Trace>)
where F: FnOnce() -> eval::ExpTerm {
    manage::init_dcg();
    
    reflect::dcg_reflect_begin();
    let term = f();
    let traces = reflect::dcg_reflect_end();
    (term, traces)
}

pub fn write_bundle(filename: &str, bundle: &Bundle) {
    let data = format!("{:?}", bundle);
    let mut f = File::create(filename).expect("Could not create bundle file");
    f.write_all(data.as_bytes()).expect("Could not write bundle data");
    f.flush().expect("Could not flush");
}
