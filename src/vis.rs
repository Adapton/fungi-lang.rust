//! Visualization of ASTs, typings, evaluation, etc.

use shared::Shared;
use std::rc::Rc;

use ast::{Name, Exp, Val, PrimApp, UseAllModule, Module, Decls};
use bitype;
use dynamics;
use adapton::reflect;
use adapton::engine::manage;

use std::fs::File;
use std::io::Write;

// use serde_json;

pub fn label_exp(e: Exp, ct: &mut usize) -> Exp {
    rewrite_exp(&e, ct)
}

fn rewrite_exp_rec(e: &Rc<Exp>, ct: &mut usize) -> Rc<Exp> {
    Rc::new(rewrite_exp(&**e, ct))
}

fn rewrite_val_rec(v: &Rc<Val>, ct: &mut usize) -> Rc<Val> {
    Rc::new(rewrite_val(&**v, ct))
}

fn rewrite_decls_rec(d: &Rc<Decls>, ct: &mut usize) -> Rc<Decls> {
    Rc::new(rewrite_decls(&**d, ct))
}

fn rewrite_useall(useall: &UseAllModule, ct: &mut usize) -> UseAllModule {
    let mut u = useall.clone();
    u.module = Shared::new(rewrite_module(&*u.module, ct));
    u
}

fn rewrite_module(module: &Module, ct: &mut usize) -> Module {
    let mut m = module.clone();
    m.decls = rewrite_decls(&m.decls, ct);
    m
}

fn rewrite_decls(decls: &Decls, ct: &mut usize) -> Decls {
    match *decls {
        Decls::UseAll(ref u, ref d) => Decls::UseAll(rewrite_useall(u, ct), rewrite_decls_rec(d, ct)),
        Decls::Doc(ref s, ref d) => Decls::Doc(s.clone(), rewrite_decls_rec(d, ct)),
        Decls::NmTm(ref s, ref n, ref d) => Decls::NmTm(s.clone(), n.clone(), rewrite_decls_rec(d, ct)),
        Decls::IdxTm(ref s, ref i, ref d) => Decls::IdxTm(s.clone(), i.clone(), rewrite_decls_rec(d, ct)),
        Decls::Type(ref s, ref t, ref d) => Decls::Type(s.clone(), t.clone(), rewrite_decls_rec(d, ct)),
        Decls::Val(ref s, ref ot, ref v, ref d) => Decls::Val(s.clone(), ot.clone(), rewrite_val(v, ct), rewrite_decls_rec(d, ct)),
        Decls::Fn(ref s, ref t, ref e, ref d) => Decls::Fn(s.clone(), t.clone(), rewrite_exp(e, ct), rewrite_decls_rec(d, ct)),
        Decls::End => Decls::End,
        Decls::NoParse(ref s) => Decls::NoParse(s.clone()),
    }
}


fn rewrite_exp(exp: &Exp, ct: &mut usize) -> Exp {
    //println!("{}", ct);
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
        Exp::UseAll(ref u, ref e) => Exp::UseAll(rewrite_useall(u, ct), rewrite_exp_rec(e, ct)),
        Exp::Decls(ref d, ref e) => Exp::Decls(Rc::new(rewrite_decls(&*d, ct)), rewrite_exp_rec(e, ct)),
        Exp::Unpack(ref x, ref y, ref v, ref e) => Exp::Unpack(x.clone(), y.clone(), rewrite_val(v, ct), rewrite_exp_rec(e, ct)),
        Exp::IdxApp(ref e, ref i) => Exp::IdxApp(rewrite_exp_rec(e, ct), i.clone()),
        Exp::Unimp => Exp::Unimp,
        Exp::NoParse(ref s) => Exp::NoParse(s.clone()),
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

/// Expectations for examples and tests
#[derive(Clone,Debug)]
pub enum Expect {
    // We expect Fungi to reject the program/test
    Failure,    
    // We expect Fungi to accept the program/test
    Success,
    // We _really_ want the test to have a `Success` outcome, but the test exhibits something that is currently broken in Fungi
    FailurexXXX,
    // We _really_ want the test to have a `Failure` outcome, but the test exhibits something that is currently broken in Fungi
    SuccessxXXX,
}

#[derive(Clone,Debug,Serialize)]
pub struct Bundle {
    pub input: String,
    pub program: bitype::ExpDer,
    // #[serde(with="TraceVecDef")]
    #[serde(skip_serializing)]
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
        // let traces = capture_traces(|| eval::eval(vec![], exp)).1;
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
macro_rules! fgi_listing_expect {
    [ [ $($outcome:tt)+ ] $($e:tt)+ ] => {{
        fn help() -> Result<(),String> {
            use std::rc::Rc;
            use ast::*;
            use bitype::*;
            use vis::*;

            let bundle : Bundle = fgi_bundle![
                $($e)+
            ];

            let filename = format!("target/{}.{}.fgb", filename_of_module_path!(), line!());
            write_bundle(filename.as_str(), &bundle);
            match ($($outcome)+, bundle.program.clas) {
                (Expect::Success,     Ok(_))     => { return Ok(()) },
                (Expect::FailurexXXX, Ok(_))     => { return Ok(()) },
                (Expect::Success,     Err(err))  => { return Err(format!("{:?}", err)) }                
                (Expect::FailurexXXX, Err(err))  => { return Err(format!("Fixed?: {:?}", err)) }

                (Expect::Failure,     Ok(_))     => { return Err(format!("Expected a failure, but did _not_ observe one.")) },
                (Expect::SuccessxXXX, Ok(_))     => { return Err(format!("Fixed?")) }
                (Expect::SuccessxXXX, Err(_err)) => { return Ok(()) }
                (Expect::Failure,     Err(_err)) => { return Ok(()) },
            }
        };
        use std::thread;
        let child =
            thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || {
                help()
            });
        let res = child.unwrap().join();
        println!("Thread join result: {:?}", &res);
        let res = res.unwrap();
        println!("     thread result: {:?}", &res);
        assert!(res.is_ok());
    }}
}

#[macro_export]
macro_rules! fgi_listing_test {
    [ $($e:tt)+ ] => {{
        {
            fgi_listing_expect![ [ Expect::Success ] $($e)+ ]
        }
    }}
}


pub fn capture_traces<F>(f: F) -> (dynamics::ExpTerm, Vec<reflect::trace::Trace>)
where F: FnOnce() -> dynamics::ExpTerm {
    manage::init_dcg();
    
    reflect::dcg_reflect_begin();
    let term = f();
    let traces = reflect::dcg_reflect_end();
    (term, traces)
}

pub fn write_bundle(filename: &str, bundle: &Bundle) {
    let data = format!("{:?}", bundle);
    
    // let mut buffer = vec![];
    // serde_xml_rs::serialize(bundle, &mut buffer).expect("Could not convert bundle to XML");
    
    let mut f = File::create(filename).expect("Could not create bundle file");
    // f.write_all(&buffer[..]).expect("Could not write bundle data");
    f.write_all(data.as_bytes()).expect("Could not write bundle data");
    f.flush().expect("Could not flush bundle output");
}

#[macro_export]
macro_rules! fgi_dynamic_trace {
    { [ $($expect:tt)+ ] $($e:tt)+ } => {{
        use reduce;
        use dynamics;
        use std::rc::Rc;
        use ast::*;
        use adapton::engine;
        
        // --------------------------------------------------------------
        // 1. Parse fungi program (expression) to reduce, and visualize
        // --------------------------------------------------------------
        let e = fgi_exp![ $($e)+ ];

        // --------------------------------------------------------------
        // 2. Run fungi program, and collect its Adapton trace
        // --------------------------------------------------------------
        use html;
        use vis;
        use adapton::reflect;
        use adapton::reflect::trace;
        use std::fs::File;
        use std::io::BufWriter;
        use std::io::Write;
        use html::WriteHTML;
        
        // Initialize Adapton
        engine::manage::init_dcg();
        // Record a debugging trace of Adapton's behavior
        reflect::dcg_reflect_begin();
        // Run our Fungi program:
        let result = {
            let mut lab = 0;
            // Label the sub-expressions of the Fungi program:
            let e = vis::label_exp(e, &mut lab);
            // Run the Fungi program:
            reduce::reduce(vec![], dynamics::env_emp(), e)
        };
        println!("{}:{}: result: {:?}", module_path!(), line!(), result);
        let traces = reflect::dcg_reflect_end();
        let count = trace::trace_count(&traces, None);
        println!("{:?}", count);
        let f = File::create(format!("target/{}.{}.html", filename_of_module_path!(), line!())).unwrap();
        let mut writer = BufWriter::new(f);
        writeln!(writer, "{}", html::style_string()).unwrap();
        writeln!(writer, "<div class=\"traces\">").unwrap();
        for tr in traces {
            html::div_of_trace(&tr).write_html(&mut writer);
        };
        writeln!(writer, "</div>").unwrap();

        // ---------------------------------------------------------------------------
        // 3. Type-check fungi program, and collect a "bundle" for HFI interactions
        // ---------------------------------------------------------------------------
        //
        // TODO: Integrate the trace above into the bundle below, so
        // we can view both, together, in HFI.
        //
        //fgi_listing_expect![ [ $($expect)+ ] $($e)+ ]
    }}
}
