use ast::*;
use std::fmt;
use std::rc::Rc;

// Move this to the enum definition?
impl TCtxt {
    pub fn lookup_var(&self, x:&Var) -> Option<Type> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Var(ref c,ref v,ref t) => {
                if x == v { Some(t.clone()) } else { c.lookup_var(x) }
            },
            TCtxt::Cell(ref c,_,_)
            | TCtxt::Thunk(ref c,_,_) => { c.lookup_var(x) },
        }
    }
    pub fn lookup_cell(&self, ptr:&Pointer) -> Option<Type> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Cell(ref c,ref p,ref t) => {
                if p == ptr { Some(t.clone()) } else { c.lookup_cell(ptr) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::Thunk(ref c,_,_) => { c.lookup_cell(ptr) },
        }
    }
    pub fn lookup_thunk(&self, ptr:&Pointer) -> Option<CType> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Thunk(ref c,ref p,ref t) => {
                if p == ptr { Some(t.clone()) } else { c.lookup_thunk(ptr) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::Cell(ref c,_,_) => { c.lookup_thunk(ptr) },
        }
    }
}

enum TypeError {
    AnnoMism,
    NoSynthRule,
    NoCheckRule,
    InvalidPtr,
    ParamMism,
    ParamNoSynth,
    AppNotArrow,
}
impl fmt::Display for TypeError {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        let s = match *self {
            _ => "TypeError"
        };
        write!(f,"{}",s)
    }
}

fn fail_synth_val(scope:Option<&Name>, err:TypeError, v:&Val) -> Option<Type> {
    None
}

fn fail_check_val(scope:Option<&Name>, err:TypeError, v:&Val) -> bool {
    false
}

fn fail_synth_exp(scope:Option<&Name>, err:TypeError, e:&Exp) -> Option<CType> {
    None
}

fn fail_check_exp(scope:Option<&Name>, err:TypeError, e:&Exp) -> bool {
    false
}

pub fn synth_val(scope:Option<&Name>, ctxt:&TCtxt, val:&Val) -> Option<Type> {
    match val {
        &Val::Anno(ref v,ref t) => {
            if check_val(scope, ctxt, v, t) {
                Some(t.clone())
            } else { fail_synth_val(scope, TypeError::AnnoMism,val) }
        },
        &Val::Var(ref v) => { ctxt.lookup_var(v) },
        // Val::AnnoVar(var,t) => {
        //     if let Some(vt) = ctxt.lookup_var(var) {
        //         if vt == t { Some(t) } else { None }
        //     } else { Some(t) }
        // },
        _ => fail_synth_val(scope, TypeError::NoSynthRule,val),
    }
}

pub fn check_val(scope:Option<&Name>, ctxt:&TCtxt, val:&Val, typ:&Type) -> bool {
    match (val, typ) {
        (&Val::Unit, &Type::Unit) => true,
        (&Val::Pair(ref v1, ref v2), &Type::Pair(ref t1, ref t2)) => {
            check_val(scope, ctxt, v1, t1 )
            & check_val(scope, ctxt, v2, t2 )
        },
        (&Val::Injl(ref v), &Type::Sum(ref t1, _)) => {
            check_val(scope, ctxt, v, t1 )
        },
        (&Val::Injr(ref v), &Type::Sum(_, ref t2)) => {
            check_val(scope, ctxt, v, t2 )
        },
        (&Val::Ref(ref p), &Type::Ref(ref t1)) => {
            if let Some(t2) = ctxt.lookup_cell(p) {
                **t1 == t2
            } else { fail_check_val(scope, TypeError::InvalidPtr,val) }
        },
        (&Val::Thunk(ref p), &Type::U(ref ct)) => {
            if let Some(t) = ctxt.lookup_thunk(p) {
                **ct == t
            } else { fail_check_val(scope, TypeError::InvalidPtr,val) }
        },
        (v, t2) => {
            if let Some(ref t1) = synth_val(scope, ctxt, v) {
                t2 == t1
            } else { fail_check_val(scope, TypeError::NoCheckRule,val) }
        },
    }
}

pub fn synth_exp(scope:Option<&Name>, ctxt:&TCtxt, exp:&Exp) -> Option<CType> {
    match exp {
        &Exp::Name(ref nm, ref e) => {
            synth_exp(Some(nm), ctxt, e)
        }
        &Exp::Anno(ref e, ref ct) => {
            if check_exp(scope, ctxt, e, ct) {
                Some(ct.clone())
            } else { fail_synth_exp(scope, TypeError::AnnoMism, exp) }
        },
        &Exp::App(ref e, ref v) => {
            if let Some(CType::Arrow(t,ct)) = synth_exp(scope, ctxt, e) {
                if check_val(scope, ctxt, v, &t) {
                    Some((*ct).clone())
                } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_synth_exp(scope, TypeError::AppNotArrow, exp) }
        },
        &Exp::Force(ref v) => {
            if let Some(Type::U(ct)) = synth_val(scope, ctxt, v) {
                Some((*ct).clone())
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::Get(ref v) => {
            if let Some(Type::Ref(t)) = synth_val(scope, ctxt, v) {
                Some(CType::F(t))
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::NatAdd(ref n1, ref n2)) => {
            if check_val(scope, ctxt, n1, &Type::PrimApp(PrimTyApp::Nat))
            & check_val(scope, ctxt, n2, &Type::PrimApp(PrimTyApp::Nat)) {
                Some(CType::F(Rc::new(Type::PrimApp(PrimTyApp::Nat))))
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        }
        &Exp::PrimApp(PrimApp::SeqFoldSeq(ref v_seq, ref v_accum, ref e_body)) => {
            /* 
            Ctx |- v_seq ==> Seq(A)
            Ctx |- v_accum ==> B
            Ctx |- e_body <== (A -> B -> F(B))
            ----------------------------------------------------- :: synth-seq-fold-seq
            Ctx |- seq_fold_seq(v_seq, v_accum, e_body) ==> F(B)
            */
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, v_seq) {
                if let Some(b) = synth_val(scope, ctxt, v_accum) {
                    let bt = CType::Arrow(a,Rc::new(CType::Arrow(
                        Rc::new(b.clone()),
                        Rc::new(CType::F(Rc::new(b.clone())))
                    )));
                    if check_exp(scope, ctxt, e_body, &bt) {
                        Some(CType::F(Rc::new(b)))
                    } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
                } else { fail_synth_exp(scope, TypeError::ParamNoSynth, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqFoldUp(ref v_seq, ref v_init, ref e_first, ref e_combine)) => {
            /*
            Ctx |- v_seq ==> Seq(A)
            Ctx |- v_init ==> B
            Ctx |- e_first <== (A -> F(B))
            Ctx |- e_combine <== (B -> B -> F(B))
            --------------------------------- :: synth-seq-fold-up
            Ctx |- seq_fold_up(v_seq, v_init, e_first, e_combine) ==> F(B)
            */
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, v_seq) {
                if let Some(b) = synth_val(scope, ctxt, v_init) {
                    let fa = CType::Arrow(a,Rc::new(
                        CType::F(Rc::new(b.clone()))
                    ));
                    if check_exp(scope, ctxt, e_first, &fa) {
                        let ca = CType::Arrow(Rc::new(b.clone()),Rc::new(CType::Arrow(
                            Rc::new(b.clone()),
                            Rc::new(CType::F(Rc::new(b.clone())))
                        )));
                        if check_exp(scope, ctxt, e_combine, &ca) {
                            Some(CType::F(Rc::new(b)))
                        } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
                    } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
                } else { fail_synth_exp(scope, TypeError::ParamNoSynth, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        _ => fail_synth_exp(scope, TypeError::NoSynthRule, exp),
    }
}

pub fn check_exp(scope:Option<&Name>, ctxt:&TCtxt, exp:&Exp, ctype:&CType) -> bool {
    match (exp, ctype) {
        (&Exp::Name(ref nm, ref e), ct) => {
            check_exp(Some(nm), ctxt, e, ct)
        }
        (&Exp::Thunk(ref e), &CType::F(ref t)) => {
            if let Type::U(ref ct) = **t {
                check_exp(scope, ctxt, e, ct)
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::Ret(ref v), &CType::F(ref t)) => {
            check_val(scope, ctxt, v, t)
        },
        (&Exp::Let(ref x, ref e1, ref e2), ct) => {
            if let Some(CType::F(t)) = synth_exp(scope, ctxt, e1) {
                check_exp(scope, &ctxt.var(x.clone(), (*t).clone()), e2, ct)
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::Lam(ref x, ref e), &CType::Arrow(ref t, ref ct)) => {
            check_exp(scope, &ctxt.var(x.clone(),(**t).clone()), e, ct)
        },
        (&Exp::Split(ref v, ref x1, ref x2, ref e), ct) => {
            if let Some(Type::Pair(t1, t2)) = synth_val(scope, ctxt, v) {
                let t1 = (*t1).clone();
                let t2 = (*t2).clone();
                check_exp(scope, &ctxt.var(x1.clone(),t1).var(x2.clone(),t2), e, ct)
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2), ct) => {
            if let Some(Type::Sum(t1, t2)) = synth_val(scope, ctxt, v) {
                let t1 = (*t1).clone();
                let t2 = (*t2).clone();
                check_exp(scope, &ctxt.var(x1.clone(),t1), e1, ct)
                & check_exp(scope, &ctxt.var(x2.clone(),t2), e2, ct)
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::Ref(ref v), &CType::F(ref t)) => {
            if let Type::Ref(ref t) = **t {
                check_val(scope, ctxt, v, t)
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::PrimApp(PrimApp::SeqFoldSeq(ref v_seq, ref v_accum, ref e_body)), ct) => {
            /* 
            Ctx |- v_seq ==> Seq(A)
            Ctx |- v_accum <== B
            Ctx |- e_body <== (A -> B -> F B)
            ----------------------------------------------------- :: check-seq-fold-seq
            Ctx |- seq_fold_seq(v_list, v_accum, e_body) <== F B
            */
            if let CType::F(ref b) = *ct {
                if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, v_seq) {
                    if check_val(scope, ctxt, v_accum, b) {
                        let bt = CType::Arrow(a,Rc::new(CType::Arrow(
                            b.clone(), Rc::new(CType::F(b.clone()))
                        )));
                        check_exp(scope, ctxt, e_body, &bt)
                    } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
                } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::Fix(ref f, ref e), ct) => {
            /*
            Ctx, f: U(C) |- e <== C
            -----------------------
            Ctx |- fix(f.e) <== C
            */
            check_exp(scope, &ctxt.var(f.clone(), Type::U(Rc::new(ct.clone()))), e, ct)
        },
        (e, ct2) => {
            if let Some(ref ct1) = synth_exp(scope, ctxt, e) {
                ct2 == ct1
            } else { fail_check_exp(scope, TypeError::NoSynthRule, exp) }
        },
    }
}
