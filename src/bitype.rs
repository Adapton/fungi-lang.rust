use ast::*;
use std::rc::Rc;

// Move this to the enum definition?
impl TCtxt {
    pub fn lookup_var(&self, x:Var) -> Option<Type> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Var(ref c,ref v,ref t) => {
                if x == *v { Some(t.clone()) } else { c.lookup_var(x) }
            },
            TCtxt::Cell(ref c,_,_)
            | TCtxt::Thunk(ref c,_,_) => { c.lookup_var(x) },
        }
    }
    pub fn lookup_cell(&self, p:Pointer) -> Option<Type> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Cell(ref c,ref ptr,ref t) => {
                if p == *ptr { Some(t.clone()) } else { c.lookup_cell(p) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::Thunk(ref c,_,_) => { c.lookup_cell(p) },
        }
    }
    pub fn lookup_thunk(&self, p:Pointer) -> Option<CType> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Thunk(ref c,ref ptr,ref t) => {
                if p == *ptr { Some(t.clone()) } else { c.lookup_thunk(p) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::Cell(ref c,_,_) => { c.lookup_thunk(p) },
        }
    }
}

pub fn synth_val(ctxt: TCtxt, v:Val) -> Option<Type> {
    match v {
        Val::Anno(val,t) => {
            if check_val(ctxt, (*val).clone(), t.clone()) {
                Some(t)
            } else { None }
        },
        Val::Var(var) => { ctxt.lookup_var(var) },
        _ => None,
    }
}

pub fn check_val(ctxt: TCtxt, v:Val, t:Type) -> bool {
    match (v,t) {
        (Val::Unit, Type::Unit) => true,
        (Val::Pair(v1,v2), Type::Pair(t1,t2)) => {
            check_val(ctxt.clone(), (*v1).clone(), (*t1).clone() )
            & check_val(ctxt, (*v2).clone(), (*t2).clone() )
        },
        (Val::Injl(v), Type::Sum(t1,_)) => {
            check_val(ctxt, (*v).clone(), (*t1).clone() )
        },
        (Val::Injr(v), Type::Sum(_,t2)) => {
            check_val(ctxt, (*v).clone(), (*t2).clone() )
        },
        (Val::Ref(p), Type::Ref(t1)) => {
            if let Some(t2) = ctxt.lookup_cell(p) {
                *t1 == t2
            } else { false }
        },
        (Val::Thunk(p), Type::U(ct)) => {
            if let Some(t) = ctxt.lookup_thunk(p) {
                *ct == t
            } else { false }
        },
        (v,t2) => {
            if let Some(t1) = synth_val(ctxt, v) {
                t2 == t1
            } else { false }
        },
    }
}

pub fn synth_exp(ctxt: TCtxt, e:Exp) -> Option<CType> {
    match e {
        Exp::Anno(e,ct) => {
            if check_exp(ctxt, (*e).clone(), ct.clone()) {
                Some(ct)
            } else { None }
        },
        Exp::App(e,v) => {
            if let Some(CType::Arrow(t,ct)) = synth_exp(ctxt.clone(), (*e).clone()) {
                if check_val(ctxt, v, (*t).clone()) {
                    Some((*ct).clone())
                } else { None }
            } else { None }
        },
        Exp::Force(v) => {
            if let Some(Type::U(ct)) = synth_val(ctxt,v) {
                Some((*ct).clone())
            } else { None }
        },
        Exp::Get(v) => {
            if let Some(Type::Ref(t)) = synth_val(ctxt,v) {
                Some(CType::F(t.clone()))
            } else { None }
        },
        Exp::PrimApp(PrimApp::SeqFoldSeq(seq, accum, body)) => {
            /* 
            Ctx |- v_seq ==> Seq(A)
            Ctx |- v_accum ==> B
            Ctx |- e_body <== (A -> B -> F(B))
            ----------------------------------------------------- :: synth-seq-fold-seq
            Ctx |- seq_fold_seq(v_seq, v_accum, e_body) ==> F(B)
            */
            if let Some(Type::PrimApp(PrimTyApp::Seq(st))) = synth_val(ctxt.clone(),seq) {
                if let Some(at) = synth_val(ctxt.clone(),accum) {
                    let bt = CType::Arrow(st,Rc::new(CType::Arrow(
                        Rc::new(at.clone()),
                        Rc::new(CType::F(Rc::new(at.clone())))
                    )));
                    if check_exp(ctxt,(*body).clone(),bt) {
                        Some(CType::F(Rc::new(at)))
                    } else { None }
                } else { None }
            } else { None }
        },
        _ => None,
    }
}

pub fn check_exp(ctxt: TCtxt, e:Exp, ct:CType) -> bool {
    match (e,ct) {
        (Exp::Thunk(e), CType::F(t)) => {
            if let Type::U(ct) = (*t).clone() {
                check_exp(ctxt, (*e).clone(), (*ct).clone())
            } else { false }
        },
        (Exp::Ret(v), CType::F(t)) => {
            check_val(ctxt, v, (*t).clone())
        },
        (Exp::Let(x,e1,e2), ct) => {
            if let Some(CType::F(t)) = synth_exp(ctxt.clone(),(*e1).clone()) {
                check_exp(ctxt.var(x,(*t).clone()),(*e2).clone(),ct)
            } else { false }
        },
        (Exp::Lam(x, e), CType::Arrow(t,ct)) => {
            check_exp(ctxt.var(x,(*t).clone()),(*e).clone(),(*ct).clone())
        },
        (Exp::Split(v, x1, x2, e), ct) => {
            if let Some(Type::Pair(t1,t2)) = synth_val(ctxt.clone(),v) {
                let t1 = (*t1).clone();
                let t2 = (*t2).clone();
                check_exp(ctxt.var(x1,t1).var(x2,t2),(*e).clone(),ct)
            } else { false }
        },
        (Exp::Case(v, x1, e1, x2, e2), ct) => {
            if let Some(Type::Sum(t1,t2)) = synth_val(ctxt.clone(),v) {
                let t1 = (*t1).clone();
                let t2 = (*t2).clone();
                check_exp(ctxt.clone().var(x1,t1),(*e1).clone(),ct.clone())
                & check_exp(ctxt.var(x2,t2),(*e2).clone(),ct)
            } else { false }
        },
        (Exp::Ref(v), CType::F(t)) => {
            check_val(ctxt,v,(*t).clone())
        },
        (Exp::Name(_,e), ct) => {
            check_exp(ctxt,(*e).clone(),ct)
        },
        (Exp::PrimApp(PrimApp::SeqFoldSeq(seq, accum, body)), ct) => {
            /* 
            Ctx |- v_seq ==> Seq(A)
            Ctx |- v_accum <== B
            Ctx |- e_body <== (A -> B -> F B)
            ----------------------------------------------------- :: check-seq-fold-seq
            Ctx |- seq_fold_seq(v_list, v_accum, e_body) <== F B
            */
            if let CType::F(at) = ct {
                if let Some(Type::PrimApp(PrimTyApp::Seq(st))) = synth_val(ctxt.clone(),seq) {
                    if check_val(ctxt.clone(),accum,(*at).clone()) {
                        let bt = CType::Arrow(st,Rc::new(CType::Arrow(
                            at.clone(), Rc::new(CType::F(at))
                        )));
                        check_exp(ctxt,(*body).clone(),bt)
                    } else { false }
                } else { false }
            } else { false }
        },
        (Exp::Fix(f,e),ct) => {
            /*
            Ctx, f: U(C) |- e <== C
            -----------------------
            Ctx |- fix(f.e) <== C
            */
            check_exp(ctxt.var(f,Type::U(Rc::new(ct.clone()))),(*e).clone(),ct)
        },
        (e,ct2) => {
            if let Some(ct1) = synth_exp(ctxt, e) {
                ct2 == ct1
            } else { false }
        },
    }
}
