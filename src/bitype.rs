use ast::*;

pub fn lookup_type(ctxt: &TCtxt, x:Var) -> Option<Type> {
    match *ctxt {
        TCtxt::Empty => None,
        TCtxt::Val(ref c,ref v,ref t) => {
            if x == *v { Some(t.clone()) } else { lookup_type(c,x) }
        },
        TCtxt::Cell(ref c,_,_)
        | TCtxt::Thunk(ref c,_,_) => { lookup_type(c,x) },
    }
}

pub fn lookup_cell(ctxt: &TCtxt, p:Pointer) -> Option<Type> {
    match *ctxt {
        TCtxt::Empty => None,
        TCtxt::Cell(ref c,ref ptr,ref t) => {
            if p == *ptr { Some(t.clone()) } else { lookup_cell(c,p) }
        },
        TCtxt::Val(ref c,_,_)
        | TCtxt::Thunk(ref c,_,_) => { lookup_cell(c,p) },
    }
}

pub fn lookup_thunk(ctxt: &TCtxt, p:Pointer) -> Option<CType> {
    match *ctxt {
        TCtxt::Empty => None,
        TCtxt::Thunk(ref c,ref ptr,ref t) => {
            if p == *ptr { Some(t.clone()) } else { lookup_thunk(c,p) }
        },
        TCtxt::Val(ref c,_,_)
        | TCtxt::Cell(ref c,_,_) => { lookup_thunk(c,p) },
    }
}

pub fn synth_val(ctxt: &TCtxt, v:Val) -> Option<Type> {
    match v {
        Val::Var(var) => { lookup_type(ctxt, var) },
        Val::Anno(val,t) => {
            if check_val(ctxt, (*val).clone(), t.clone()) { Some(t) } else { None }
        },
        _ => None,
    }
}

pub fn check_val(ctxt: &TCtxt, v:Val, t:Type) -> bool {
    match (v,t) {
        (Val::Unit, Type::Unit) => true,
        (Val::Num(_), Type::Num) => true,
        (Val::Str(_), Type::Str) => true,
        (Val::Pair(v1,v2), Type::Pair(t1,t2)) => {
            check_val(&ctxt.clone(), (*v1).clone(), (*t1).clone() )
            & check_val(ctxt, (*v2).clone(), (*t2).clone() )
        },
        (Val::Injl(v), Type::Sum(t1,_)) => {
            check_val(ctxt, (*v).clone(), (*t1).clone() )
        },
        (Val::Injr(v), Type::Sum(_,t2)) => {
            check_val(ctxt, (*v).clone(), (*t2).clone() )
        },
        (Val::Ref(p), Type::Ref(t)) => {
            if let Some(ty) = lookup_cell(ctxt,p) {
                *t == ty
            } else { false }
        },
        (Val::Thunk(p), Type::U(ct)) => {
            if let Some(ty) = lookup_thunk(ctxt,p) {
                *ct == ty
            } else { false }
        },
        (v,t) => {
            if let Some(ty) = synth_val(ctxt, v) {
                t == ty
            } else { false }
        },
    }
}

pub fn synth_exp(ctxt: &TCtxt, e:Exp) -> Option<CType> {
    unimplemented!()
}

pub fn check_exp(ctxt: &TCtxt, e:Exp, t:CType) -> bool {
    unimplemented!()
}