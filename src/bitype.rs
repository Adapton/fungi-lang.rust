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

pub fn synth_val(ctxt: &TCtxt, v:Val) -> Type {
    unimplemented!()
}

pub fn check_val(ctxt: &TCtxt, v:Val, t:Type) -> bool {
    unimplemented!()
}

pub fn synth_exp(ctxt: &TCtxt, e:Exp) -> CType {
    unimplemented!()
}

pub fn check_exp(ctxt: &TCtxt, e:Exp, t:CType) -> bool {
    unimplemented!()
}