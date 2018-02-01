use tgt_ast::*;
use std::fmt;
use std::rc::Rc;

// TODO: Switch to outer linked-list or vector to simplify code
pub type TCtxtRec = Rc<TCtxt>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum TCtxt {
    Empty,
    Var(TCtxtRec,Var,Type),
    IVar(TCtxtRec,Var,Sort),
    TVar(TCtxtRec,Var,Kind),
    TCons(TCtxtRec,TypeCons,Kind),
    Equiv(TCtxtRec,IdxTm,IdxTm,Sort),
    Apart(TCtxtRec,IdxTm,IdxTm,Sort),
    PropTrue(TCtxtRec,Prop),
}
impl TCtxt {
    /// bind a var and type
    pub fn var(&self,v:Var,t:Type) -> TCtxt {
        TCtxt::Var(Rc::new(self.clone()),v,t)
    }
    /// bind a index var and sort
    pub fn ivar(&self,v:Var,s:Sort) -> TCtxt {
        TCtxt::IVar(Rc::new(self.clone()),v,s)
    }
    /// bind a type var and kind
    pub fn tvar(&self,v:Var,k:Kind) -> TCtxt {
        TCtxt::TVar(Rc::new(self.clone()),v,k)
    }
    /// bind a type constructor and kind
    pub fn tcons(&self,d:TypeCons,k:Kind) -> TCtxt {
        TCtxt::TCons(Rc::new(self.clone()),d,k)
    }
    /// bind an index equivalence
    pub fn equiv(&self,i1:IdxTm,i2:IdxTm,s:Sort) -> TCtxt {
        TCtxt::Equiv(Rc::new(self.clone()),i1,i2,s)
    }
    /// bind an index apartness
    pub fn apart(&self,i1:IdxTm,i2:IdxTm,s:Sort) -> TCtxt {
        TCtxt::Apart(Rc::new(self.clone()),i1,i2,s)
    }
    /// bind a true proposition
    pub fn prop(&self,p:Prop) -> TCtxt {
        TCtxt::PropTrue(Rc::new(self.clone()),p)
    }
}

impl TCtxt {
    pub fn lookup_var(&self, x:&Var) -> Option<Type> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Var(ref c,ref v,ref t) => {
                if x == v { Some(t.clone()) } else { c.lookup_var(x) }
            },
            TCtxt::IVar(ref c,_,_)
            | TCtxt::TVar(ref c,_,_)
            | TCtxt::TCons(ref c,_,_)
            | TCtxt::Equiv(ref c,_,_,_)
            | TCtxt::Apart(ref c,_,_,_)
            | TCtxt::PropTrue(ref c,_) => { c.lookup_var(x) },
        }
    }
    pub fn lookup_ivar(&self, x:&Var) -> Option<Sort> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::IVar(ref c,ref v,ref s) => {
                if x == v { Some(s.clone()) } else { c.lookup_ivar(x) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::TVar(ref c,_,_)
            | TCtxt::TCons(ref c,_,_)
            | TCtxt::Equiv(ref c,_,_,_)
            | TCtxt::Apart(ref c,_,_,_)
            | TCtxt::PropTrue(ref c,_) => { c.lookup_ivar(x) },
        }
    }
    pub fn lookup_tvar(&self, x:&Var) -> Option<Kind> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::TVar(ref c,ref v,ref k) => {
                if x == v { Some(k.clone()) } else { c.lookup_tvar(x) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::IVar(ref c,_,_)
            | TCtxt::TCons(ref c,_,_)
            | TCtxt::Equiv(ref c,_,_,_)
            | TCtxt::Apart(ref c,_,_,_)
            | TCtxt::PropTrue(ref c,_) => { c.lookup_tvar(x) },
        }
    }
    pub fn lookup_tcons(&self, x:&TCons) -> Option<Kind> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Var(ref c,ref v,ref k) => {
                if x == v { Some(k.clone()) } else { c.lookup_tcons(x) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::IVar(ref c,_,_)
            | TCtxt::TVar(ref c,_,_)
            | TCtxt::Equiv(ref c,_,_,_)
            | TCtxt::Apart(ref c,_,_,_)
            | TCtxt::PropTrue(ref c,_) => { c.lookup_tcons(x) },
        }
    }
    pub fn lookup_equiv(&self, idx1:IdxTm, idx2:IdxTm) -> Option<Sort> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Equiv(ref c,ref i1,ref i2,ref s) => {
                if i1 == idx1 & i2 == idx2 { Some(s.clone()) }
                else { c.lookup_equiv(i1,i2) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::IVar(ref c,_,_)
            | TCtxt::TVar(ref c,_,_)
            | TCtxt::TCons(ref c,_,_)
            | TCtxt::Apart(ref c,_,_,_)
            | TCtxt::PropTrue(ref c,_) => { c.lookup_equiv(i1,i2) },
        }
    pub fn lookup_apart(&self, idx1:IdxTm, idx2:IdxTm) -> Option<Sort> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Apart(ref c,ref i1,ref i2,ref s) => {
                if i1 == idx1 & i2 == idx2 { Some(s.clone()) }
                else { c.lookup_apart(i1,i2) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::IVar(ref c,_,_)
            | TCtxt::TVar(ref c,_,_)
            | TCtxt::TCons(ref c,_,_)
            | TCtxt::Equiv(ref c,_,_,_)
            | TCtxt::PropTrue(ref c,_) => { c.lookup_apart(i1,i2) },
        }
    }
    pub fn lookup_prop(&self, prop:Prop) -> bool {
        match *self {
            TCtxt::Empty => false,
            TCtxt::Prop(ref c,ref p) => {
                if p == prop { true } else { c.lookup_prop(prop) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::Equiv(ref c,_,_,_)
            | TCtxt::Apart(ref c,_,_,_) => { c.lookup_prop(prop) },
        }
    }
}

pub enum Dir { Synth, Check }

pub struct NameTmInfo { 
    pub ctxt:TCtxt,
    pub val:Rc<NameTmTD>,
    pub dir:Dir,
    pub typ:Sort,
}

pub enum NameTmTD {
    Var(Var),
    Name(Name),
    Bin(NameTmInfo, NameTmInfo),
    Lam(Var,NameTmInfo),
    App(NameTmInfo, NameTmInfo),
}

pub struct IdxTmInfo { 
    pub ctxt:TCtxt,
    pub val:Rc<IdxTmTD>,
    pub dir:Dir,
    pub typ:Sort,
}

pub enum IdxTmTD {
    Var(Var),
    Sing(NameTmInfo),
    Empty,
    Disj(IdxTmInfo, IdxTmInfo),
    Union(IdxTmInfo, IdxTmInfo),
    Unit,
    Pair(IdxTmInfo, IdxTmInfo),
    Proj1(IdxTmInfo),
    Proj2(IdxTmInfo),
    Lam(Var, IdxTmInfo),
    App(IdxTmInfo, IdxTmInfo),
    Map(NameTmInfo, IdxTmInfo),
    FlatMap(IdxTmInfo, IdxTmInfo),
    Star(IdxTmInfo, IdxTmInfo),
}

pub struct ValInfo { 
    pub ctxt:TCtxt,
    pub val:Rc<ValTD>,
    pub dir:Dir,
    pub typ:Type,
}

pub enum ValTD {
    Var(Var),
    Unit,
    Pair(ValInfo, ValInfo),
    Inj1(ValInfo),
    Inj2(ValInfo),
    Roll(ValInfo),
    Name(Name),
    NameFn(NameTmInfo),
    Anno(ValInfo,Type),
    ThunkAnon(ExpInfo),
    Bool(bool),
    Nat(usize),
    Str(String),
}

pub struct ExpInfo { 
    pub ctxt:TCtxt,
    pub val:Rc<ExpTD>,
    pub dir:Dir,
    pub typ:CEffect,
}

pub enum ExpTD {
    Anno(ExpInfo,CType),
    Force(ValInfo),
    Thunk(ValInfo,ExpInfo),
    Unroll(ValInfo,Var,ExpInfo),
    Fix(Var,ExpInfo),
    Ret(ValInfo),
    DefType(Var,Type,ExpInfo),
    Let(Var,ExpInfo,ExpInfo),
    Lam(Var, ExpInfo),
    App(ExpInfo, ValInfo),
    Split(ValInfo, Var, Var, ExpInfo),
    Case(ValInfo, Var, ExpInfo, Var, ExpInfo),
    IfThenElse(ValInfo, ExpInfo, ExpInfo),
    Ref(ValInfo,ValInfo),
    Get(ValInfo),
    Scope(ValInfo,ExpInfo),
    NameFnApp(ValInfo,ValInfo),
    PrimApp(PrimApp),
    Unimp,
    DebugLabel(String,ExpInfo),
}

enum TypeError {
    AnnoMism,
    NoSynthRule,
    NoCheckRule,
    InvalidPtr,
    ParamMism(usize),
    ParamNoSynth(usize),
    AppNotArrow,
    BadCheck,
    DSLiteral,
    EmptyDT,
}
impl fmt::Display for TypeError {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        let s = match *self {
            TypeError::AnnoMism => format!("annotation mismatch"),
            TypeError::NoSynthRule => format!("no synth rule found"),
            TypeError::NoCheckRule => format!("no check rule found"),
            TypeError::InvalidPtr => format!("invalid pointer"),
            TypeError::ParamMism(num) => format!("parameter {} type incorrect",num),
            TypeError::ParamNoSynth(num) => format!("parameter {} unknown type",num),
            TypeError::AppNotArrow => format!("application of non-arrow type"),
            TypeError::BadCheck => format!("checked type inappropriate for value"),
            TypeError::DSLiteral => format!("data structure literals not allowed"),
            TypeError::EmptyDT => format!("ambiguous empty data type"),
        };
        write!(f,"{}",s)
    }
}

impl Val {
    fn short(&self) -> &str {
        match *self {
            Var(_) => "Var",
            Unit => "Unit",
            Pair(_, _) => "Pair",
            Inj1(_) => "Inj1",
            Inj2(_) => "Inj2",
            Roll(_) => "Roll",
            Name(_) => "Name",
            NameFn(_) => "NameFn",
            Anno(_,_) => "Anno",
            ThunkAnon(_) => "ThunkAnon",
            Bool(_) => "Bool",
            Nat(_) => "Nat",
            Str(_) => "Str",
            NoParse(_) => "NoParse",
        }
    }
}

impl Exp {
    fn short(&self) -> &str {
        match *self {
            Anno(_,_) => "Anno",
            Force(_) => "Force",
            Thunk(_,_) => "Thunk",
            Unroll(_,_,_) => "Unroll",
            Fix(_,_) => "Fix",
            Ret(_) => "Ret",
            DefType(_,_,_) => "DefType",
            Let(Var,_,_) => "Let",
            Lam(Var, _) => "Lam",
            App(_, _) => "App",
            Split(_, _, _, _) => "Split",
            Case(_, _, _, _, _) => "Case",
            IfThenElse(_, _, _) => "IfThenElse",
            Ref(_,_) => "Ref",
            Get(_) => "Get",
            Scope(_,_) => "Scope",
            NameFnApp(_,_) => "NameFnApp",
            PrimApp(ref p) => p.short(),
            Unimp => "Unimp",
            DebugLabel(_,_) => "DebugLabel",
            NoParse(_) => "NoParse",
        }
    }
}
impl PrimApp {
    fn short(&self) -> &str {
        NatLt(_,_) => "NatLt",
        NameBin(_,_) => "NameBin",
        RefThunk(_), => "RefThunk",
    }
}

fn fail_synth_idxtm(last_label:Option<String>, err:TypeError, idxtm:&IdxTm) -> Option<IdxTmInfo> {
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to synthesize {} index term, error: {}", v.short(), err);
    None
}

fn fail_check_idxtm(last_label:Option<String>, err:TypeError, v:&IdxTm) -> Option<IdxTmInfo> {
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to check {} index term, error: {}", v.short(), err);
    None
}

fn fail_synth_nmtm(last_label:Option<String>, err:TypeError, nmtm:&NameTm) -> Option<NameTmInfo> {
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to synthesize {} name term, error: {}", v.short(), err);
    None
}

fn fail_check_nmtm(last_label:Option<String>, err:TypeError, nmtm:&NameTm) -> Option<NameTmInfo> {
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to check {} name term, error: {}", v.short(), err);
    None
}

fn fail_synth_val(last_label:Option<String>, err:TypeError, v:&Val) -> Option<Type> {
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to synthesize {} value, error: {}", v.short(), err);
    None
}

fn fail_check_val(last_label:Option<String>, err:TypeError, v:&Val) -> Option<Type> {
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to check {} value, error: {}", v.short(), err);
    None
}

fn fail_synth_exp(last_label:Option<String>, err:TypeError, e:&Exp) -> Option<CEffect> {
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to synthesize {} expression, error: {}", e.short(), err);
    None
}

fn fail_check_exp(last_label:Option<String>, err:TypeError, e:&Exp) -> Option<CEffect> {
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to check {} expression, error: {}", e.short(), err);
    None
}

pub fn synth_idxtm(last_label:Option<String>, ctc:&TCtxt, idxtm:&IdxTm) -> Option<Sort> {
    match idxtm {
        &Var(ref x) => {},
        &Sing(ref nt) => {},
        &Empty => {},
        &Disj(ref idx1, ref idx2) => {},
        &Union(ref idx1, ref idx2) => {},
        &Unit => {},
        &Pair(ref idx1, ref idx2) => {},
        &Proj1(ref idx) => {},
        &Proj2(ref idx) => {},
        &Lam(ref x, ref idx) => {},
        &App(ref idx1, ref idx2) => {},
        &Map(ref nt, ref idx) => {},
        &FlatMap(ref idx1, ref idx2) => {},
        &Star(ref idx1, ref idx2) => {},
        &NoParse(ref s) => {},
    }
}

pub fn check_idxtm(last_label:Option<String>, ctc:&TCtxt, idxtm:&IdxTm, sort:&Sort) -> Option<Sort> {
    match idxtm {
        &Var(ref x) => {},
        &Sing(ref nt) => {},
        &Empty => {},
        &Disj(ref idx1, ref idx2) => {},
        &Union(ref idx1, ref idx2) => {},
        &Unit => {},
        &Pair(ref idx1, ref idx2) => {},
        &Proj1(ref idx) => {},
        &Proj2(ref idx) => {},
        &Lam(ref x, ref idx) => {},
        &App(ref idx1, ref idx2) => {},
        &Map(ref nt, ref idx) => {},
        &FlatMap(ref idx1, ref idx2) => {},
        &Star(ref idx1, ref idx2) => {},
        &NoParse(ref s) => {},
    }  
}

pub fn synth_nmtm(last_label:Option<String>, ctc:&TCtxt, nmtm:&NameTm) -> Option<Sort> {
    match nmtm {
        Var(ref x) => {},
        Name(ref n) => {},
        Bin(ref nt1, ref nt2) => {},
        Lam(ref x,ref nt) => {},
        App(ref nt1, ref nt2) => {},
        NoParse(ref s) => {},
    }  
}

pub fn check_nmtm(last_label:Option<String>, ctc:&TCtxt, nmtm:&NameTm, sort:&Sort) -> Option<Sort> {
    match nmtm {
        Var(ref x) => {},
        Name(ref n) => {},
        Bin(ref nt1, ref nt2) => {},
        Lam(ref x,ref nt) => {},
        App(ref nt1, ref nt2) => {},
        NoParse(ref s) => {},
    }  
}

pub fn synth_val(last_label:Option<String>, ctxt:&TCtxt, val:&Val) -> Option<Type> {
    match val {
        /* Note for implementers:
            one or both of `synth_val` or `check_val` should be implemented
            for your new Val variant
            (check_val defaults to synth_val)
        */
        &Val::Var(ref v) => { ctxt.lookup_var(v) },
        &Val::Unit => { Some(Type::Unit) },
        &Val::Pair(ref x, ref y) => {
            if let Some(a) = synth_val(last_label, ctxt, x) {
                if let Some(b) = synth_val(last_label, ctxt, y) {
                    Some(Type::Prod(Rc::new(a),Rc::new(b)))
                } else { fail_synth_val(last_label, TypeError::ParamNoSynth(1), val) }
            } else { fail_synth_val(last_label, TypeError::ParamNoSynth(0), val) }
        },
        &NameTm(ref n) => { unimplemented!("synth val name term") },
        &Val::Inj1(_) => { fail_synth_val(last_label, TypeError::NoSynthRule, val) },
        &Val::Inj2(_) => { fail_synth_val(last_label, TypeError::NoSynthRule, val) },
        &Val::Anno(ref v,ref t) => {
            if check_val(last_label, ctxt, v, t) {
                Some(t.clone())
            } else { fail_synth_val(last_label, TypeError::AnnoMism, val) }
        },
        &Val::Nat(_) => { unimplemented!("synth val nat") },
        &Val::Str(_) => { unimplemented!("synth val string") },
  --------------------------------------------------------------------      
        &Var(ref v) => {},
        &Unit => {},
        &Pair(ref v1, ref v2) => {},
        &Inj1(ref v) => {},
        &Inj2(ref v) => {},
        &Roll(ref v) => {},
        &Name(ref n) => {},
        &NameFn(ref nmtm) => {},
        &Anno(ref v,ref t) => {},
        &ThunkAnon(ref e) => {},
        &Bool(_) => {},
        &Nat(_) => {},
        &Str(_) => {},
        &NoParse(ref s) => {},
    }
}


pub fn check_val(last_label:Option<String>, ctxt:&TCtxt, val:&Val, typ:&Type) -> bool {
    match (val, typ) {
        (&Val::Unit, &Type::Unit) => true,
        (&Val::Pair(ref v1, ref v2), &Type::Prod(ref t1, ref t2)) => {
            check_val(last_label, ctxt, v1, t1 )
            & check_val(last_label, ctxt, v2, t2 )
        },
        (&Val::Inj1(ref v), &Type::Sum(ref t1, _)) => {
            check_val(last_label, ctxt, v, t1 )
        },
        (&Val::Inj2(ref v), &Type::Sum(_, ref t2)) => {
            check_val(last_label, ctxt, v, t2 )
        },
        (&Val::Nat(_), _) => unimplemented!("check val nat"),
        (&Val::Str(_), _) => unimplemented!("check val string"),
        (v, t2) => {
            if let Some(ref t1) = synth_val(last_label, ctxt, v) {
                t2 == t1
            } else { fail_check_val(last_label, TypeError::NoCheckRule,val) }
        },
  ---------------------------------------------------------------------------      
        &Var(ref v) => {},
        &Unit => {},
        &Pair(ref v1, ref v2) => {},
        &Inj1(ref v) => {},
        &Inj2(ref v) => {},
        &Roll(ref v) => {},
        &Name(ref n) => {},
        &NameFn(ref nmtm) => {},
        &Anno(ref v,ref t) => {},
        &ThunkAnon(ref e) => {},
        &Bool(_) => {},
        &Nat(_) => {},
        &Str(_) => {},
        &NoParse(ref s) => {},
    }
}

pub fn synth_exp(last_label:Option<String>, ctxt:&TCtxt, exp:&Exp) -> Option<CType> {
    // TODO: synth rules for all capable expressions
    match exp {
        /* Note for implementers:
            one or both of `synth_exp` or `check_exp` should be implemented
            for your new Exp variant
            (check_exp defaults to synth_exp)
        */
        &Exp::Anno(ref e, ref ct) => {
            if check_exp(last_label, ctxt, e, ct) {
                Some(ct.clone())
            } else { fail_synth_exp(last_label, TypeError::AnnoMism, exp) }
        },
        &Exp::Force(ref v) => {
            if let Some(Type::U(ct)) = synth_val(last_label, ctxt, v) {
                Some((*ct).clone())
            } else { fail_synth_exp(last_label, TypeError::ParamMism(0), exp) }
        },
        &Exp::Thunk(ref e) => {
            if let Some(ct) = synth_exp(last_label, ctxt, e) {
                Some(make_ctype![F U outerctx ct])
            } else { fail_synth_exp(last_label, TypeError::ParamNoSynth(0), exp) }
        },
        &Exp::Fix(_,_) => { fail_synth_exp(last_label, TypeError::NoSynthRule, exp) },
        &Exp::Ret(ref v) => {
            if let Some(t) = synth_val(last_label, ctxt, v) {
                Some(make_ctype![F outerctx t])
            } else { fail_synth_exp(last_label, TypeError::ParamNoSynth(0), exp) }
        },
        &Exp::Let(ref x,ref e1, ref e2) => {
            if let Some(CType::F(t)) = synth_exp(last_label, ctxt, e1) {
                synth_exp(last_label, &ctxt.var(x.clone(), (*t).clone()), e2)
            } else { fail_synth_exp(last_label, TypeError::ParamMism(2), exp) }
        },
        &Exp::Lam(_, _) => { fail_synth_exp(last_label, TypeError::NoSynthRule, exp) },
        &Exp::App(ref e, ref v) => {
            if let Some(CType::Arrow(t,ct)) = synth_exp(last_label, ctxt, e) {
                if check_val(last_label, ctxt, v, &t) {
                    Some((*ct).clone())
                } else { fail_synth_exp(last_label, TypeError::ParamMism(1), exp) }
            } else { fail_synth_exp(last_label, TypeError::AppNotArrow, exp) }
        },
        &Exp::Split(_, _, _, _) => { fail_synth_exp(last_label, TypeError::NoSynthRule, exp) },
        &Exp::Case(_, _, _, _, _) => { fail_synth_exp(last_label, TypeError::NoSynthRule, exp) },
        &Exp::Ref(_) => { fail_synth_exp(last_label, TypeError::NoSynthRule, exp) },
        &Exp::Get(ref v) => {
            if let Some(Type::Ref(t)) = synth_val(last_label, ctxt, v) {
                Some(CType::F(t))
            } else { fail_synth_exp(last_label, TypeError::ParamMism(0), exp) }
        },
        &Exp::Name(ref nm, ref e) => {
            synth_exp(Some(nm), ctxt, e)
        },
   ------------------------------------------------------------------
        &Anno(ref e,ref ct) => {},
        &Force(ref v) => {},
        &Thunk(ref v,ref e) => {},
        &Unroll(ref v,ref x,ref e) => {},
        &Fix(ref x,ref e) => {},
        &Ret(ref v) => {},
        &DefType(ref x,Type,ref e) => {},
        &Let(ref x,ExpRec,ExpRec) => {},
        &Lam(ref x, ref e) => {},
        &App(ref e, ref v) => {},
        &Split(ref v, ref x1, ref x2, ref e) => {},
        &Case(ref v, ref x1, ExpRec, ref x2, ExpRec) => {},
        &IfThenElse(ref v, ExpRec, ExpRec) => {},
        &Ref(ref v1,ref v2) => {},
        &Get(ref v) => {},
        &Scope(ref v,ref e) => {},
        &NameFnApp(ref v1,ref v2) => {},
        &PrimApp(PrimApp) => {},
        &Unimp => {},
        &DebugLabel(ref s,ref e) => {},
        &NoParse(ref s) => {},
    }
}

pub fn check_exp(last_label:Option<String>, ctxt:&TCtxt, exp:&Exp, ctype:&CType) -> bool {
    // TODO: remove ctype from match, check it in body and maybe give type error
    match (exp, ctype) {
        (&Exp::Name(ref nm, ref e), ct) => {
            check_exp(Some(nm), ctxt, e, ct)
        },
        (&Exp::Thunk(ref e), &CType::F(ref t)) => {
            if let Type::U(ref ct) = **t {
                check_exp(last_label, ctxt, e, ct)
            } else { fail_check_exp(last_label, TypeError::ParamMism(0), exp) }
        },
        (&Exp::Ret(ref v), &CType::F(ref t)) => {
            check_val(last_label, ctxt, v, t)
        },
        (&Exp::Let(ref x, ref e1, ref e2), ct) => {
            if let Some(CType::F(t)) = synth_exp(last_label, ctxt, e1) {
                check_exp(last_label, &ctxt.var(x.clone(), (*t).clone()), e2, ct)
            } else { fail_check_exp(last_label, TypeError::ParamMism(0), exp) }
        },
        (&Exp::Lam(ref x, ref e), &CType::Arrow(ref t, ref ct)) => {
            check_exp(last_label, &ctxt.var(x.clone(),(**t).clone()), e, ct)
        },
        (&Exp::Split(ref v, ref x1, ref x2, ref e), ct) => {
            if let Some(Type::Pair(t1, t2)) = synth_val(last_label, ctxt, v) {
                let t1 = (*t1).clone();
                let t2 = (*t2).clone();
                check_exp(last_label, &ctxt.var(x1.clone(),t1).var(x2.clone(),t2), e, ct)
            } else { fail_check_exp(last_label, TypeError::ParamMism(0), exp) }
        },
        (&Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2), ct) => {
            if let Some(Type::Sum(t1, t2)) = synth_val(last_label, ctxt, v) {
                let t1 = (*t1).clone();
                let t2 = (*t2).clone();
                check_exp(last_label, &ctxt.var(x1.clone(),t1), e1, ct)
                & check_exp(last_label, &ctxt.var(x2.clone(),t2), e2, ct)
            } else { fail_check_exp(last_label, TypeError::ParamMism(0), exp) }
        },
        (&Exp::Ref(ref v), &CType::F(ref t)) => {
            if let Type::Ref(ref t) = **t {
                check_val(last_label, ctxt, v, t)
            } else { fail_check_exp(last_label, TypeError::ParamMism(0), exp) }
        },
        (&Exp::Fix(ref f, ref e), ct) => {
            /*
            Ctx, f: U(C) |- e <== C
            -----------------------
            Ctx |- fix(f.e) <== C
            */
            check_exp(last_label, &ctxt.var(f.clone(), Type::U(Rc::new(ct.clone()))), e, ct)
        },
        (e, ct2) => {
            if let Some(ref ct1) = synth_exp(last_label, ctxt, e) {
                ct2 == ct1
            } else { fail_check_exp(last_label, TypeError::NoSynthRule, exp) }
        },
 ---------------------------------------------------------------------------
        &Anno(ref e,ref ct) => {},
        &Force(ref v) => {},
        &Thunk(ref v,ref e) => {},
        &Unroll(ref v,ref x,ref e) => {},
        &Fix(ref x,ref e) => {},
        &Ret(ref v) => {},
        &DefType(ref x,Type,ref e) => {},
        &Let(ref x,ExpRec,ExpRec) => {},
        &Lam(ref x, ref e) => {},
        &App(ref e, ref v) => {},
        &Split(ref v, ref x1, ref x2, ref e) => {},
        &Case(ref v, ref x1, ExpRec, ref x2, ExpRec) => {},
        &IfThenElse(ref v, ExpRec, ExpRec) => {},
        &Ref(ref v1,ref v2) => {},
        &Get(ref v) => {},
        &Scope(ref v,ref e) => {},
        &NameFnApp(ref v1,ref v2) => {},
        &PrimApp(PrimApp) => {},
        &Unimp => {},
        &DebugLabel(ref s,ref e) => {},
        &NoParse(ref s) => {},

    }
}
