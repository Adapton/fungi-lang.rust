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
    pub fn lookup_tcons(&self, x:&TypeCons) -> Option<Kind> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::TCons(ref c,ref v,ref k) => {
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
    pub fn lookup_equiv(&self, idx1:&IdxTm, idx2:&IdxTm) -> Option<Sort> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Equiv(ref c,ref i1,ref i2,ref s) => {
                if (i1 == idx1) & (i2 == idx2) { Some(s.clone()) }
                else { c.lookup_equiv(idx1,idx2) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::IVar(ref c,_,_)
            | TCtxt::TVar(ref c,_,_)
            | TCtxt::TCons(ref c,_,_)
            | TCtxt::Apart(ref c,_,_,_)
            | TCtxt::PropTrue(ref c,_) => { c.lookup_equiv(idx1,idx2) },
        }
    }
    pub fn lookup_apart(&self, idx1:&IdxTm, idx2:&IdxTm) -> Option<Sort> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Apart(ref c,ref i1,ref i2,ref s) => {
                if (i1 == idx1) & (i2 == idx2) { Some(s.clone()) }
                else { c.lookup_apart(idx1,idx2) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::IVar(ref c,_,_)
            | TCtxt::TVar(ref c,_,_)
            | TCtxt::TCons(ref c,_,_)
            | TCtxt::Equiv(ref c,_,_,_)
            | TCtxt::PropTrue(ref c,_) => { c.lookup_apart(idx1,idx2) },
        }
    }
    pub fn lookup_prop(&self, prop:&Prop) -> bool {
        match *self {
            TCtxt::Empty => false,
            TCtxt::PropTrue(ref c,ref p) => {
                if p == prop { true } else { c.lookup_prop(prop) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::IVar(ref c,_,_)
            | TCtxt::TVar(ref c,_,_)
            | TCtxt::TCons(ref c,_,_)
            | TCtxt::Equiv(ref c,_,_,_)
            | TCtxt::Apart(ref c,_,_,_) => { c.lookup_prop(prop) },
        }
    }
}

pub trait HasType { type Type; }

pub struct TypeInfo<TD:HasType> { 
    pub ctxt:TCtxt,
    pub node:Rc<TD>,
    pub dir:Dir,
    pub typ:Result<TD::Type,TypeError>,
}
impl<A:HasType> TypeInfo<A> {
    pub fn is_err(&self) -> bool { self.typ.is_err() }
    pub fn is_ok(&self) -> bool { self.typ.is_ok() }
}

pub enum NameTmTD {
    Var(Var),
    Name(Name),
    Bin(TypeInfo<NameTmTD>, TypeInfo<NameTmTD>),
    Lam(Var,Sort,TypeInfo<NameTmTD>),
    App(TypeInfo<NameTmTD>, TypeInfo<NameTmTD>),
    NoParse(String),
}
impl HasType for NameTmTD { type Type = Sort; }

pub enum IdxTmTD {
    Var(Var),
    Sing(TypeInfo<NameTmTD>),
    Empty,
    Disj(TypeInfo<IdxTmTD>, TypeInfo<IdxTmTD>),
    Union(TypeInfo<IdxTmTD>, TypeInfo<IdxTmTD>),
    Unit,
    Pair(TypeInfo<IdxTmTD>, TypeInfo<IdxTmTD>),
    Proj1(TypeInfo<IdxTmTD>),
    Proj2(TypeInfo<IdxTmTD>),
    Lam(Var, Sort, TypeInfo<IdxTmTD>),
    App(TypeInfo<IdxTmTD>, TypeInfo<IdxTmTD>),
    Map(TypeInfo<NameTmTD>, TypeInfo<IdxTmTD>),
    FlatMap(TypeInfo<IdxTmTD>, TypeInfo<IdxTmTD>),
    Star(TypeInfo<IdxTmTD>, TypeInfo<IdxTmTD>),
    NoParse(String),
}
impl HasType for IdxTmTD { type Type = Sort; }

pub enum ValTD {
    Var(Var),
    Unit,
    Pair(TypeInfo<ValTD>, TypeInfo<ValTD>),
    Inj1(TypeInfo<ValTD>),
    Inj2(TypeInfo<ValTD>),
    Roll(TypeInfo<ValTD>),
    Name(Name),
    NameFn(TypeInfo<NameTmTD>),
    Anno(TypeInfo<ValTD>,Type),
    ThunkAnon(TypeInfo<ExpTD>),
    Bool(bool),
    Nat(usize),
    Str(String),
    NoParse(String),
}
impl HasType for ValTD { type Type = Type; }

pub enum ExpTD {
    AnnoC(TypeInfo<ExpTD>,CType),
    AnnoE(TypeInfo<ExpTD>,CEffect),
    Force(TypeInfo<ValTD>),
    Thunk(TypeInfo<ValTD>,TypeInfo<ExpTD>),
    Unroll(TypeInfo<ValTD>,Var,TypeInfo<ExpTD>),
    Fix(Var,TypeInfo<ExpTD>),
    Ret(TypeInfo<ValTD>),
    DefType(Var,Type,TypeInfo<ExpTD>),
    Let(Var,TypeInfo<ExpTD>,TypeInfo<ExpTD>),
    Lam(Var, TypeInfo<ExpTD>),
    App(TypeInfo<ExpTD>, TypeInfo<ValTD>),
    Split(TypeInfo<ValTD>, Var, Var, TypeInfo<ExpTD>),
    Case(TypeInfo<ValTD>, Var, TypeInfo<ExpTD>, Var, TypeInfo<ExpTD>),
    IfThenElse(TypeInfo<ValTD>, TypeInfo<ExpTD>, TypeInfo<ExpTD>),
    Ref(TypeInfo<ValTD>,TypeInfo<ValTD>),
    Get(TypeInfo<ValTD>),
    Scope(TypeInfo<ValTD>,TypeInfo<ExpTD>),
    NameFnApp(TypeInfo<ValTD>,TypeInfo<ValTD>),
    PrimApp(PrimAppTD),
    Unimp,
    DebugLabel(Option<Name>, Option<String>,TypeInfo<ExpTD>),
    NoParse(String),
}
impl HasType for ExpTD { type Type = CEffect; }

pub enum PrimAppTD {
    NatLt(TypeInfo<ValTD>,TypeInfo<ValTD>),
    NameBin(TypeInfo<ValTD>,TypeInfo<ValTD>),
    RefThunk(TypeInfo<ValTD>),
}
trait AstNode {
    fn node_desc() -> &'static str { "ast node" }
    fn short(&self) -> &str { "unknown" }
}

impl AstNode for NameTmTD {
    fn node_desc() -> &'static str { "name term" }
    fn short(&self) -> &str {
        match *self {
            NameTmTD::Var(_) => "Var",
            NameTmTD::Name(_) => "Name",
            NameTmTD::Bin(_, _) => "Bin",
            NameTmTD::Lam(_,_,_) => "Lam",
            NameTmTD::App(_, _) => "App",
            NameTmTD::NoParse(_) => "NoParse",
        }
    }
}

impl AstNode for IdxTmTD {
    fn node_desc() -> &'static str { "index term" }
    fn short(&self) -> &str {
        match *self {
            IdxTmTD::Var(_) => "Var",
            IdxTmTD::Sing(_) => "Sing",
            IdxTmTD::Empty => "Empty",
            IdxTmTD::Disj(_, _) => "Disj",
            IdxTmTD::Union(_, _) => "Union",
            IdxTmTD::Unit => "Unit",
            IdxTmTD::Pair(_, _) => "Pair",
            IdxTmTD::Proj1(_) => "Proj1",
            IdxTmTD::Proj2(_) => "Proj2",
            IdxTmTD::Lam(_, _, _) => "Lam",
            IdxTmTD::App(_, _) => "App",
            IdxTmTD::Map(_, _) => "Map",
            IdxTmTD::FlatMap(_, _) => "FlatMap",
            IdxTmTD::Star(_, _) => "Star",
            IdxTmTD::NoParse(_) => "NoParse",
        }
    }
}

impl AstNode for ValTD {
    fn node_desc() -> &'static str { "value" }
    fn short(&self) -> &str {
        match *self {
            ValTD::Var(_) => "Var",
            ValTD::Unit => "Unit",
            ValTD::Pair(_, _) => "Pair",
            ValTD::Inj1(_) => "Inj1",
            ValTD::Inj2(_) => "Inj2",
            ValTD::Roll(_) => "Roll",
            ValTD::Name(_) => "Name",
            ValTD::NameFn(_) => "NameFn",
            ValTD::Anno(_,_) => "Anno",
            ValTD::ThunkAnon(_) => "ThunkAnon",
            ValTD::Bool(_) => "Bool",
            ValTD::Nat(_) => "Nat",
            ValTD::Str(_) => "Str",
            ValTD::NoParse(_) => "NoParse",
        }
    }
}

impl AstNode for ExpTD {
    fn node_desc() -> &'static str { "expression" }
    fn short(&self) -> &str {
        match *self {
            ExpTD::AnnoC(_,_) => "AnnoC",
            ExpTD::AnnoE(_,_) => "AnnoE",
            ExpTD::Force(_) => "Force",
            ExpTD::Thunk(_,_) => "Thunk",
            ExpTD::Unroll(_,_,_) => "Unroll",
            ExpTD::Fix(_,_) => "Fix",
            ExpTD::Ret(_) => "Ret",
            ExpTD::DefType(_,_,_) => "DefType",
            ExpTD::Let(_,_,_) => "Let",
            ExpTD::Lam(_, _) => "Lam",
            ExpTD::App(_, _) => "App",
            ExpTD::Split(_, _, _, _) => "Split",
            ExpTD::Case(_, _, _, _, _) => "Case",
            ExpTD::IfThenElse(_, _, _) => "IfThenElse",
            ExpTD::Ref(_,_) => "Ref",
            ExpTD::Get(_) => "Get",
            ExpTD::Scope(_,_) => "Scope",
            ExpTD::NameFnApp(_,_) => "NameFnApp",
            ExpTD::PrimApp(ref p) => p.short(),
            ExpTD::Unimp => "Unimp",
            ExpTD::DebugLabel(_,_,_) => "DebugLabel",
            ExpTD::NoParse(_) => "NoParse",
        }
    }
}
impl AstNode for PrimAppTD {
    fn node_desc() -> &'static str { "primitive expression" }
    fn short(&self) -> &str {
        match *self {
            PrimAppTD::NatLt(_,_) => "NatLt",
            PrimAppTD::NameBin(_,_) => "NameBin",
            PrimAppTD::RefThunk(_) => "RefThunk",
        }
    }
}

pub enum Dir { Synth, Check }
impl Dir {
    fn short(&self) -> &str {
        match *self {
            Dir::Synth => "synth",
            Dir::Check => "check",
        }
    }
}

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum TypeError {
    VarNotInScope(String),
    NoParse(String),
    AnnoMism,
    NoSynthRule,
    NoCheckRule,
    InvalidPtr,
    ParamMism(usize),
    ParamNoSynth(usize),
    ParamNoCheck(usize),
    ProjNotProd,
    AppNotArrow,
    ValNotArrow,
    GetNotRef,
    BadCheck,
    DSLiteral,
    EmptyDT,
    Unimplemented,
}
impl fmt::Display for TypeError {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        let s = match *self {
            TypeError::VarNotInScope(ref s) => format!("variable {} not in scope",s),
            TypeError::NoParse(ref s) => format!("term did not parse: `{}`",s),
            TypeError::AnnoMism => format!("annotation mismatch"),
            TypeError::NoSynthRule => format!("no synth rule found, try an annotation"),
            TypeError::NoCheckRule => format!("no check rule found"),
            TypeError::InvalidPtr => format!("invalid pointer"),
            // 0 based parameter numbers
            TypeError::ParamMism(num) => format!("parameter {} type incorrect",num),
            TypeError::ParamNoSynth(num) => format!("parameter {} unknown type",num),
            TypeError::ParamNoCheck(num) => format!("parameter {} type mismatch ",num),
            TypeError::ProjNotProd => format!("projection of non-product type"),
            TypeError::ValNotArrow => format!("this value requires an arrow type"),
            TypeError::AppNotArrow => format!("application of non-arrow type"),
            TypeError::GetNotRef => format!("get from a non-ref val"),
            TypeError::BadCheck => format!("checked type inappropriate for value"),
            TypeError::DSLiteral => format!("data structure literals not allowed"),
            TypeError::EmptyDT => format!("ambiguous empty data type"),
            TypeError::Unimplemented => format!("Internal Error: type-checking unimplemented"),
        };
        write!(f,"{}",s)
    }
}

fn failure<N:AstNode+HasType>(dir:Dir, last_label:Option<&str>, ctxt:&TCtxt, n:N, err:TypeError) -> TypeInfo<N> {
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to {} {} {}, error: {}", dir.short(), n.short(), N::node_desc(), err);
    TypeInfo{
        ctxt: ctxt.clone(),
        node: Rc::new(n),
        dir: dir,
        typ: Err(err),
    }
}

fn success<N:AstNode+HasType>(dir:Dir, _last_label:Option<&str>, ctxt:&TCtxt, n:N, typ:N::Type) -> TypeInfo<N> {
    TypeInfo{
        ctxt: ctxt.clone(),
        node: Rc::new(n),
        dir: dir,
        typ: Ok(typ)
    }
}

pub fn synth_idxtm(last_label:Option<&str>, ctxt:&TCtxt, idxtm:&IdxTm) -> TypeInfo<IdxTmTD> {
    let fail = |td:IdxTmTD, err :TypeError| { failure(Dir::Synth, last_label, ctxt, td, err)  };
    let succ = |td:IdxTmTD, sort:Sort     | { success(Dir::Synth, last_label, ctxt, td, sort) };
    match idxtm {
        &IdxTm::Var(ref x) => {
            let td = IdxTmTD::Var(x.clone());
            match ctxt.lookup_ivar(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(sort) => succ(td, sort)
            }   
        }
        &IdxTm::Sing(ref nt) => {
            let td0 = synth_nmtm(last_label,ctxt,nt);
            let ty0 = td0.typ.clone();
            let td = IdxTmTD::Sing(td0);
            match ty0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(ref t) if *t == Sort::Nm => succ(td, Sort::NmSet),
                Ok(_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Empty => {
            succ(IdxTmTD::Empty, Sort::NmSet)
        },
        &IdxTm::Disj(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctxt,idx0);
            let td1 = synth_idxtm(last_label,ctxt,idx1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = IdxTmTD::Disj(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmSet),Ok(Sort::NmSet)) => succ(td, Sort::NmSet),
                (Ok(Sort::NmSet),_) => fail(td, TypeError::ParamMism(1)),
                (_,_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Union(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctxt,idx0);
            let td1 = synth_idxtm(last_label,ctxt,idx1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = IdxTmTD::Union(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmSet),Ok(Sort::NmSet)) => succ(td, Sort::NmSet),
                (Ok(Sort::NmSet),_) => fail(td, TypeError::ParamMism(1)),
                (_,_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Unit => {
            succ(IdxTmTD::Unit, Sort::Unit)
        },
        &IdxTm::Pair(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctxt,idx0);
            let td1 = synth_idxtm(last_label,ctxt,idx1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = IdxTmTD::Pair(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(t0),Ok(t1)) => succ(td, Sort::Prod(
                    Rc::new(t0), Rc::new(t1),
                ))
            }
        },
        &IdxTm::Proj1(ref idx) => {
            let td0 = synth_idxtm(last_label,ctxt,idx);
            let typ0 = td0.typ.clone();
            let td = IdxTmTD::Proj1(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Sort::Prod(t0,_)) => succ(td, (*t0).clone()),
                _ => fail(td, TypeError::ProjNotProd),
            }
        },
        &IdxTm::Proj2(ref idx) => {
            let td0 = synth_idxtm(last_label,ctxt,idx);
            let typ0 = td0.typ.clone();
            let td = IdxTmTD::Proj2(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Sort::Prod(_,t1)) => succ(td, (*t1).clone()),
                _ => fail(td, TypeError::ProjNotProd),
            }
        },
        &IdxTm::Lam(ref x, ref x_sort, ref idx) => {
            let ctxt_ext = ctxt.ivar(x.clone(), x_sort.clone());
            let td0 = synth_idxtm(last_label,&ctxt_ext,idx);
            let typ0 = td0.typ.clone();
            let td = IdxTmTD::Lam(x.clone(), x_sort.clone(), td0);
            if let &Sort::NoParse(ref bad) = x_sort {
                return fail(td, TypeError::NoParse(bad.clone()))
            }
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(2)),
                Ok(s) =>  succ(td, Sort::IdxArrow(
                    Rc::new(x_sort.clone()),
                    Rc::new(s),
                )),
            }
        },
        &IdxTm::App(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctxt,idx0);
            let td1 = synth_idxtm(last_label,ctxt,idx1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = IdxTmTD::App(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::IdxArrow(ref t0,ref t1)),Ok(ref t2)) if **t0 == *t2 => succ(td, (**t1).clone()),
                (Ok(Sort::IdxArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                _ => fail(td, TypeError::AppNotArrow),
            }
        },
        &IdxTm::Map(ref nt, ref idx) => {
            let td0 = synth_nmtm(last_label,ctxt,nt);
            let td1 = synth_idxtm(last_label,ctxt,idx);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = IdxTmTD::Map(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmArrow(n0,n1)),Ok(Sort::NmSet)) => {
                    if (*n0 == Sort::Nm) & (*n1 == Sort::Nm) { succ(td, Sort::NmSet) }
                    else { fail(td, TypeError::ParamMism(0)) }
                },
                (Ok(Sort::NmArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                _ => fail(td, TypeError::AppNotArrow),
            }
        },
        &IdxTm::FlatMap(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctxt,idx0);
            let td1 = synth_idxtm(last_label,ctxt,idx1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = IdxTmTD::FlatMap(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::IdxArrow(n0,n1)),Ok(Sort::NmSet)) => {
                    if (*n0 == Sort::Nm) & (*n1 == Sort::NmSet) { succ(td, Sort::NmSet) }
                    else { fail(td, TypeError::ParamMism(0)) }
                },
                (Ok(Sort::IdxArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                (Ok(_),_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Star(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctxt,idx0);
            let td1 = synth_idxtm(last_label,ctxt,idx1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = IdxTmTD::Star(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::IdxArrow(n0,n1)),Ok(Sort::NmSet)) => {
                    if (*n0 == Sort::Nm) & (*n1 == Sort::NmSet) { succ(td,Sort::NmSet) }
                    else { fail(td, TypeError::ParamMism(0)) }
                },
                (Ok(Sort::IdxArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                (Ok(_),_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::NoParse(ref s) => {
            fail(IdxTmTD::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },
    }
}

pub fn check_idxtm(last_label:Option<&str>, ctxt:&TCtxt, idxtm:&IdxTm, sort:&Sort) -> TypeInfo<IdxTmTD> {
    // let fail = |td:IdxTmTD, err :TypeError| { failure(Dir::Check, last_label, ctxt, td, err)  };
    // let succ = |td:IdxTmTD, sort:Sort     | { success(Dir::Check, last_label, ctxt, td, sort) };
    match idxtm {
        // We're exclusively using synthesis for index terms at the moment
        tm => {
            let mut td = synth_idxtm(last_label,ctxt,tm);
            let ty = td.typ.clone();
            if let Ok(ty) = ty {
                if ty == *sort { td }
                else {
                    td.typ = Err(TypeError::AnnoMism);
                    td
                }
            } else { td }
        },
    }  
}

pub fn synth_nmtm(last_label:Option<&str>, ctxt:&TCtxt, nmtm:&NameTm) -> TypeInfo<NameTmTD> {
    let fail = |td:NameTmTD, err :TypeError| { failure(Dir::Synth, last_label, ctxt, td, err)  };
    let succ = |td:NameTmTD, sort:Sort     | { success(Dir::Synth, last_label, ctxt, td, sort) };
    match nmtm {
        &NameTm::Var(ref x) => {
            let td = NameTmTD::Var(x.clone());
            match ctxt.lookup_ivar(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(sort) => succ(td, sort)
            }
        },
        &NameTm::Name(ref n) => {
            let td = NameTmTD::Name(n.clone());
            if let &Name::NoParse(ref bad) = n {
                return fail(td, TypeError::NoParse(bad.clone()))
            }
            succ(td, Sort::Nm)
        },
        &NameTm::Bin(ref nt0, ref nt1) => {
            let td0 = synth_nmtm(last_label, ctxt, nt0);
            let td1 = synth_nmtm(last_label, ctxt, nt1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = NameTmTD::Bin(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::Nm),Ok(Sort::Nm)) => succ(td, Sort::Nm),
                (Ok(Sort::Nm),_) => fail(td, TypeError::ParamMism(1)),
                (_,_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &NameTm::Lam(ref x, ref s, ref nt) => {
            let ctxt_ext = ctxt.ivar(x.clone(), s.clone());
            let td0 = synth_nmtm(last_label,&ctxt_ext,nt);
            let typ0 = td0.typ.clone();
            let td = NameTmTD::Lam(x.clone(), s.clone(), td0);
            if let &Sort::NoParse(ref bad) = s {
                return fail(td, TypeError::NoParse(bad.clone()))
            }
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(2)),
                Ok(rty) =>  succ(td, Sort::NmArrow(
                    Rc::new(s.clone()),
                    Rc::new(rty),
                )),
            }
        },
        &NameTm::App(ref nt0, ref nt1) => {
            let td0 = synth_nmtm(last_label,ctxt,nt0);
            let td1 = synth_nmtm(last_label,ctxt,nt1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = NameTmTD::App(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmArrow(ref t0,ref t1)),Ok(ref t2)) if **t0 == *t2 => succ(td, (**t1).clone()),
                (Ok(Sort::NmArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                _ => fail(td, TypeError::AppNotArrow),
            }
        },
        &NameTm::NoParse(ref s) => {
            fail(NameTmTD::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },
    }  
}

pub fn check_nmtm(last_label:Option<&str>, ctxt:&TCtxt, nmtm:&NameTm, sort:&Sort) -> TypeInfo<NameTmTD> {
    // let fail = |td:IdxTmTD, err :TypeError| { failure(Dir::Check, last_label, ctxt, td, err)  };
    // let succ = |td:IdxTmTD, sort:Sort     | { success(Dir::Check, last_label, ctxt, td, sort) };
    match nmtm {
        // We're exclusively using synthesis for name terms at the moment
        tm => {
            let mut td = synth_nmtm(last_label,ctxt,tm);
            let ty = td.typ.clone();
            if let Ok(ty) = ty {
                if ty == *sort { td }
                else {
                    td.typ = Err(TypeError::AnnoMism);
                    td
                }
            } else { td }
        },
    }  
}

pub fn synth_val(last_label:Option<&str>, ctxt:&TCtxt, val:&Val) -> TypeInfo<ValTD> {
    let fail = |td:ValTD, err :TypeError| { failure(Dir::Synth, last_label, ctxt, td, err)  };
    let succ = |td:ValTD, typ :Type     | { success(Dir::Synth, last_label, ctxt, td, typ) };
    match val {
        &Val::Var(ref x) => {
            let td = ValTD::Var(x.clone());
            match ctxt.lookup_var(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(ty) => succ(td, ty)
            }
        },
        &Val::Unit => {
            succ(ValTD::Unit, Type::Unit)
        },
        &Val::Pair(ref v0, ref v1) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = ValTD::Pair(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(ty0),Ok(ty1)) => succ(td, Type::Prod(
                    Rc::new(ty0), Rc::new(ty1),
                )),
            }
        },
        &Val::Inj1(ref v) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td = ValTD::Inj1(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Val::Inj2(ref v) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td = ValTD::Inj2(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Val::Roll(ref v) => {
            let td0 = synth_val(last_label, ctxt, v);
            // let typ0 = td0.typ.clone();
            let td = ValTD::Inj2(td0);
            // TODO: Rule for Roll
            fail(td, TypeError::Unimplemented)
        },
        &Val::Name(ref n) => {
            let td = ValTD::Name(n.clone());
            match n {
                &Name::NoParse(ref s) => fail(td, TypeError::NoParse(s.clone())),
                // TODO: generate this idx based on other refinements
                _ => succ(td, Type::Nm(IdxTm::Sing(NameTm::Name(n.clone())))),
            }
        },
        &Val::NameFn(ref nmtm) => {
            let td0 = synth_nmtm(last_label, ctxt, nmtm);
            let typ0 = td0.typ.clone();
            let td = ValTD::NameFn(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Sort::NmArrow(n0,n1)) => {
                    if (*n0 == Sort::Nm) & (*n1 == Sort::Nm) {
                        succ(td, Type::NmFn(nmtm.clone()))
                    } else { fail(td, TypeError::ParamMism(0)) }
                },
                _ => fail(td, TypeError::ValNotArrow),
            }
        },
        &Val::Anno(ref v,ref t) => {
            let td0 = check_val(last_label, ctxt, v, t);
            let typ0 = td0.typ.clone();
            let td = ValTD::Anno(td0, t.clone());
            match typ0 {
                Err(err) => fail(td, err.clone()),
                Ok(typ) => succ(td, typ.clone()),
            }
        },
        &Val::ThunkAnon(ref e) => {
            let td0 = synth_exp(last_label, ctxt, e);
            let typ0 = td0.typ.clone();
            let td = ValTD::ThunkAnon(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                // TODO: do we need the type of CBPV thunks?
                _ => fail(td, TypeError::Unimplemented),
            }
        },
        &Val::Bool(b) => {
            succ(ValTD::Bool(b), Type::Cons(TypeCons::Bool))
        },
        &Val::Nat(n) => {
            succ(ValTD::Nat(n), Type::Cons(TypeCons::Nat))
        },
        &Val::Str(ref s) => {
            succ(ValTD::Str(s.clone()), Type::Cons(TypeCons::String))
        },
        &Val::NoParse(ref s) => {
            fail(ValTD::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },
    }
}


pub fn check_val(last_label:Option<&str>, ctxt:&TCtxt, val:&Val, typ:&Type) -> TypeInfo<ValTD> {
    let fail = |td:ValTD, err :TypeError| { failure(Dir::Check, last_label, ctxt, td, err)  };
    let succ = |td:ValTD, typ :Type     | { success(Dir::Check, last_label, ctxt, td, typ) };
    match val {
        &Val::Var(ref x) => {
            let td = ValTD::Var(x.clone());
            match ctxt.lookup_var(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(ty) => {
                    if ty == *typ { succ(td, ty) }
                    else { fail(td, TypeError::AnnoMism) }
                }
            }
        },
        &Val::Unit => {
            let td = ValTD::Unit;
            if Type::Unit == *typ { succ(td, typ.clone()) }
            else { fail(td, TypeError::AnnoMism) }
        },
        &Val::Pair(ref v0, ref v1) => {
            if let Type::Prod(ref t0, ref t1) = *typ {
                let td0 = check_val(last_label, ctxt, v0, t0);
                let td1 = check_val(last_label, ctxt, v1, t1);
                let (typ0,typ1) = (td0.typ.clone(), td1.typ.clone());
                let td = ValTD::Pair(td0,td1);
                match (typ0,typ1) {
                    (Err(_),_) => fail(td, TypeError::ParamNoCheck(0)),
                    (_,Err(_)) => fail(td, TypeError::ParamNoCheck(1)),
                    (Ok(_),Ok(_)) => succ(td, typ.clone()),
                }
            } else { fail(ValTD::Pair(
                synth_val(last_label, ctxt, v0),
                synth_val(last_label, ctxt, v1),
            ), TypeError::AnnoMism) }
        },
        &Val::Inj1(ref v) => {
            if let Type::Sum(ref t1, _) = *typ {
                let td0 = check_val(last_label, ctxt, v, t1);
                let typ0 = td0.typ.clone();
                let td = ValTD::Inj1(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Ok(_) => succ(td, typ.clone()),
                }
            } else { fail(ValTD::Inj1(
                synth_val(last_label,ctxt, v)
            ), TypeError::AnnoMism) }
        },
        &Val::Inj2(ref v) => {
            if let Type::Sum(_, ref t2) = *typ {
                let td0 = check_val(last_label, ctxt, v, t2);
                let typ0 = td0.typ.clone();
                let td = ValTD::Inj2(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Ok(_) => succ(td, typ.clone()),
                }
            } else { fail(ValTD::Inj2(
                synth_val(last_label,ctxt, v)
            ), TypeError::AnnoMism) }
        },
        &Val::Roll(ref v) => {
            // TODO: Rule for Roll
            let temp_td = synth_val(last_label, ctxt, v);
            fail(ValTD::Roll(temp_td), TypeError::Unimplemented)
        },
        &Val::Name(ref n) => {
            let td = ValTD::Name(n.clone());
            if let Type::Nm(ref _idx) = *typ {
                match n { 
                    &Name::NoParse(ref s) => fail(td, TypeError::NoParse(s.clone())),
                    // TODO: check that n is a member of idx
                    _ => succ(td, typ.clone())
                }
            } else { fail(td, TypeError::AnnoMism) }
        },
        &Val::NameFn(ref nmtm) => {
            if let Type::NmFn(ref nt) = *typ {
                let td0 = check_nmtm(last_label, ctxt, nt, &Sort::NmArrow(
                    Rc::new(Sort::Nm), Rc::new(Sort::Nm),
                ));
                let typ0 = td0.typ.clone();
                let td = ValTD::NameFn(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    // TODO: check equivalence of nmtm and nt
                    Ok(_) => succ(td, typ.clone())
                }
            } else { fail(ValTD::NameFn(
                synth_nmtm(last_label, ctxt, nmtm)
            ), TypeError::AnnoMism) }
        },
        &Val::Anno(ref v,ref t) => {
            if *t == *typ {
                let td0 = check_val(last_label, ctxt, v, t);
                let typ0 = td0.typ.clone();
                let td = ValTD::Anno(td0, t.clone());
                match typ0 {
                    Err(err) => fail(td, err.clone()),
                    Ok(typ) => succ(td, typ.clone()),
                }
            } else { fail(ValTD::Anno(
                synth_val(last_label, ctxt, v), t.clone()
            ), TypeError::AnnoMism) }
        },
        &Val::ThunkAnon(ref e) => {
            if false {
                // TODO: we may need a type for CBPV thunks
                unimplemented!()
            } else { fail(ValTD::ThunkAnon(
                synth_exp(last_label, ctxt, e)
            ), TypeError::AnnoMism) }
        },
        &Val::Bool(b) => {
            let td = ValTD::Bool(b);
            if Type::Cons(TypeCons::Bool) == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::Nat(n) => {
            let td = ValTD::Nat(n);
            if Type::Cons(TypeCons::Nat) == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::Str(ref s) => {
            let td = ValTD::Str(s.clone());
            if Type::Cons(TypeCons::String) == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::NoParse(ref s) => {
            fail(ValTD::NoParse(s.clone()), TypeError::NoParse(s.clone()))
        },
        // v => {
        //     let mut td = synth_val(last_label,ctxt,v);
        //     let ty = td.typ.clone();
        //     if let Ok(ty) = ty {
        //         if ty == *typ { td }
        //         else {
        //             td.typ = Err(TypeError::AnnoMism);
        //             td
        //         }
        //     } else { td }
        // },
    }
}

pub fn synth_exp(last_label:Option<&str>, ctxt:&TCtxt, exp:&Exp) -> TypeInfo<ExpTD> {
    let fail = |td:ExpTD, err :TypeError| { failure(Dir::Synth, last_label, ctxt, td, err) };
    let succ = |td:ExpTD, typ :CEffect  | { success(Dir::Synth, last_label, ctxt, td, typ) };
    match exp {
        &Exp::AnnoC(ref e,ref ct) => {
            let td0 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::AnnoC(td0, ct.clone());
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::AnnoE(ref e,ref et) => {
            let td0 = check_exp(last_label, ctxt, e, et);
            let typ0 = td0.typ.clone();
            let td = ExpTD::AnnoE(td0, et.clone());
            match typ0 {
                Err(_) => fail(td, TypeError::AnnoMism),
                Ok(ty) => succ(td, ty),
            }
        },
        &Exp::Force(ref v) => {
            let td0 = synth_val(last_label, ctxt, v);
            let typ0 = td0.typ.clone();
            let td = ExpTD::Force(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Type::Thk(ref _idx,ref ce)) => {
                    // TODO: Compose effects
                    succ(td, (**ce).clone())
                }
                Ok(_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &Exp::Thunk(ref v,ref e) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Thunk(td0,td1);
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::Unroll(ref v,ref x,ref e) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td2 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Unroll(td0, x.clone(), td2);
            // TODO: rule for unroll
            fail(td, TypeError::Unimplemented)
        },
        &Exp::Fix(ref x,ref e) => {
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Fix(x.clone(), td1);
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::Ret(ref v) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td = ExpTD::Ret(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::DefType(ref x,ref t, ref e) => {
            let td2 = synth_exp(last_label, ctxt, e);
            // TODO: user-type kinding??
            let typ2 = td2.typ.clone();
            let td = ExpTD::DefType(x.clone(), t.clone(), td2);
            match typ2 {
                Err(_) => fail(td, TypeError::ParamNoSynth(2)),
                Ok(ty) => succ(td, ty.clone()),
            }
        },
        &Exp::Let(ref x, ref e1, ref e2) => {
            let td1 = synth_exp(last_label, ctxt, e1);
            let td2 = synth_exp(last_label, ctxt, e2);
            let td = ExpTD::Let(x.clone(), td1, td2);
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::Lam(ref x, ref e) => {
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Lam(x.clone(), td1);
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::App(ref e, ref v) => {
            let td0 = synth_exp(last_label, ctxt, e);
            let typ0 = td0.typ.clone();
            match typ0 {
                Err(_) => {
                    let td1 = synth_val(last_label, ctxt, v);
                    let td = ExpTD::App(td0,td1);
                    fail(td, TypeError::ParamNoSynth(0))
                },
                Ok(CEffect::Cons(CType::Arrow(ref ty,ref ce), ref _ef)) => {
                    let td1 = check_val(last_label, ctxt, v, ty);
                    let ty1 = td1.typ.clone();
                    let td = ExpTD::App(td0,td1);
                    match ty1 {
                        Err(_) => fail(td, TypeError::ParamMism(1)),
                        Ok(_) => {
                            // TODO: compose effects
                            succ(td, (**ce).clone())
                        }
                    }
                },
                Ok(_) => {
                    let td1 = synth_val(last_label, ctxt, v);
                    let td = ExpTD::App(td0,td1);
                    fail(td, TypeError::ParamMism(0))
                }
            }
        },
        &Exp::Split(ref v, ref x1, ref x2, ref e) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td3 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Split(td0,x1.clone(),x2.clone(),td3);
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td2 = synth_exp(last_label, ctxt, e1);
            let td4 = synth_exp(last_label, ctxt, e2);
            let td = ExpTD::Case(td0,x1.clone(),td2,x2.clone(),td4);
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::IfThenElse(ref v, ref e1, ref e2) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td1 = synth_exp(last_label, ctxt, e1);
            let td2 = synth_exp(last_label, ctxt, e2);
            let td = ExpTD::IfThenElse(td0,td1,td2);
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::Ref(ref v1,ref v2) => {
            let td0 = synth_val(last_label, ctxt, v1);
            let td1 = synth_val(last_label, ctxt, v2);
            let td = ExpTD::Ref(td0,td1);
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::Get(ref v) => {
            let td0 = synth_val(last_label, ctxt, v);
            let typ0 = td0.typ.clone();
            let td = ExpTD::Get(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Type::Ref(ref idx,ref ty)) => succ(td, CEffect::Cons(
                    CType::Lift((**ty).clone()),
                    Effect::WR(IdxTm::Empty, idx.clone())
                )),
                Ok(_) => fail(td, TypeError::GetNotRef)
            }
        },
        &Exp::Scope(ref v,ref e) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Scope(td0,td1);
            fail(td, TypeError::NoSynthRule)
        },
        // &Exp::NameFnApp(ref v1,ref v2) => {},
        // &Exp::PrimApp(PrimApp) => {},
        // &Exp::Unimp => {},
        // &Exp::DebugLabel(ref n, ref s,ref e) => {},
        // &Exp::NoParse(ref s) => {},
        _ => unimplemented!("TODO: Finish synth expressions")
    }
}

pub fn check_exp(last_label:Option<&str>, ctxt:&TCtxt, exp:&Exp, ceffect:&CEffect) -> TypeInfo<ExpTD> {
    match exp {
        // &Exp::AnnoC(ref e,ref ct) => {},
        // &Exp::AnnoE(ref e,ref et) => {},
        // &Exp::Force(ref v) => {},
        // &Exp::Thunk(ref v,ref e) => {},
        // &Exp::Unroll(ref v,ref x,ref e) => {},
        // &Exp::Fix(ref x,ref e) => {},
        // &Exp::Ret(ref v) => {},
        // &Exp::DefType(ref x,Type,ref e) => {},
        // &Exp::Let(ref x,ExpRec,ExpRec) => {},
        // &Exp::Lam(ref x, ref e) => {},
        // &Exp::App(ref e, ref v) => {},
        // &Exp::Split(ref v, ref x1, ref x2, ref e) => {},
        // &Exp::Case(ref v, ref x1, ExpRec, ref x2, ExpRec) => {},
        // &Exp::IfThenElse(ref v, ExpRec, ExpRec) => {},
        // &Exp::Ref(ref v1,ref v2) => {},
        // &Exp::Get(ref v) => {},
        // &Exp::Scope(ref v,ref e) => {},
        // &Exp::NameFnApp(ref v1,ref v2) => {},
        // &Exp::PrimApp(PrimApp) => {},
        // &Exp::Unimp => {},
        // &Exp::DebugLabel(ref s,ref e) => {},
        // &Exp::NoParse(ref s) => {},
        _ => unimplemented!("Finish check expressions")
    }
}
