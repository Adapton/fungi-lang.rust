/*! Bidirectional type system.

# Fungi: bidirectional type system

*/

use ast::*;
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

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct TypeInfo<TD:HasType> { 
    pub dir:Dir,
    pub ctxt:TCtxt,
    pub typ:Result<TD::Type,TypeError>,
    pub node:Rc<TD>,
}
impl<A:HasType> TypeInfo<A> {
    pub fn is_err(&self) -> bool { self.typ.is_err() }
    pub fn is_ok(&self) -> bool { self.typ.is_ok() }
}

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum NameTmTD {
    Var(Var),
    Name(Name),
    Bin(TypeInfo<NameTmTD>, TypeInfo<NameTmTD>),
    Lam(Var,Sort,TypeInfo<NameTmTD>),
    App(TypeInfo<NameTmTD>, TypeInfo<NameTmTD>),
    NoParse(String),
}
impl HasType for NameTmTD { type Type = Sort; }

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum PrimAppTD {
    NatEq(TypeInfo<ValTD>,TypeInfo<ValTD>),
    NatLt(TypeInfo<ValTD>,TypeInfo<ValTD>),
    NatLte(TypeInfo<ValTD>,TypeInfo<ValTD>),
    NatPlus(TypeInfo<ValTD>,TypeInfo<ValTD>),
    NameBin(TypeInfo<ValTD>,TypeInfo<ValTD>),
    RefThunk(TypeInfo<ValTD>),
}
trait AstNode {
    fn node_desc() -> &'static str { "ast node" }
    fn short(&self) -> &str { "unknown" }
}

impl AstNode for NameTmTD {
    fn node_desc() -> &'static str { "name-term" }
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
    fn node_desc() -> &'static str { "index-term" }
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
            PrimAppTD::NatEq(_,_) => "NatEq",
            PrimAppTD::NatLt(_,_) => "NatLt",
            PrimAppTD::NatLte(_,_) => "NatLte",
            PrimAppTD::NatPlus(_,_) => "NatPlus",
            PrimAppTD::NameBin(_,_) => "NameBin",
            PrimAppTD::RefThunk(_) => "RefThunk",
        }
    }
}

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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
    ExpNotCons,
    BadCheck,
    DSLiteral,
    EmptyDT,
    Unimplemented,
    // More errors
    CheckFailType(Type),
    CheckFailCEffect(CEffect),
    SynthFailVal(Val),
    //TypeMismatch(Type1,Type2),
    UnexpectedCEffect(CEffect),
    UnexpectedType(Type),
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
            TypeError::ExpNotCons => format!("annotated a expression that was not type-and-effect"),
            TypeError::BadCheck => format!("checked type inappropriate for value"),
            TypeError::DSLiteral => format!("data structure literals not allowed"),
            TypeError::EmptyDT => format!("ambiguous empty data type"),
            TypeError::Unimplemented => format!("Internal Error: type-checking unimplemented"),
            // 
            TypeError::CheckFailType(ref t) => format!("check fail for type {:?}",t),
            TypeError::CheckFailCEffect(ref ce) => format!("check fail for ceffect {:?}",ce),
            TypeError::SynthFailVal(ref v) => format!("failed to synthesize type for value {:?}",v),
            //TypeError::TypeMismatch(ref t1, ref t2) => format!("failed to equate types {:?} (given) and {:?} (expected)", t1, t2),
            TypeError::UnexpectedCEffect(ref ce) => format!("unexpected effect type: {:?}", ce),
            TypeError::UnexpectedType(ref t) => format!("unexpected type: {:?}", t),
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


/// Reduce type applications.
///
/// To do so, we may generally need to do lookups and type
/// substitutions using the type context, to find the definitions of
/// user-defined types and apply them to type or index arguments.
///
/// ### Example:
///
/// Suppose the user defines `NmOp := foralli X:NmSet. 1 + Nm[X]` in
/// the context.  Then, `NmOp [{@1}]` reduces to `1 + Nm[{@1}]`, by
/// using the body of the definition of `NmOp`, and reducing the
/// type-index application.
///
/// ### Reducible forms (not head normal form)
///
/// The following type forms are **reducible**:
///
///   1. `(foralli a:g. A) [i]`   -- type-index application
///   2. `(forallt a:K. A) B`     -- type-type application
///   3. `User(_)` -- user-defined type name (reduces to its definition)
///
/// ### Normal forms (irreducible forms)
///
/// The following forms are "normal" (irreducible); they each have
/// intro/elim forms in the core language's program syntax:
///
///  1. Base types, sums, products
///  3. `Ref`, `Thk`, `Nm`, `(Nm->Nm)[_]`,
///  4. `exists`
///  5. `forallt`, `foralli`
///  6. `rec`
///  7. type variables, as introduced by `forallt` and `rec` (note: not the same as user-defined type names, which each have a known definition)
///  8. type applications in head normal form.
/// 
pub fn reduce_type(last_label:Option<&str>, ctxt:&TCtxt, typ:&Type) -> Type {
    /// XXX
    /// Needed to implement case in the max example; the `Seq [X][Y] Nat` arg type needs to be "reduced" and then unrolled.
    unimplemented!()
}

/*

Not head normal:
(#a. (#b. b) 3) 4
-->
(#a. 3) 4
-->
3 4
-/->

Not in normal form: (#b.b) 3) --> 3
(#x. ((#b.b) 3))

Is head normal (with lambda as outside thing)
(#x. ((#b.b) 3))

Head normal (with application as outside thing)
x 1 2 3
^
| variable here

*/

/// Unroll a `rec` type, exposing its recursive body's type structure.
///
/// ### Example 1:  
///
/// `unroll_type(rec a. 1 + a)`  
///  = `1 + (rec a. 1 + (rec a. 1 + a))`
///
/// ### Example 2:
///
/// `unroll_type(rec a. (+ 1 + a + (x a x a)))`  
///  = `(+ 1`  
///      `+ (rec a. 1 + a + (x a x a))`  
///      `+ (x (rec a. 1 + a + (x a x a)) x (rec a. 1 + a + (x a x a)))`  
///     `)`  
///
///
pub fn unroll_type(ctxt:&TCtxt, typ:&Type) -> Option<Type> {
    /// XXX
    /// Needed to implement case in the max example; the `Seq [X][Y] Nat` arg type needs to be "reduced" and then unrolled.
    unimplemented!()
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
                // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
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
                // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
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
                Ok(ty) => succ(td, Type::Thk(IdxTm::Empty, Rc::new(ty))),
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
                    // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
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
            // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
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
            if let Type::Thk(ref _idx, ref ce) = *typ {
                let td0 = check_exp(last_label, ctxt, &*e, &*ce);
                let typ0 = td0.typ.clone();
                let td = ValTD::ThunkAnon(td0);
                // TODO: use this once effects are implemented
                // if IdxTm::Empty != *idx {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ0 {
                    //Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Err(_) => fail(td, TypeError::CheckFailCEffect((**ce).clone())),
                    Ok(_) => succ(td, typ.clone())
                }
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
        &Exp::AnnoC(ref e,ref ctyp) => {
            // TODO: this is a hackthat only works while we're ignoring effects,
            // we need check_exp to handle an optional effect
            let noeffect = Effect::WR(IdxTm::Empty,IdxTm::Empty);
            let td0 = check_exp(last_label, ctxt, e, &CEffect::Cons(ctyp.clone(),noeffect));
            let typ0 = td0.typ.clone();
            let td = ExpTD::AnnoC(td0, ctyp.clone());
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                Ok(CEffect::Cons(ct,eff)) => {
                    // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
                    if *ctyp == ct { succ(td, CEffect::Cons(ct,eff)) }
                    else { fail(td, TypeError::AnnoMism) }
                },
                _ => fail(td, TypeError::ExpNotCons)
            }
        },
        &Exp::AnnoE(ref e,ref et) => {
            let td0 = check_exp(last_label, ctxt, e, et);
            let typ0 = td0.typ.clone();
            let td = ExpTD::AnnoE(td0, et.clone());
            match typ0 {
                Ok(ty) => succ(td, ty),
                Err(_err) => {                    
                    fail(td, TypeError::CheckFailCEffect((et.clone())))
                }
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
                Ok(t) => fail(td, TypeError::UnexpectedType(t.clone())),
            }
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
        &Exp::App(ref e, ref v) => {
            let td0 = synth_exp(last_label, ctxt, e);
            let typ0 = td0.typ.clone();
            match typ0 {
                Err(_) => {
                    let td1 = synth_val(last_label, ctxt, v);
                    let td = ExpTD::App(td0,td1);
                    fail(td, TypeError::SynthFailVal(v.clone()))
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
                Ok(ce) => {
                    let td1 = synth_val(last_label, ctxt, v);
                    let td = ExpTD::App(td0,td1);
                    fail(td, TypeError::UnexpectedCEffect(ce.clone()))
                }
            }
        },
        &Exp::Get(ref v) => {
            let td0 = synth_val(last_label, ctxt, v);
            let typ0 = td0.typ.clone();
            let td = ExpTD::Get(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::SynthFailVal(v.clone())),
                Ok(Type::Ref(ref idx,ref ty)) => succ(td, CEffect::Cons(
                    CType::Lift((**ty).clone()),
                    Effect::WR(IdxTm::Empty, idx.clone())
                )),
                Ok(_) => fail(td, TypeError::GetNotRef)
            }
        },
        &Exp::Ret(ref v) => {
            // XXX  -- for example
            let td0 = synth_val(last_label, ctxt, v);
            let td = ExpTD::Ret(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::Let(ref x, ref e1, ref e2) => {
            // XXX  -- for example
            let td1 = synth_exp(last_label, ctxt, e1);
            let td2 = synth_exp(last_label, ctxt, e2);
            let td = ExpTD::Let(x.clone(), td1, td2);
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::PrimApp(PrimApp::NameBin(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpTD::PrimApp(PrimAppTD::NameBin(td0,td1));
            // TODO: implement
            // XXX -- for example
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::RefThunk(ref v)) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td = ExpTD::PrimApp(PrimAppTD::RefThunk(td0));
            // TODO: implement
            // XXX -- for example
            fail(td, TypeError::Unimplemented)
        },        
        &Exp::PrimApp(PrimApp::NatLt(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpTD::PrimApp(PrimAppTD::NatLt(td0,td1));
            // TODO: implement
            // XXX -- for max example:
            fail(td, TypeError::Unimplemented)
        },
        &Exp::Unimp => {
            let td = ExpTD::Unimp;
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::DebugLabel(ref n, ref s,ref e) => {
            let td2 = synth_exp(last_label, ctxt, e);
            let typ2 = td2.typ.clone();
            let td = ExpTD::DebugLabel(n.clone(),s.clone(),td2);
            match typ2 {
                // Copy/propagate the error; do not replace it with a new one.
                Err(err) => fail(td, err),
                Ok(ty) => succ(td, ty),
            }
        },
        &Exp::NoParse(ref s) => {
            fail(ExpTD::NoParse(s.clone()), TypeError::NoParse(s.clone()))
        },

        //
        // -------- low priority:
        //
        
        &Exp::NameFnApp(ref v0,ref v1) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpTD::NameFnApp(td0,td1);
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatEq(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpTD::PrimApp(PrimAppTD::NatEq(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatLte(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpTD::PrimApp(PrimAppTD::NatLte(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatPlus(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpTD::PrimApp(PrimAppTD::NatPlus(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },

        //
        // -------- More cases (lowest priority)
        //

        &Exp::Scope(ref v,ref e) => {            
            let td0 = synth_val(last_label, ctxt, v);
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Scope(td0,td1);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },
        &Exp::Split(ref v, ref x1, ref x2, ref e) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td3 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Split(td0,x1.clone(),x2.clone(),td3);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },
        &Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td2 = synth_exp(last_label, ctxt, e1);
            let td4 = synth_exp(last_label, ctxt, e2);
            let td = ExpTD::Case(td0,x1.clone(),td2,x2.clone(),td4);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },
        &Exp::IfThenElse(ref v, ref e1, ref e2) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td1 = synth_exp(last_label, ctxt, e1);
            let td2 = synth_exp(last_label, ctxt, e2);
            let td = ExpTD::IfThenElse(td0,td1,td2);
            // TODO: implement
            fail(td, TypeError::Unimplemented) // Ok, for now.
        },
        &Exp::Ref(ref v1,ref v2) => {
            let td0 = synth_val(last_label, ctxt, v1);
            let td1 = synth_val(last_label, ctxt, v2);
            let td = ExpTD::Ref(td0,td1);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },

        // ==  
        // == -- No synth rules for these forms
        // ==
        &Exp::Thunk(ref v,ref e) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Thunk(td0,td1); // Ok
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::Fix(ref x,ref e) => {
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Fix(x.clone(), td1);
            fail(td, TypeError::NoSynthRule) // Ok
        },
        &Exp::Lam(ref x, ref e) => {
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Lam(x.clone(), td1);
            fail(td, TypeError::NoSynthRule) // Ok
        },        
        &Exp::Unroll(ref v,ref x,ref e) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td2 = synth_exp(last_label, ctxt, e);
            let td = ExpTD::Unroll(td0, x.clone(), td2);
            fail(td, TypeError::Unimplemented) // Ok
        },
    }
}

pub fn check_exp(last_label:Option<&str>, ctxt:&TCtxt, exp:&Exp, ceffect:&CEffect) -> TypeInfo<ExpTD> {
    let fail = |td:ExpTD, err :TypeError| { failure(Dir::Check, last_label, ctxt, td, err) };
    let succ = |td:ExpTD, typ :CEffect  | { success(Dir::Check, last_label, ctxt, td, typ) };
    match exp {
        &Exp::Fix(ref x,ref e) => {            
            let new_ctxt = ctxt.var(x.clone(), Type::Thk(IdxTm::Empty, Rc::new(ceffect.clone())));
            let td = check_exp(last_label, &new_ctxt, e, ceffect);
            let td_typ = td.typ.clone();
            match td_typ {
                Err(_) => fail(ExpTD::Fix(x.clone(),td), TypeError::CheckFailCEffect((ceffect.clone()))),
                Ok(_)  => succ(ExpTD::Fix(x.clone(),td), ceffect.clone())
            }
        },
        &Exp::Lam(ref x, ref e) => {
            // Strip off "forall" quantifiers in the ceffect type, moving their assumptions into the context.
            fn strip_foralls (ctxt:&TCtxt, ceffect:&CEffect) -> (TCtxt, CEffect) {
                match ceffect {
                    &CEffect::ForallType(ref _a, ref _kind, ref ceffect) => {
                        // TODO: extend context with _x, etc.
                        strip_foralls(ctxt, ceffect)
                    },
                    &CEffect::ForallIdx(ref _a, ref _sort, ref _prop, ref ceffect) => {
                        // TODO: extend context with _x, etc.
                        strip_foralls(ctxt, ceffect)
                    },
                    &CEffect::Cons(_, _) => { (ctxt.clone(), ceffect.clone()) }
                    &CEffect::NoParse(_) => { (ctxt.clone(), ceffect.clone()) }
                }
            }
            let (ctxt, ceffect) = strip_foralls(ctxt, ceffect);            
            if let CEffect::Cons(CType::Arrow(ref at,ref et),ref _ef) = ceffect {
                let new_ctxt = ctxt.var(x.clone(),at.clone());
                let td1 = check_exp(last_label, &new_ctxt, e, et);
                let typ1 = td1.typ.clone();
                let td = ExpTD::Lam(x.clone(), td1);
                // TODO: use this once effects are properly implemented
                // if *ef != Effect::WR(IdxTm::Empty,IdxTm::Empty) {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ1 {
                    Err(_) => fail(td, TypeError::CheckFailCEffect((ceffect.clone()))),
                    Ok(_) => succ(td, ceffect.clone()),
                }
            } else { fail(ExpTD::Lam(
                x.clone(), synth_exp(last_label, &ctxt, e)
            ), TypeError::AnnoMism) }
        },
        &Exp::Unroll(ref v,ref x,ref e) => {
            let v_td = synth_val(last_label, ctxt, v);
            match v_td.typ.clone() {
                Err(_) => {
                    let td0 = check_exp(last_label, ctxt, e, ceffect);
                    fail(ExpTD::Unroll(v_td, x.clone(), td0),
                         TypeError::SynthFailVal(v.clone()))
                }
                Ok(v_ty) => {
                    // XXX/TODO -- Call `reduce_type`,
                    // and then `unroll_type` before extending
                    // context with `v_ty`.
                    let new_ctxt = ctxt.var(x.clone(), v_ty);
                    let td0 = check_exp(last_label, &new_ctxt, e, ceffect);
                    let td0_typ = td0.typ.clone();
                    let td = ExpTD::Unroll(v_td, x.clone(), td0);
                    match td0_typ {
                        Err(_) => fail(td, TypeError::CheckFailCEffect((ceffect.clone()))),
                        Ok(_)  => succ(td, ceffect.clone())
                    }
                }
            }
        },
        &Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2) => {
            let v_td = synth_val(last_label, ctxt, v);
            match v_td.typ.clone() {
                Ok(Type::Sum(ty1, ty2)) => {
                    let new_ctxt1 = ctxt.var(x1.clone(), (*ty1).clone());
                    let new_ctxt2 = ctxt.var(x2.clone(), (*ty2).clone());
                    let td1 = check_exp(last_label, &new_ctxt1, e1, ceffect);
                    let td1_typ = td1.typ.clone();
                    let td2 = check_exp(last_label, &new_ctxt2, e2, ceffect);
                    let td2_typ = td2.typ.clone();
                    let td = ExpTD::Case(v_td, x1.clone(), td1, x2.clone(), td2);
                    match (td1_typ, td2_typ) {
                        (Ok(_),Ok(_)) => succ(td, ceffect.clone()),
                        (_    ,_    ) => fail(td, TypeError::CheckFailCEffect((ceffect.clone()))),
                    }
                }
                Ok(t) => {
                    let td1 = check_exp(last_label, ctxt, e1, ceffect);
                    let td2 = check_exp(last_label, ctxt, e2, ceffect);
                    fail(ExpTD::Case(v_td, x1.clone(), td1, x2.clone(), td2),
                         TypeError::UnexpectedType(t))
                }
                _ => {
                    let td1 = check_exp(last_label, ctxt, e1, ceffect);
                    let td2 = check_exp(last_label, ctxt, e2, ceffect);
                    fail(ExpTD::Case(v_td, x1.clone(), td1, x2.clone(), td2),
                         TypeError::SynthFailVal(v.clone()))
                }
            }
        },
        &Exp::Let(ref x,ref e1, ref e2) => {
            if let CEffect::Cons(ref ctyp,ref _eff) = *ceffect {
                let td1 = synth_exp(last_label, ctxt, e1);
                let typ1 = td1.typ.clone();
                match typ1 {
                    Err(_) => { fail(ExpTD::Let(
                        x.clone(), td1,
                        synth_exp(last_label, ctxt, e2)
                    ), TypeError::ParamNoSynth(1)) },
                    Ok(CEffect::Cons(CType::Lift(ref ct1),ref _eff1)) => {
                        let new_ctxt = ctxt.var(x.clone(),ct1.clone());
                        // TODO: compute this effect
                        let eff2 = Effect::WR(IdxTm::Empty,IdxTm::Empty);
                        let typ2 = CEffect::Cons(ctyp.clone(), eff2);
                        let td2 = check_exp(last_label, &new_ctxt, e2, &typ2);
                        let typ2res = td2.typ.clone();
                        let td = ExpTD::Let(x.clone(), td1,td2);
                        match typ2res {
                            Err(_) => fail(td, TypeError::ParamNoCheck(2)),
                            Ok(_) => succ(td, ceffect.clone()),
                        }
                    },
                    _ => fail(ExpTD::Let(
                        x.clone(), td1,
                        synth_exp(last_label,ctxt,e2)
                    ), TypeError::ParamMism(1)),
                }
            } else { fail(ExpTD::Let(x.clone(),
                synth_exp(last_label, ctxt, e1),
                synth_exp(last_label, ctxt, e1),
            ), TypeError::AnnoMism) }
        },
        &Exp::Ret(ref v) => {
            if let CEffect::Cons(CType::Lift(ref t),ref _ef) = *ceffect {
                let td0 = check_val(last_label, ctxt, v, t);
                let typ0 = td0.typ.clone();
                let td = ExpTD::Ret(td0);
                // TODO: use this once effects are properly implemented
                // if *ef != Effect::WR(IdxTm::Empty,IdxTm::Empty) {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ0 {
                    Err(_) => fail(td, TypeError::CheckFailType((t.clone()))),
                    Ok(_) => succ(td, ceffect.clone())
                }
            } else { fail(ExpTD::Ret(
                synth_val(last_label,ctxt,v)
            ), TypeError::AnnoMism) }
        },
        
        // XXX: TODO next:
        //   &Exp::Split(ref v, ref x1, ref x2, ref e) => {},
        //   &Exp::IfThenElse(ref v, ExpRec, ExpRec) => {},
        //
        // TODO later:
        //   &Exp::Scope(ref v,ref e) => {},
        //
        //
        // Later and/or use synth rule:
        //   &Exp::App(ref e, ref v) => {},
        //   &Exp::Force(ref v) => {},
        //   &Exp::Get(ref v) => {},
        //   &Exp::DefType(ref x,Type,ref e) => {},
        //   &Exp::AnnoC(ref e,ref ct) => {},
        //   &Exp::AnnoE(ref e,ref et) => {},      
        //   &Exp::Thunk(ref v,ref e) => {},
        //   &Exp::Ref(ref v1,ref v2) => {},
        //   &Exp::PrimApp(PrimApp) => {},
        //   &Exp::NameFnApp(ref v1,ref v2) => {},
        //
        &Exp::Unimp => {
            succ(ExpTD::Unimp, ceffect.clone())
        },
        &Exp::DebugLabel(ref _s, ref _n, ref e) => {
            // TODO: update last_label here?
            check_exp(last_label, ctxt, e, ceffect)
        },
        &Exp::NoParse(ref s) => {
            fail(ExpTD::NoParse(s.clone()), TypeError::NoParse(s.clone()))
        },
        e => {
            let mut td = synth_exp(last_label,ctxt,e);
            let ty = td.typ.clone();
            if let Ok(ty) = ty {
                // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
                if ty == *ceffect { td }
                else {
                    td.typ = Err(TypeError::AnnoMism);
                    td
                }
            } else { td }
        },
    }
}
