/*! Bidirectional type system.

# Fungi: bidirectional type system

*/

use ast::*;
use std::fmt;
use std::rc::Rc;

pub type CtxRec = Rc<Ctx>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Ctx {
    Empty,
    Var(CtxRec,Var,Type),
    IVar(CtxRec,Var,Sort),
    TVar(CtxRec,Var,Kind),
    TCons(CtxRec,TypeCons,Kind),
    Equiv(CtxRec,IdxTm,IdxTm,Sort),
    Apart(CtxRec,IdxTm,IdxTm,Sort),
    PropTrue(CtxRec,Prop),
}
impl Ctx {
    /// bind a var and type
    pub fn var(&self,v:Var,t:Type) -> Ctx {
        Ctx::Var(Rc::new(self.clone()),v,t)
    }
    /// bind a index var and sort
    pub fn ivar(&self,v:Var,s:Sort) -> Ctx {
        Ctx::IVar(Rc::new(self.clone()),v,s)
    }
    /// bind a type var and kind
    pub fn tvar(&self,v:Var,k:Kind) -> Ctx {
        Ctx::TVar(Rc::new(self.clone()),v,k)
    }
    /// bind a type constructor and kind
    pub fn tcons(&self,d:TypeCons,k:Kind) -> Ctx {
        Ctx::TCons(Rc::new(self.clone()),d,k)
    }
    /// assume an index equivalence
    pub fn equiv(&self,i1:IdxTm,i2:IdxTm,s:Sort) -> Ctx {
        Ctx::Equiv(Rc::new(self.clone()),i1,i2,s)
    }
    /// assume an index apartness
    pub fn apart(&self,i1:IdxTm,i2:IdxTm,s:Sort) -> Ctx {
        Ctx::Apart(Rc::new(self.clone()),i1,i2,s)
    }
    /// assume a proposition is true
    pub fn prop(&self,p:Prop) -> Ctx {
        Ctx::PropTrue(Rc::new(self.clone()),p)
    }
}

impl Ctx {
    pub fn rest(&self) -> Option<CtxRec> {
        match *self {
            Ctx::Empty => None,
            Ctx::Var(ref c, _, _) |
            Ctx::IVar(ref c,_,_) |
            Ctx::TVar(ref c,_,_) |
            Ctx::TCons(ref c,_,_) |
            Ctx::Equiv(ref c,_,_,_) |
            Ctx::Apart(ref c,_,_,_) |
            Ctx::PropTrue(ref c,_) => { Some(c.clone()) },
        }
    }
    pub fn lookup_var(&self, x:&Var) -> Option<Type> {
        match *self {
            Ctx::Empty => None,
            Ctx::Var(ref c,ref v,ref t) => {
                if x == v { Some(t.clone()) } else { c.lookup_var(x) }
            },
            ref c => c.rest().unwrap().lookup_var(x)
        }
    }
    pub fn lookup_ivar(&self, x:&Var) -> Option<Sort> {
        match *self {
            Ctx::Empty => None,
            Ctx::IVar(ref c,ref v,ref s) => {
                if x == v { Some(s.clone()) } else { c.lookup_ivar(x) }
            },
            ref c => c.rest().unwrap().lookup_ivar(x)
        }
    }
    pub fn lookup_tvar(&self, x:&Var) -> Option<Kind> {
        match *self {
            Ctx::Empty => None,
            Ctx::TVar(ref c,ref v,ref k) => {
                if x == v { Some(k.clone()) } else { c.lookup_tvar(x) }
            },
            ref c => c.rest().unwrap().lookup_tvar(x)
        }
    }
    pub fn lookup_tcons(&self, x:&TypeCons) -> Option<Kind> {
        match *self {
            Ctx::Empty => None,
            Ctx::TCons(ref c,ref v,ref k) => {
                if x == v { Some(k.clone()) } else { c.lookup_tcons(x) }
            },
            ref c => c.rest().unwrap().lookup_tcons(x)                
        }
    }
}

pub trait HasClas { type Type; }

/// Typing derivation: A context, a direction, a classifier (type, sort, etc) and a rule (`node`)
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
// Proposal: pub struct Der<Rule:HasClas> {   <---- Use "Rule" not "TD" below
pub struct Der<TD:HasClas> {
    pub dir:Dir,
    pub ctxt:Ctx,    
    pub rule:Rc<TD>,                    // <-------- TODO: rename: `rule` for "typing rule"
    pub typ:Result<TD::Type,TypeError>, // <-------- TODO: rename: `clas` for "classifier"
}
impl<A:HasClas> Der<A> {
    pub fn is_err(&self) -> bool { self.typ.is_err() }
    pub fn is_ok(&self) -> bool { self.typ.is_ok() }
}

/// Name term sorting rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum NmTmRule { // <---------- "NameTmRule"; the typing derivation is `Der<NameTmRule>`
    Var(Var),
    Name(Name),
    Bin(NmTmDer, NmTmDer),
    Lam(Var,Sort,NmTmDer),
    App(NmTmDer, NmTmDer),
    NoParse(String),
}
pub type NmTmDer = Der<NmTmRule>;
impl HasClas for NmTmRule { type Type = Sort; }

/// Index term sorting rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum IdxTmRule {
    Var(Var),
    Sing(NmTmDer),
    Empty,
    Disj(IdxTmDer, IdxTmDer),
    Union(IdxTmDer, IdxTmDer),
    Unit,
    Pair(IdxTmDer, IdxTmDer),
    Proj1(IdxTmDer),
    Proj2(IdxTmDer),
    Lam(Var, Sort, IdxTmDer),
    App(IdxTmDer, IdxTmDer),
    Map(NmTmDer, IdxTmDer),
    FlatMap(IdxTmDer, IdxTmDer),
    Star(IdxTmDer, IdxTmDer),
    NoParse(String),
}
pub type IdxTmDer = Der<IdxTmRule>;
impl HasClas for IdxTmRule { type Type = Sort; }

/// Value typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ValRule {
    Var(Var),
    Unit,
    Pair(ValDer, ValDer),
    Inj1(ValDer),
    Inj2(ValDer),
    Roll(ValDer),
    Pack(Var,ValDer),
    Name(Name),
    NameFn(NmTmDer),
    Anno(ValDer,Type),
    ThunkAnon(Der<ExpRule>),
    Bool(bool),
    Nat(usize),
    Str(String),
    NoParse(String),
}
pub type ValDer = Der<ValRule>;
impl HasClas for ValRule { type Type = Type; }


/// Qualifiers for module item names
///
/// Two named objects in a module can reuse the same name if they have
/// different qualifiers (e.g., name term vs index term vs type vs value).
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Qual {
    NmTm,
    IdxTm,
    Type,
    Val
}

/// Module typing derivation
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct ModuleTD {
    /// untyped AST of the module
    pub ast: Rc<Module>,
    /// typing sub-derivations: each (var,qual) pair is unique in the list
    pub tds: Vec<((String,Qual),DeclTD)>,
}
/// Module import typing derivation
pub struct UseAllModuleTD {
    /// untyped AST of the imported module
    pub ast: UseAllModule,
    /// typing derivation for the imported module
    pub td: ModuleTD,
}
/// Declaration typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum DeclRule {
    UseAll(UseAllModule),
    NmTm (String, NmTmDer),
    IdxTm(String, IdxTmDer),
    // TODO: add kinds
    Type (String, Type), 
    Val  (String, ValDer),
    Fn   (String, ExpDer),
    NoParse(String),
}

/// Declaration typing derivation
type DeclTD = Der<DeclRule>;
impl HasClas for DeclRule { type Type = (); }
impl HasClas for DeclTD   { type Type = (); }

/// Expression typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ExpRule {
    AnnoC(ExpDer,CType),
    AnnoE(ExpDer,CEffect),
    Force(ValDer),
    Thunk(ValDer,ExpDer),
    Unroll(ValDer,Var,ExpDer),
    Unpack(Var,Var,ValDer,ExpDer),
    Fix(Var,ExpDer),
    Ret(ValDer),
    DefType(Var,Type,ExpDer),
    Let(Var,ExpDer,ExpDer),
    Lam(Var, ExpDer),
    HostFn(HostEvalFn),
    App(ExpDer, ValDer),
    Split(ValDer, Var, Var, ExpDer),
    Case(ValDer, Var, ExpDer, Var, ExpDer),
    IfThenElse(ValDer, ExpDer, ExpDer),
    Ref(ValDer,ValDer),
    Get(ValDer),
    Scope(ValDer,ExpDer),
    NameFnApp(ValDer,ValDer),
    PrimApp(PrimAppRule),
    Unimp,
    DebugLabel(Option<Name>, Option<String>,ExpDer),
    NoParse(String),
}
pub type ExpDer = Der<ExpRule>;
impl HasClas for ExpRule { type Type = CEffect; }

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum PrimAppRule {
    NatEq(ValDer,ValDer),
    NatLt(ValDer,ValDer),
    NatLte(ValDer,ValDer),
    NatPlus(ValDer,ValDer),
    NameBin(ValDer,ValDer),
    RefThunk(ValDer),
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
    ExistVarMism,
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
            TypeError::ExistVarMism => format!("identifiers of packed/unpacked existensial vars must match"),
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

fn failure<N:HasClas+debug::DerRule>
    (dir:Dir, last_label:Option<&str>,
     ctxt:&Ctx, n:N, err:TypeError) -> Der<N>
{
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to {} {} {}, error: {}", dir.short(), n.short(), N::term_desc(), err);
    Der{
        ctxt: ctxt.clone(),
        rule: Rc::new(n),
        dir: dir,
        typ: Err(err),
    }
}

fn success<N:HasClas+debug::DerRule>
    (dir:Dir, _last_label:Option<&str>,
     ctxt:&Ctx, n:N, typ:N::Type) -> Der<N>
{
    Der{
        ctxt: ctxt.clone(),
        rule: Rc::new(n),
        dir: dir,
        typ: Ok(typ)
    }
}


/// Normalize types (expand definitions and reduce applications).
///
/// To normalize types, we generally need to **expand definitions** of
/// user-defined types, and **apply them** to type or index arguments.
///
/// ### Example:
///
/// Suppose the user defines `NmOp := foralli X:NmSet. 1 + Nm[X]` in
/// the context.  Then, `NmOp [{@1}]` normalizes to `1 + Nm[{@1}]`, by
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
pub fn normal_type(last_label:Option<&str>, ctxt:&Ctx, typ:&Type) -> Type {
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
pub fn unroll_type(ctxt:&Ctx, typ:&Type) -> Option<Type> {
    /// XXX
    /// Needed to implement case in the max example; the `Seq [X][Y] Nat` arg type needs to be "reduced" and then unrolled.
    unimplemented!()
}


pub fn synth_idxtm(last_label:Option<&str>, ctxt:&Ctx, idxtm:&IdxTm) -> IdxTmDer {
    let fail = |td:IdxTmRule, err :TypeError| { failure(Dir::Synth, last_label, ctxt, td, err)  };
    let succ = |td:IdxTmRule, sort:Sort     | { success(Dir::Synth, last_label, ctxt, td, sort) };
    match idxtm {
        &IdxTm::Var(ref x) => {
            let td = IdxTmRule::Var(x.clone());
            match ctxt.lookup_ivar(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(sort) => succ(td, sort)
            }   
        }
        &IdxTm::Sing(ref nt) => {
            let td0 = synth_nmtm(last_label,ctxt,nt);
            let ty0 = td0.typ.clone();
            let td = IdxTmRule::Sing(td0);
            match ty0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(ref t) if *t == Sort::Nm => succ(td, Sort::NmSet),
                Ok(_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Empty => {
            succ(IdxTmRule::Empty, Sort::NmSet)
        },
        &IdxTm::Disj(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctxt,idx0);
            let td1 = synth_idxtm(last_label,ctxt,idx1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = IdxTmRule::Disj(td0,td1);
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
            let td = IdxTmRule::Union(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmSet),Ok(Sort::NmSet)) => succ(td, Sort::NmSet),
                (Ok(Sort::NmSet),_) => fail(td, TypeError::ParamMism(1)),
                (_,_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Unit => {
            succ(IdxTmRule::Unit, Sort::Unit)
        },
        &IdxTm::Pair(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctxt,idx0);
            let td1 = synth_idxtm(last_label,ctxt,idx1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = IdxTmRule::Pair(td0,td1);
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
            let td = IdxTmRule::Proj1(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Sort::Prod(t0,_)) => succ(td, (*t0).clone()),
                _ => fail(td, TypeError::ProjNotProd),
            }
        },
        &IdxTm::Proj2(ref idx) => {
            let td0 = synth_idxtm(last_label,ctxt,idx);
            let typ0 = td0.typ.clone();
            let td = IdxTmRule::Proj2(td0);
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
            let td = IdxTmRule::Lam(x.clone(), x_sort.clone(), td0);
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
            let td = IdxTmRule::App(td0,td1);
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
            let td = IdxTmRule::Map(td0,td1);
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
            let td = IdxTmRule::FlatMap(td0,td1);
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
            let td = IdxTmRule::Star(td0,td1);
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
            fail(IdxTmRule::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },
    }
}

pub fn check_idxtm(last_label:Option<&str>, ctxt:&Ctx, idxtm:&IdxTm, sort:&Sort) -> IdxTmDer {
    // let fail = |td:IdxTmRule, err :TypeError| { failure(Dir::Check, last_label, ctxt, td, err)  };
    // let succ = |td:IdxTmRule, sort:Sort     | { success(Dir::Check, last_label, ctxt, td, sort) };
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

pub fn synth_nmtm(last_label:Option<&str>, ctxt:&Ctx, nmtm:&NameTm) -> NmTmDer {
    let fail = |td:NmTmRule, err :TypeError| { failure(Dir::Synth, last_label, ctxt, td, err)  };
    let succ = |td:NmTmRule, sort:Sort     | { success(Dir::Synth, last_label, ctxt, td, sort) };
    match nmtm {
        &NameTm::Var(ref x) => {
            let td = NmTmRule::Var(x.clone());
            match ctxt.lookup_ivar(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(sort) => succ(td, sort)
            }
        },
        &NameTm::Name(ref n) => {
            let td = NmTmRule::Name(n.clone());
            if let &Name::NoParse(ref bad) = n {
                return fail(td, TypeError::NoParse(bad.clone()))
            }
            succ(td, Sort::Nm)
        },
        &NameTm::Bin(ref nt0, ref nt1) => {
            let td0 = synth_nmtm(last_label, ctxt, nt0);
            let td1 = synth_nmtm(last_label, ctxt, nt1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = NmTmRule::Bin(td0,td1);
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
            let td = NmTmRule::Lam(x.clone(), s.clone(), td0);
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
            let td = NmTmRule::App(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmArrow(ref t0,ref t1)),Ok(ref t2)) if **t0 == *t2 => succ(td, (**t1).clone()),
                (Ok(Sort::NmArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                _ => fail(td, TypeError::AppNotArrow),
            }
        },
        &NameTm::NoParse(ref s) => {
            fail(NmTmRule::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },
    }  
}

pub fn check_nmtm(last_label:Option<&str>, ctxt:&Ctx, nmtm:&NameTm, sort:&Sort) -> NmTmDer {
    // let fail = |td:IdxTmRule, err :TypeError| { failure(Dir::Check, last_label, ctxt, td, err)  };
    // let succ = |td:IdxTmRule, sort:Sort     | { success(Dir::Check, last_label, ctxt, td, sort) };
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

pub fn synth_val(last_label:Option<&str>, ctxt:&Ctx, val:&Val) -> ValDer {
    let fail = |td:ValRule, err :TypeError| { failure(Dir::Synth, last_label, ctxt, td, err)  };
    let succ = |td:ValRule, typ :Type     | { success(Dir::Synth, last_label, ctxt, td, typ) };
    match val {
        &Val::Var(ref x) => {
            let td = ValRule::Var(x.clone());
            match ctxt.lookup_var(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(ty) => succ(td, ty)
            }
        },
        &Val::Unit => {
            succ(ValRule::Unit, Type::Unit)
        },
        &Val::Pair(ref v0, ref v1) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = ValRule::Pair(td0,td1);
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
            let td = ValRule::Inj1(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Val::Inj2(ref v) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td = ValRule::Inj2(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Val::Roll(ref v) => {
            let td0 = synth_val(last_label, ctxt, v);
            // let typ0 = td0.typ.clone();
            let td = ValRule::Roll(td0);
            // TODO: Rule for Roll
            fail(td, TypeError::Unimplemented)
        },
        &Val::Pack(ref a, ref v) => {
            let td1 = synth_val(last_label, ctxt, v);
            let td = ValRule::Pack(a.clone(), td1);
            fail(td, TypeError::NoSynthRule)
        }
        &Val::Name(ref n) => {
            let td = ValRule::Name(n.clone());
            match n {
                &Name::NoParse(ref s) => fail(td, TypeError::NoParse(s.clone())),
                _ => succ(td, Type::Nm(IdxTm::Sing(NameTm::Name(n.clone())))),
            }
        },
        &Val::NameFn(ref nmtm) => {
            let td0 = synth_nmtm(last_label, ctxt, nmtm);
            let typ0 = td0.typ.clone();
            let td = ValRule::NameFn(td0);
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
            let td = ValRule::Anno(td0, t.clone());
            match typ0 {
                Err(err) => fail(td, err.clone()),
                Ok(typ) => succ(td, typ.clone()),
            }
        },
        &Val::ThunkAnon(ref e) => {
            let td0 = synth_exp(last_label, ctxt, e);
            let typ0 = td0.typ.clone();
            let td = ValRule::ThunkAnon(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(ty) => succ(td, Type::Thk(IdxTm::Empty, Rc::new(ty))),
            }
        },
        &Val::Bool(b) => {
            succ(ValRule::Bool(b), Type::Cons(TypeCons::Bool))
        },
        &Val::Nat(n) => {
            succ(ValRule::Nat(n), Type::Cons(TypeCons::Nat))
        },
        &Val::Str(ref s) => {
            succ(ValRule::Str(s.clone()), Type::Cons(TypeCons::String))
        },
        &Val::NoParse(ref s) => {
            fail(ValRule::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },
    }
}


pub fn check_val(last_label:Option<&str>, ctxt:&Ctx, val:&Val, typ:&Type) -> ValDer {
    let fail = |td:ValRule, err :TypeError| { failure(Dir::Check, last_label, ctxt, td, err)  };
    let succ = |td:ValRule, typ :Type     | { success(Dir::Check, last_label, ctxt, td, typ) };
    match val {
        &Val::Var(ref x) => {
            let td = ValRule::Var(x.clone());
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
            let td = ValRule::Unit;
            if Type::Unit == *typ { succ(td, typ.clone()) }
            else { fail(td, TypeError::AnnoMism) }
        },
        &Val::Pair(ref v0, ref v1) => {
            if let Type::Prod(ref t0, ref t1) = *typ {
                let td0 = check_val(last_label, ctxt, v0, t0);
                let td1 = check_val(last_label, ctxt, v1, t1);
                let (typ0,typ1) = (td0.typ.clone(), td1.typ.clone());
                let td = ValRule::Pair(td0,td1);
                match (typ0,typ1) {
                    (Err(_),_) => fail(td, TypeError::ParamNoCheck(0)),
                    (_,Err(_)) => fail(td, TypeError::ParamNoCheck(1)),
                    (Ok(_),Ok(_)) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Pair(
                synth_val(last_label, ctxt, v0),
                synth_val(last_label, ctxt, v1),
            ), TypeError::AnnoMism) }
        },
        &Val::Inj1(ref v) => {
            if let Type::Sum(ref t1, _) = *typ {
                let td0 = check_val(last_label, ctxt, v, t1);
                let typ0 = td0.typ.clone();
                let td = ValRule::Inj1(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Ok(_) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Inj1(
                synth_val(last_label,ctxt, v)
            ), TypeError::AnnoMism) }
        },
        &Val::Inj2(ref v) => {
            if let Type::Sum(_, ref t2) = *typ {
                let td0 = check_val(last_label, ctxt, v, t2);
                let typ0 = td0.typ.clone();
                let td = ValRule::Inj2(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Ok(_) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Inj2(
                synth_val(last_label,ctxt, v)
            ), TypeError::AnnoMism) }
        },
        &Val::Roll(ref v) => {
            // TODO: Rule for Roll
            let temp_td = synth_val(last_label, ctxt, v);
            fail(ValRule::Roll(temp_td), TypeError::Unimplemented)
        },
        &Val::Name(ref n) => {
            let td = ValRule::Name(n.clone());
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
                let td = ValRule::NameFn(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    // TODO: check equivalence of nmtm and nt
                    Ok(_) => succ(td, typ.clone())
                }
            } else { fail(ValRule::NameFn(
                synth_nmtm(last_label, ctxt, nmtm)
            ), TypeError::AnnoMism) }
        },
        &Val::Anno(ref v,ref t) => {
            // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
            if *t == *typ {
                let td0 = check_val(last_label, ctxt, v, t);
                let typ0 = td0.typ.clone();
                let td = ValRule::Anno(td0, t.clone());
                match typ0 {
                    Err(err) => fail(td, err.clone()),
                    Ok(typ) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Anno(
                synth_val(last_label, ctxt, v), t.clone()
            ), TypeError::AnnoMism) }
        },
        //
        // Gamma, a:g         ||- P true
        // Gamma, a:g, P true |- v <= A
        // -------------------------------------------- :: existsi
        // Gamma |- pack(a,v) <= (exists a:g|P. A)
        //
        &Val::Pack(ref a1, ref v) => {
            if let Type::Exists(a2,g,p,aa) = typ.clone() {
                if *a1 == a2 {
                    let new_ctxt1 = ctxt.ivar(a1.clone(),(*g).clone());
                    // TODO: check that p is true
                    let new_ctxt2 = new_ctxt1.prop(p);
                    let td1 = check_val(last_label, &new_ctxt2, v, &aa);
                    let typ1 = td1.typ.clone();
                    let td = ValRule::Pack(a1.clone(), td1);
                    match typ1 {
                        Err(_) => fail(td, TypeError::ParamNoCheck(1)),
                        Ok(_) => succ(td, typ.clone()),
                    }
                } else { fail(ValRule::Pack(
                    a1.clone(), synth_val(last_label, ctxt, v)
                ), TypeError::ExistVarMism) }
            } else { fail(ValRule::Pack(
                a1.clone(), synth_val(last_label, ctxt, v)
            ), TypeError::AnnoMism) }
        },
        &Val::ThunkAnon(ref e) => {
            if let Type::Thk(ref _idx, ref ce) = *typ {
                let td0 = check_exp(last_label, ctxt, &*e, &*ce);
                let typ0 = td0.typ.clone();
                let td = ValRule::ThunkAnon(td0);
                // TODO: use this once effects are implemented
                // if IdxTm::Empty != *idx {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ0 {
                    //Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Err(_) => fail(td, TypeError::CheckFailCEffect((**ce).clone())),
                    Ok(_) => succ(td, typ.clone())
                }
            } else { fail(ValRule::ThunkAnon(
                synth_exp(last_label, ctxt, e)
            ), TypeError::AnnoMism) }
        },
        &Val::Bool(b) => {
            let td = ValRule::Bool(b);
            if Type::Cons(TypeCons::Bool) == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::Nat(n) => {
            let td = ValRule::Nat(n);
            if Type::Cons(TypeCons::Nat) == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::Str(ref s) => {
            let td = ValRule::Str(s.clone());
            if Type::Cons(TypeCons::String) == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::NoParse(ref s) => {
            fail(ValRule::NoParse(s.clone()), TypeError::NoParse(s.clone()))
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

// Synthesize a typing derivation for a module, given the module AST.
pub fn synth_module(m:&Module) -> ModuleTD {
    // XXX
    panic!("TODO")
}

// TODO: import the decls of m into the typing context.
//
// TODO: We need a "decls import" judgement for modules that works by
// extending a given context with new bindings, and signaling errors
// when bindings shadow existing ones (shadowing is useful, but
// usually not intended for module-level bindings).
//
pub fn import_module(ctxt:&Ctx, m:&ModuleTD) -> Ctx {
    // XXX
    ctxt.clone()
}

pub fn synth_exp(last_label:Option<&str>, ctxt:&Ctx, exp:&Exp) -> ExpDer {
    let fail = |td:ExpRule, err :TypeError| { failure(Dir::Synth, last_label, ctxt, td, err) };
    let succ = |td:ExpRule, typ :CEffect  | { success(Dir::Synth, last_label, ctxt, td, typ) };
    match exp {
        &Exp::UseAll(ref m, ref exp) => {
            let mtd = synth_module(&(*m.module));
            let ctxt = import_module(&ctxt, &mtd);
            synth_exp(last_label, &ctxt, exp)
        }
        &Exp::AnnoC(ref e,ref ctyp) => {
            // TODO: this is a hackthat only works while we're ignoring effects,
            // we need check_exp to handle an optional effect
            let noeffect = Effect::WR(IdxTm::Empty,IdxTm::Empty);
            let td0 = check_exp(last_label, ctxt, e, &CEffect::Cons(ctyp.clone(),noeffect));
            let typ0 = td0.typ.clone();
            let td = ExpRule::AnnoC(td0, ctyp.clone());
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
            let td = ExpRule::AnnoE(td0, et.clone());
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
            let td = ExpRule::Force(td0);
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
            let td = ExpRule::DefType(x.clone(), t.clone(), td2);
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
                    let td = ExpRule::App(td0,td1);
                    fail(td, TypeError::SynthFailVal(v.clone()))
                },
                Ok(CEffect::Cons(CType::Arrow(ref ty,ref ce), ref _ef)) => {
                    let td1 = check_val(last_label, ctxt, v, ty);
                    let ty1 = td1.typ.clone();
                    let td = ExpRule::App(td0,td1);
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
                    let td = ExpRule::App(td0,td1);
                    fail(td, TypeError::UnexpectedCEffect(ce.clone()))
                }
            }
        },
        &Exp::Get(ref v) => {
            let td0 = synth_val(last_label, ctxt, v);
            let typ0 = td0.typ.clone();
            let td = ExpRule::Get(td0);
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
            let td0 = synth_val(last_label, ctxt, v);
            let typ0 = td0.typ.clone();
            let td = ExpRule::Ret(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(ty) => succ(td, CEffect::Cons(
                    CType::Lift(ty),
                    Effect::WR(IdxTm::Empty, IdxTm::Empty)
                )),
            }
        },
        &Exp::Let(ref x, ref e1, ref e2) => {
            let td1 = synth_exp(last_label, ctxt, e1);
            match td1.typ.clone() {
                Err(_) => fail(ExpRule::Let(x.clone(),td1,
                    synth_exp(last_label, ctxt, e2)
                ), TypeError::ParamNoSynth(1)),
                Ok(CEffect::Cons(CType::Lift(ty1),_eff1)) => {
                    let new_ctxt = ctxt.var(x.clone(), ty1);
                    let td2 = synth_exp(last_label, &new_ctxt, e2);
                    let typ2 = td2.typ.clone();
                    let td = ExpRule::Let(x.clone(),td1,td2);
                    match typ2 {
                        Err(_) => fail(td, TypeError::ParamNoSynth(2)),
                        Ok(CEffect::Cons(ty2,eff2)) => {
                            // TODO: combine effects
                            succ(td, CEffect::Cons(ty2, eff2))
                        },
                        _ => fail(td, TypeError::ParamMism(2)),
                    }
                },
                _ => fail(ExpRule::Let(x.clone(),td1,
                    synth_exp(last_label, ctxt, e2)
                ), TypeError::ParamMism(1)),
            }
        },
        &Exp::PrimApp(PrimApp::NameBin(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let (typ0,typ1) = (td0.typ.clone(),td1.typ.clone());
            let td = ExpRule::PrimApp(PrimAppRule::NameBin(td0,td1));
            match (typ0,typ1) {
                (Err(_),_) => fail(td,TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td,TypeError::ParamNoSynth(1)),
                (Ok(Type::Nm(_)),Ok(Type::Nm(_))) => {
                    if let (&Val::Name(ref nm0),&Val::Name(ref nm1)) = (v0,v1) {
                        succ(td, CEffect::Cons(
                            CType::Lift(Type::Nm(
                                IdxTm::Sing(NameTm::Name(Name::Bin(
                                    Rc::new(nm0.clone()),
                                    Rc::new(nm1.clone()),
                                )))
                            )),
                            Effect::WR(IdxTm::Empty, IdxTm::Empty))
                        )
                    } else { unreachable!("NameBin: Type::Nm not Val::Name") }
                },
                (Ok(Type::Nm(_)),_) => fail(td,TypeError::ParamMism(1)),
                _ => fail(td, TypeError::ParamMism(0))
            }
        },
        &Exp::PrimApp(PrimApp::RefThunk(ref v)) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td = ExpRule::PrimApp(PrimAppRule::RefThunk(td0));
            // TODO: implement
            // XXX -- for example
            fail(td, TypeError::Unimplemented)
        },        
        &Exp::PrimApp(PrimApp::NatLt(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatLt(td0,td1));
            // TODO: implement
            // XXX -- for max example:
            fail(td, TypeError::Unimplemented)
        },
        &Exp::Unimp => {
            let td = ExpRule::Unimp;
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::DebugLabel(ref n, ref s,ref e) => {
            let td2 = match s {
                &None => synth_exp(last_label, ctxt, e),
                &Some(ref lbl) => synth_exp(Some(lbl), ctxt, e),
            };
            let typ2 = td2.typ.clone();
            let td = ExpRule::DebugLabel(n.clone(),s.clone(),td2);
            match typ2 {
                // Copy/propagate the error; do not replace it with a new one.
                Err(err) => fail(td, err),
                Ok(ty) => succ(td, ty),
            }
        },
        &Exp::NoParse(ref s) => {
            fail(ExpRule::NoParse(s.clone()), TypeError::NoParse(s.clone()))
        },
        &Exp::HostFn(ref hef) => {
            fail(ExpRule::HostFn(hef.clone()),
                 TypeError::NoSynthRule)
        },
        //
        // -------- low priority:
        //
        
        &Exp::NameFnApp(ref v0,ref v1) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpRule::NameFnApp(td0,td1);
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatEq(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatEq(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatLte(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatLte(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatPlus(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctxt, v0);
            let td1 = synth_val(last_label, ctxt, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatPlus(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },

        //
        // -------- More cases (lowest priority)
        //

        &Exp::Scope(ref v,ref e) => {            
            let td0 = synth_val(last_label, ctxt, v);
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpRule::Scope(td0,td1);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },
        &Exp::Split(ref v, ref x1, ref x2, ref e) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td3 = synth_exp(last_label, ctxt, e);
            let td = ExpRule::Split(td0,x1.clone(),x2.clone(),td3);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },
        &Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td2 = synth_exp(last_label, ctxt, e1);
            let td4 = synth_exp(last_label, ctxt, e2);
            let td = ExpRule::Case(td0,x1.clone(),td2,x2.clone(),td4);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },
        &Exp::IfThenElse(ref v, ref e1, ref e2) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td1 = synth_exp(last_label, ctxt, e1);
            let td2 = synth_exp(last_label, ctxt, e2);
            let td = ExpRule::IfThenElse(td0,td1,td2);
            // TODO: implement
            fail(td, TypeError::Unimplemented) // Ok, for now.
        },
        &Exp::Ref(ref v1,ref v2) => {
            let td0 = synth_val(last_label, ctxt, v1);
            let td1 = synth_val(last_label, ctxt, v2);
            let td = ExpRule::Ref(td0,td1);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },

        // ==  
        // == -- No synth rules for these forms
        // ==
        &Exp::Thunk(ref v,ref e) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpRule::Thunk(td0,td1);
            fail(td, TypeError::NoSynthRule) // Ok
        },
        &Exp::Fix(ref x,ref e) => {
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpRule::Fix(x.clone(), td1);
            fail(td, TypeError::NoSynthRule) // Ok
        },
        &Exp::Lam(ref x, ref e) => {
            let td1 = synth_exp(last_label, ctxt, e);
            let td = ExpRule::Lam(x.clone(), td1);
            fail(td, TypeError::NoSynthRule) // Ok
        },        
        &Exp::Unroll(ref v,ref x,ref e) => {
            let td0 = synth_val(last_label, ctxt, v);
            let td2 = synth_exp(last_label, ctxt, e);
            let td = ExpRule::Unroll(td0, x.clone(), td2);
            fail(td, TypeError::Unimplemented) // Ok
        },
        &Exp::Unpack(ref i, ref x, ref v, ref e) => {
            let td2 = synth_val(last_label, ctxt, v);
            let td3 = synth_exp(last_label, ctxt, e);
            let td = ExpRule::Unpack(i.clone(),x.clone(),td2,td3);
            fail(td, TypeError::NoSynthRule)
        }
    }
}

pub fn check_exp(last_label:Option<&str>, ctxt:&Ctx, exp:&Exp, ceffect:&CEffect) -> ExpDer {
    let fail = |td:ExpRule, err :TypeError| { failure(Dir::Check, last_label, ctxt, td, err) };
    let succ = |td:ExpRule, typ :CEffect  | { success(Dir::Check, last_label, ctxt, td, typ) };
    match exp {
        &Exp::Fix(ref x,ref e) => {            
            let new_ctxt = ctxt.var(x.clone(), Type::Thk(IdxTm::Empty, Rc::new(ceffect.clone())));
            let td = check_exp(last_label, &new_ctxt, e, ceffect);
            let td_typ = td.typ.clone();
            match td_typ {
                Err(_) => fail(ExpRule::Fix(x.clone(),td), TypeError::CheckFailCEffect((ceffect.clone()))),
                Ok(_)  => succ(ExpRule::Fix(x.clone(),td), ceffect.clone())
            }
        },
        &Exp::Lam(ref x, ref e) => {
            // Strip off "forall" quantifiers in the ceffect type, moving their assumptions into the context.
            fn strip_foralls (ctxt:&Ctx, ceffect:&CEffect) -> (Ctx, CEffect) {
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
                let td = ExpRule::Lam(x.clone(), td1);
                // TODO: use this once effects are properly implemented
                // if *ef != Effect::WR(IdxTm::Empty,IdxTm::Empty) {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ1 {
                    Err(_) => fail(td, TypeError::CheckFailCEffect((ceffect.clone()))),
                    Ok(_) => succ(td, ceffect.clone()),
                }
            } else { fail(ExpRule::Lam(
                x.clone(), synth_exp(last_label, &ctxt, e)
            ), TypeError::AnnoMism) }
        },
        &Exp::Unroll(ref v,ref x,ref e) => {
            let v_td = synth_val(last_label, ctxt, v);
            match v_td.typ.clone() {
                Err(_) => {
                    let td0 = check_exp(last_label, ctxt, e, ceffect);
                    fail(ExpRule::Unroll(v_td, x.clone(), td0),
                         TypeError::SynthFailVal(v.clone()))
                }
                Ok(v_ty) => {
                    // XXX/TODO -- Call `reduce_type`,
                    // and then `unroll_type` before extending
                    // context with `v_ty`.
                    let new_ctxt = ctxt.var(x.clone(), v_ty);
                    let td0 = check_exp(last_label, &new_ctxt, e, ceffect);
                    let td0_typ = td0.typ.clone();
                    let td = ExpRule::Unroll(v_td, x.clone(), td0);
                    match td0_typ {
                        Err(_) => fail(td, TypeError::CheckFailCEffect((ceffect.clone()))),
                        Ok(_)  => succ(td, ceffect.clone())
                    }
                }
            }
        },
        ///////////////////////////////////////////////////////
        //
        // Gamma |- v => (exists a:g|P. A)
        // Gamma, b:g, [b/a]P true, x:[b/a]A |- e <= E
        // -------------------------------------------- :: unpack2
        // Gamma |- unpack(v,x.b.e) <= E                                   
        //
        // more general version of rule that permits index vars `a`
        // and `b` to differ; requires substituting an index term for
        // an index variable (index term 'b', a variable, for variable
        // 'a') in propositions, in indices and in types.
        //
        /////////////////////////////////////////////////////////
        //
        // Gamma |- v => (exists a:g|P. A)
        // Gamma, a:g, P true, x:A |- e <= E
        // ---------------------------------- :: unpack
        // Gamma |- unpack(v,x.a.e) <= E
        //
        &Exp::Unpack(ref a1, ref x, ref v, ref e) => {
            let td2 = synth_val(last_label, ctxt, v);
            match td2.typ.clone() {
                Ok(Type::Exists(ref a2, ref g, ref p, ref aa)) => {
                    if *a1 == *a2 {
                        let new_ctxt = ctxt
                            .ivar(a1.clone(),(**g).clone())
                            .prop(p.clone())
                            .var(x.clone(),(**aa).clone())
                        ;
                        let td3 = check_exp(last_label, &new_ctxt, e, &ceffect);
                        let typ3 = td3.typ.clone();
                        let td = ExpRule::Unpack(a1.clone(),x.clone(),td2,td3);
                        match typ3 {
                            Err(_) => fail(td, TypeError::ParamNoCheck(3)),
                            Ok(_) => succ(td, ceffect.clone())
                        }

                    } else {
                        // TODO: See more general version of rule, above.
                        let td3 = synth_exp(last_label, ctxt, e);
                        let td = ExpRule::Unpack(a1.clone(),x.clone(),td2,td3);
                        fail(td, TypeError::ExistVarMism)
                    }
                },
                rt => {
                    let td3 = synth_exp(last_label, ctxt, e);
                    let td = ExpRule::Unpack(a1.clone(),x.clone(),td2,td3);
                    if let Err(_) = rt { fail(td, TypeError::ParamNoSynth(2)) }
                    else { fail(td, TypeError::ParamMism(2)) }
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
                    let td = ExpRule::Case(v_td, x1.clone(), td1, x2.clone(), td2);
                    match (td1_typ, td2_typ) {
                        (Ok(_),Ok(_)) => succ(td, ceffect.clone()),
                        (_    ,_    ) => fail(td, TypeError::CheckFailCEffect((ceffect.clone()))),
                    }
                }
                Ok(t) => {
                    let td1 = check_exp(last_label, ctxt, e1, ceffect);
                    let td2 = check_exp(last_label, ctxt, e2, ceffect);
                    fail(ExpRule::Case(v_td, x1.clone(), td1, x2.clone(), td2),
                         TypeError::UnexpectedType(t))
                }
                _ => {
                    let td1 = check_exp(last_label, ctxt, e1, ceffect);
                    let td2 = check_exp(last_label, ctxt, e2, ceffect);
                    fail(ExpRule::Case(v_td, x1.clone(), td1, x2.clone(), td2),
                         TypeError::SynthFailVal(v.clone()))
                }
            }
        },
        &Exp::Let(ref x,ref e1, ref e2) => {
            if let CEffect::Cons(ref ctyp,ref _eff) = *ceffect {
                let td1 = synth_exp(last_label, ctxt, e1);
                let typ1 = td1.typ.clone();
                match typ1 {
                    Err(_) => { fail(ExpRule::Let(
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
                        let td = ExpRule::Let(x.clone(), td1,td2);
                        match typ2res {
                            Err(_) => fail(td, TypeError::ParamNoCheck(2)),
                            Ok(_) => succ(td, ceffect.clone()),
                        }
                    },
                    _ => fail(ExpRule::Let(
                        x.clone(), td1,
                        synth_exp(last_label,ctxt,e2)
                    ), TypeError::ParamMism(1)),
                }
            } else { fail(ExpRule::Let(x.clone(),
                synth_exp(last_label, ctxt, e1),
                synth_exp(last_label, ctxt, e1),
            ), TypeError::AnnoMism) }
        },
        &Exp::Ret(ref v) => {
            if let CEffect::Cons(CType::Lift(ref t),ref _ef) = *ceffect {
                let td0 = check_val(last_label, ctxt, v, t);
                let typ0 = td0.typ.clone();
                let td = ExpRule::Ret(td0);
                // TODO: use this once effects are properly implemented
                // if *ef != Effect::WR(IdxTm::Empty,IdxTm::Empty) {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ0 {
                    Err(_) => fail(td, TypeError::CheckFailType((t.clone()))),
                    Ok(_) => succ(td, ceffect.clone())
                }
            } else { fail(ExpRule::Ret(
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
        &Exp::HostFn(ref hef) => {
            succ(ExpRule::HostFn(hef.clone()), ceffect.clone())
        }        
        &Exp::Unimp => {
            succ(ExpRule::Unimp, ceffect.clone())
        },
        &Exp::DebugLabel(ref _n, ref s, ref e) => {
            match s {
                &None => check_exp(last_label, ctxt, e, ceffect),
                &Some(ref lbl) => check_exp(Some(lbl), ctxt, e, ceffect),
            }
            
        },
        &Exp::NoParse(ref s) => {
            fail(ExpRule::NoParse(s.clone()), TypeError::NoParse(s.clone()))
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



/// Stringification for debugging derivation rules
mod debug {
    use super::*;
    // rule instance in a derivation tree
    pub trait DerRule {
        /// short term family description
        fn term_desc() -> &'static str { "unknown term family" }
        /// short name for rule
        fn short(&self) -> &str { "unknown rule" }
    }

    impl DerRule for NmTmRule {
        fn term_desc() -> &'static str { "name-term" }
        fn short(&self) -> &str {
            match *self {
                NmTmRule::Var(_) => "Var",
                NmTmRule::Name(_) => "Name",
                NmTmRule::Bin(_, _) => "Bin",
                NmTmRule::Lam(_,_,_) => "Lam",
                NmTmRule::App(_, _) => "App",
                NmTmRule::NoParse(_) => "NoParse",
            }
        }
    }

    impl DerRule for IdxTmRule {
        fn term_desc() -> &'static str { "index-term" }
        fn short(&self) -> &str {
            match *self {
                IdxTmRule::Var(_) => "Var",
                IdxTmRule::Sing(_) => "Sing",
                IdxTmRule::Empty => "Empty",
                IdxTmRule::Disj(_, _) => "Disj",
                IdxTmRule::Union(_, _) => "Union",
                IdxTmRule::Unit => "Unit",
                IdxTmRule::Pair(_, _) => "Pair",
                IdxTmRule::Proj1(_) => "Proj1",
                IdxTmRule::Proj2(_) => "Proj2",
                IdxTmRule::Lam(_, _, _) => "Lam",
                IdxTmRule::App(_, _) => "App",
                IdxTmRule::Map(_, _) => "Map",
                IdxTmRule::FlatMap(_, _) => "FlatMap",
                IdxTmRule::Star(_, _) => "Star",
                IdxTmRule::NoParse(_) => "NoParse",
            }
        }
    }

    impl DerRule for ValRule {
        fn term_desc() -> &'static str { "value" }
        fn short(&self) -> &str {
            match *self {
                ValRule::Var(_) => "Var",
                ValRule::Unit => "Unit",
                ValRule::Pair(_, _) => "Pair",
                ValRule::Inj1(_) => "Inj1",
                ValRule::Inj2(_) => "Inj2",
                ValRule::Roll(_) => "Roll",
                ValRule::Pack(_,_) => "Pack",
                ValRule::Name(_) => "Name",
                ValRule::NameFn(_) => "NameFn",
                ValRule::Anno(_,_) => "Anno",
                ValRule::ThunkAnon(_) => "ThunkAnon",
                ValRule::Bool(_) => "Bool",
                ValRule::Nat(_) => "Nat",
                ValRule::Str(_) => "Str",
                ValRule::NoParse(_) => "NoParse",
            }
        }
    }

    impl DerRule for ExpRule {
        fn term_desc() -> &'static str { "expression" }
        fn short(&self) -> &str {
            match *self {
                ExpRule::AnnoC(_,_) => "AnnoC",
                ExpRule::AnnoE(_,_) => "AnnoE",
                ExpRule::Force(_) => "Force",
                ExpRule::Thunk(_,_) => "Thunk",
                ExpRule::Unroll(_,_,_) => "Unroll",
                ExpRule::Unpack(_,_,_,_) => "Unpack",
                ExpRule::Fix(_,_) => "Fix",
                ExpRule::Ret(_) => "Ret",
                ExpRule::DefType(_,_,_) => "DefType",
                ExpRule::Let(_,_,_) => "Let",
                ExpRule::Lam(_, _) => "Lam",
                ExpRule::HostFn(_) => "HostFn",
                ExpRule::App(_, _) => "App",
                ExpRule::Split(_, _, _, _) => "Split",
                ExpRule::Case(_, _, _, _, _) => "Case",
                ExpRule::IfThenElse(_, _, _) => "IfThenElse",
                ExpRule::Ref(_,_) => "Ref",
                ExpRule::Get(_) => "Get",
                ExpRule::Scope(_,_) => "Scope",
                ExpRule::NameFnApp(_,_) => "NameFnApp",
                ExpRule::PrimApp(ref p) => p.short(),
                ExpRule::Unimp => "Unimp",
                ExpRule::DebugLabel(_,_,_) => "DebugLabel",
                ExpRule::NoParse(_) => "NoParse",
            }
        }
    }
    impl DerRule for PrimAppRule {
        fn term_desc() -> &'static str { "primitive expression" }
        fn short(&self) -> &str {
            match *self {
                PrimAppRule::NatEq(_,_) => "NatEq",
                PrimAppRule::NatLt(_,_) => "NatLt",
                PrimAppRule::NatLte(_,_) => "NatLte",
                PrimAppRule::NatPlus(_,_) => "NatPlus",
                PrimAppRule::NameBin(_,_) => "NameBin",
                PrimAppRule::RefThunk(_) => "RefThunk",
            }
        }
    }
}
use self::debug::*;
