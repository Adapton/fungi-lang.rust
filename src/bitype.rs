/*! Bidirectional type system. */

use ast::*;
use std::fmt;
use std::rc::Rc;

use normal;
use decide;
use subst;
use expand;

/// "Extra" typing information carried by the typing judgements
#[deriven(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Ext {
    /// The last programmer-chosen label encountered in the AST; for visualizations, error messages, etc.
    pub last_label:Option<Rc<String>>,
    /// Write scope, as a (sorted) name term function (of sort `Nm -> Nm`).
    pub write_scope: NameTm,
}

impl Ext {
    pub fn empty () -> Ext {
        Ext {
            // No labels yet.
            last_label:None,
            // The initial/default/neutral write scope is the the
            // "ambient" write scope, denoted as `NameTm::WriteScope`.
            //
            // All other write scopes are functions that compose with
            // this one (where this function is always the "last"
            // function in the composition).
            write_scope:NameTm::WriteScope,
        }
    }
}


/// Typing context
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Ctx {
    Empty,
    /// Define a type term to be carried in the type context
    Def(CtxRec,Var,Term),
    /// Define a value variable's type
    Var(CtxRec,Var,Type),
    /// Define a name/index variable's sort
    IVar(CtxRec,Var,Sort),
    /// Define a type variable's kind
    TVar(CtxRec,Var,Kind),
    /// Assume an index term equivalence, at a common sort
    Equiv(CtxRec,IdxTm,IdxTm,Sort),
    /// Assume an index term apartness, at a common sort
    Apart(CtxRec,IdxTm,IdxTm,Sort),
    /// Assume a proposition is true
    PropTrue(CtxRec,Prop),
}
pub type CtxRec = Rc<Ctx>;

/// Type terms; each can be defined by a module declaration,
/// and carried (by identifier name) in the typing context, and used
/// (by identifier name) to construct terms used in typing
/// derivations.
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Term {
    NmTm(NameTm),
    IdxTm(IdxTm),
    Type(Type),
}

impl Ctx {
    /// define a term
    pub fn def(&self,v:Var,t:Term) -> Ctx {
        Ctx::Def(Rc::new(self.clone()),v,t)
    }
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
        match p {
            // Avoid adding the trivial prop to the context, to make them smaller/shorter
            Prop::Tt => self.clone(),
            _ => Ctx::PropTrue(Rc::new(self.clone()),p)
        }
    }
    // append another context to the given one
    pub fn append(&self,other:&Ctx) -> Ctx {
        match *self {
            Ctx::Empty => other.clone(),
            Ctx::Def(ref c, ref x, ref t)  => Ctx::Def(c.append_rec(other), x.clone(), t.clone()),
            Ctx::Var(ref c, ref x, ref a)  => Ctx::Var(c.append_rec(other), x.clone(), a.clone()),
            Ctx::IVar(ref c, ref x, ref g) => Ctx::IVar(c.append_rec(other), x.clone(), g.clone()),
            Ctx::TVar(ref c, ref x, ref k) => Ctx::TVar(c.append_rec(other), x.clone(), k.clone()),
            Ctx::PropTrue(ref c, ref prop) => Ctx::PropTrue(c.append_rec(other), prop.clone()),
            Ctx::Equiv(ref c, ref i, ref j, ref g) => Ctx::Equiv(c.append_rec(other), i.clone(), j.clone(), g.clone()),
            Ctx::Apart(ref c, ref i, ref j, ref g) => Ctx::Apart(c.append_rec(other), i.clone(), j.clone(), g.clone()),
        }
    }
    pub fn append_rec(&self,other:&Ctx) -> Rc<Ctx> {
        Rc::new(self.append(other))
    }
}

impl Ctx {
    pub fn rest(&self) -> Option<CtxRec> {
        match *self {
            Ctx::Empty => None,
            Ctx::Def(ref c,_,_) |
            Ctx::Var(ref c, _, _) |
            Ctx::IVar(ref c,_,_) |
            Ctx::TVar(ref c,_,_) |
            Ctx::Equiv(ref c,_,_,_) |
            Ctx::Apart(ref c,_,_,_) |
            Ctx::PropTrue(ref c,_) => { Some(c.clone()) },
        }
    }
    pub fn lookup_var(&self, x:&Var) -> Option<Type> {
        match *self {
            Ctx::Empty => None,
            Ctx::Var(ref c,ref y,ref a) => {
                if x == y { Some(a.clone()) } else { c.lookup_var(x) }
            },
            ref c => c.rest().unwrap().lookup_var(x)
        }
    }
    pub fn lookup_ivar(&self, x:&Var) -> Option<Sort> {
        match *self {
            Ctx::Empty => None,
            Ctx::IVar(ref c,ref y,ref g) => {
                if x == y { Some(g.clone()) } else { c.lookup_ivar(x) }
            },
            ref c => c.rest().unwrap().lookup_ivar(x)
        }
    }
    pub fn lookup_tvar(&self, x:&Var) -> Option<Kind> {
        match *self {
            Ctx::Empty => None,
            Ctx::TVar(ref c,ref y,ref k) => {
                if x == y { Some(k.clone()) } else { c.lookup_tvar(x) }
            },
            ref c => c.rest().unwrap().lookup_tvar(x)
        }
    }
    pub fn lookup_type_def(&self, x:&Var) -> Option<Type> {
        match *self {
            Ctx::Empty => None,
            Ctx::Def(ref c,ref y, Term::Type(ref a)) => {
                if x == y { Some(a.clone()) } else { c.lookup_type_def(x) }
            },
            ref c => c.rest().unwrap().lookup_type_def(x)
        }        
    }    
    pub fn lookup_idxtm_def(&self, x:&Var) -> Option<IdxTm> {
        match *self {
            Ctx::Empty => None,
            Ctx::Def(ref c,ref y, Term::IdxTm(ref i)) => {
                if x == y { Some(i.clone()) } else { c.lookup_idxtm_def(x) }
            },
            ref c => c.rest().unwrap().lookup_idxtm_def(x)
        }        
    }
    pub fn lookup_nmtm_def(&self, x:&Var) -> Option<NameTm> {
        match *self {
            Ctx::Empty => None,
            Ctx::Def(ref c,ref y, Term::NmTm(ref n)) => {
                if x == y { Some(n.clone()) } else { c.lookup_nmtm_def(x) }
            },
            ref c => c.rest().unwrap().lookup_nmtm_def(x)
        }        
    }
    //TODO: Return a Vec<_>; try each possible decomposition.
    pub fn find_defs_for_idxtm_var(&self, x:&Var) -> Option<IdxTm> {
        match self {
            &Ctx::Empty => None,
            &Ctx::PropTrue(_, Prop::Equiv(IdxTm::Var(ref x_), ref i,_)) if x == x_ => Some(i.clone()),
            &Ctx::PropTrue(_, Prop::Equiv(ref i, IdxTm::Var(ref x_),_)) if x == x_ => Some(i.clone()),
            _ => self.rest().unwrap().find_defs_for_idxtm_var(x)
        }
    }
    pub fn only_defs(&self) -> Ctx {
        match self {
            &Ctx::Empty => Ctx::Empty,
            &Ctx::Def(ref c, ref x, ref t) => {
                Ctx::Def(c.clone(), x.clone(), t.clone())
            }
            _ => self.rest().unwrap().only_defs()
        }
    }
}

pub trait HasClas {
    type Term : fmt::Debug;
    type Clas;    
    fn tm_fam() -> String;
}

/// Typing derivation: A context (`ctx`), a direction (`dir`), a classifier (type, sort, etc) and a rule (`rule`).
#[derive(Clone,Debug,Eq,Hash)]
pub struct Der<Rule:HasClas+debug::DerRule> {
    // TODO: Add this "extra info" to the derivations; may break HFI in the short term.
    //pub ext:Ext,
    pub ctx:Ctx,
    pub dir:Dir<Rule>,
    pub term:Rc<Rule::Term>,
    pub clas:Result<Rule::Clas,TypeError>,
    pub rule:Rc<Rule>,
    pub vis:DerVis,
}
impl<Rule:HasClas+debug::DerRule> PartialEq for Der<Rule> where
    Rule: PartialEq,
    Rule::Clas: PartialEq
{
    // we only check rule and class for equality
    fn eq(&self, other:&Self) -> bool {
        self.rule == other.rule &&
        match (&self.clas,&other.clas) {
            (&Ok(ref s),&Ok(ref o)) => s == o,
            // treat all errors as equal, they depend on context
            (&Err(_),&Err(_)) => true,
            _ => false,
        }
    }
}
impl<Rule:HasClas+debug::DerRule> Der<Rule> {
    pub fn is_err(&self) -> bool { self.clas.is_err() }
    pub fn is_ok(&self) -> bool { self.clas.is_ok() }
}
/// Information for visualizing derivation trees in HFI
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct DerVis {
    /// Term family name, for HFI
    pub tmfam:String,
    /// `true` for _local_ errors that should be visually indicated at
    /// the given AST/derivation node, and `false` for both non-local
    /// errors and `Ok` nodes.
    pub local_err:bool,
}


/// Name term sorting rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum NmTmRule {
    /// Name-term level variable `x`, of some sort `g`:
    ///
    /// ```text
    ///  Γ(x) = g
    /// ----------- :: Var
    ///  Γ ⊢ x : g
    /// ```
    Var(Var),
    /// Injected value-level variable `x`, of type `Nm[i]`, for some name set `i`:
    ///
    /// ```text
    ///  Γ(x) = Nm[i]
    /// -------------- :: ValVar
    ///  Γ ⊢ ~x : Nm
    /// ```
    ValVar(Var),
    /// ```text
    /// ------------ :: Name
    ///  Γ ⊢ n : Nm
    /// ```
    Name(Name),
    /// ```text
    ///  Γ ⊢ N : Nm
    ///  Γ ⊢ M : Nm
    /// --------------- :: Bin
    ///  Γ ⊢ N * M : Nm
    /// ```    
    Bin(NmTmDer, NmTmDer),
    /// ```text
    ///  Γ, x:g1 ⊢ M : g2
    /// ------------------------- :: Lam
    ///  Γ ⊢ #x:g1. M : g1 -> g2
    /// ```
    Lam(Var,Sort,NmTmDer),
    /// ```text
    ///  Γ ⊢ M : g1 -> g2
    ///  Γ ⊢ N : g1
    /// ------------------ :: App
    ///  Γ ⊢ [M] N : g2
    /// ```
    App(NmTmDer, NmTmDer),
    /// `@@ : Nm -> Nm`
    ///
    /// This is the initial/default/neutral/ambient write scope.  All
    /// other write scopes are functions that compose with this one
    /// (where this function is always the "last" function in the
    /// composition).
    WriteScope,    
    NoParse(String),
}
pub type NmTmDer = Der<NmTmRule>;
impl HasClas for NmTmRule {
    type Term = NameTm;
    type Clas = Sort;
    fn tm_fam() -> String { "NmTm".to_string() }
}

/// Index term sorting rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum IdxTmRule {
    Var(Var),
    Sing(NmTmDer),
    Empty,
    Apart(IdxTmDer, IdxTmDer),
    Union(IdxTmDer, IdxTmDer),
    Bin(IdxTmDer, IdxTmDer),
    Unit,
    Pair(IdxTmDer, IdxTmDer),
    Proj1(IdxTmDer),
    Proj2(IdxTmDer),
    Lam(Var, Sort, IdxTmDer),
    WriteScope,
    App(IdxTmDer, IdxTmDer),
    Map(NmTmDer, IdxTmDer),
    MapStar(NmTmDer, IdxTmDer),
    FlatMap(IdxTmDer, IdxTmDer),
    FlatMapStar(IdxTmDer, IdxTmDer),
    NoParse(String),
    /// For normal::NmSet index terms
    NmSet,
}
pub type IdxTmDer = Der<IdxTmRule>;
impl HasClas for IdxTmRule {
    type Term = IdxTm;
    type Clas = Sort;
    fn tm_fam () -> String { "IdxTm".to_string() }
}

/// Value typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ValRule {
    Var(Var),
    Unit,
    Pair(ValDer, ValDer),
    Inj1(ValDer),
    Inj2(ValDer),
    Roll(ValDer),
    Pack(IdxTmDer,ValDer),
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
impl HasClas for ValRule {
    type Term = Val;
    type Clas = Type;
    fn tm_fam () -> String { "Val".to_string() }
}


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

/// Module item derivation; wraps a `DeclDer` with additional structure
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct ItemDer {
    pub doc:Option<String>,
    pub qual:Qual,
    pub var:String,
    pub der:DeclDer,
}
/// Module item typing rule; each `Decl` is typed by an `ItemRule`
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ItemRule {
    UseAll(UseAllModuleDer),
    Bind(ItemDer),
    NoParse(String),
}
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Module typing derivation
pub struct ModuleDer {
    /// untyped AST of the module
    pub ast: Rc<Module>,
    /// typing sub-derivations for each module item: each `ModuleVar` is unique
    pub tds: Vec<ItemRule>,
    /// the context exported by this module to modules that use it
    pub ctx_out: Ctx,
}
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Module import typing derivation
pub struct UseAllModuleDer {
    /// untyped AST of the imported module
    pub ast: UseAllModule,
    /// typing derivation for the imported module
    pub der: ModuleDer,
}
/// Module declaration typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum DeclRule {
    UseAll(UseAllModuleDer),
    NmTm (String, NmTmDer),
    IdxTm(String, IdxTmDer),
    // TODO: add kinds
    Type (String, Type), 
    Val  (String, ValDer),
    Fn   (String, ValDer),
}
/// Classifier for declared object in a module
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum DeclClas {
    /// Classifier `g` for name terms `N` and index terms `i`
    Sort(Sort),
    /// Classifier `K` for types `A`
    Kind(Kind),
    /// Classifier `A` for values `v`
    Type(Type),
    /// Classifier `E` for function bodies `e` (implied thunk type is `Thk[0] E`)
    CEffect(CEffect),
}
/// Module declaration typing derivation
pub type DeclDer = Der<DeclRule>;
impl HasClas for DeclRule {
    type Term = ();
    type Clas = DeclClas;
    fn tm_fam () -> String { "Decl".to_string() }
}

/// Expression typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ExpRule {
    UseAll(UseAllModuleDer,ExpDer),
    Decls(Vec<ItemRule>,ExpDer),
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
    IdxApp(ExpDer, IdxTmDer),
    Split(ValDer, Var, Var, ExpDer),
    Case(ValDer, Var, ExpDer, Var, ExpDer),
    IfThenElse(ValDer, ExpDer, ExpDer),
    Ref(ValDer,ValDer),
    Get(ValDer),
    WriteScope(ValDer,ExpDer),
    NameFnApp(ValDer,ValDer),
    PrimApp(PrimAppRule),
    Unimp,
    DebugLabel(Option<Name>, Option<String>,ExpDer),
    NoParse(String),
}
pub type ExpDer = Der<ExpRule>;
impl HasClas for ExpRule {
    type Term = Exp;
    type Clas = CEffect;
    fn tm_fam () -> String { "Exp".to_string() }
}

/// Primitive application typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum PrimAppRule {
    NatEq(ValDer,ValDer),
    NatLt(ValDer,ValDer),
    NatLte(ValDer,ValDer),
    NatPlus(ValDer,ValDer),
    NameBin(ValDer,ValDer),
    RefThunk(ValDer),
}

/// Bidirectional direction: _Synthesis_ vs _Checking_
///
/// Checking direction has an associated system of rules, and
/// classifier for the check, e.g., the system of rules for values and
/// expressions check against a `Type` or a `CEffect`, respectively.
///
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Dir<R:HasClas+debug::DerRule> {
    Synth,
    Check(R::Clas),
}
impl<R:HasClas+debug::DerRule> Dir<R> {
    fn short(&self) -> &str {
        match *self {
            Dir::Synth    => "synth",
            Dir::Check(_) => "check",
        }
    }
}

/// Typing error
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum TypeError {
    VarNotInScope(String),
    IdentNotInScope(String),
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
    ScopeNotNmTm,
    GetNotRef,
    ExpNotCons,
    BadCheck,
    DSLiteral,
    EmptyDT,
    Unimplemented,
    // More errors
    CheckFailType(Type),
    CheckFailCEffect(CEffect),
    CheckFailArrow(CEffect),    
    SynthFailVal(Val),
    UnexpectedCEffect(CEffect),
    UnexpectedType(Type),
    EffectError(decide::effect::Error),
    
    Later(Rc<TypeError>),
    Inside(Rc<TypeError>),
    
    // error in subderivation; for tree-shaped AST nodes e.g. `App`, and value forms.
    Subder,
    Mismatch,
    MismatchSort(Sort,Sort),
    SubsumptionFailure(CEffect,CEffect),
}

fn debug_truncate<X:fmt::Debug>(x: &X) -> String {
    let x = format!("{:?}", x);
    format!("\n\t`{:.80}{}", x, if x.len() > 80 { " ...`" } else { "`" } )
}

impl fmt::Display for TypeError {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        let s = match *self {
            TypeError::VarNotInScope(ref s) => format!("variable {} not in scope",s),
            TypeError::IdentNotInScope(ref i) => format!("identifier {} not in scope",i),
            TypeError::NoParse(ref s) => format!("term did not parse: `{}`",s),
            TypeError::AnnoMism => format!("annotation mismatch"),
            TypeError::NoSynthRule => format!("no synth rule found, try an annotation"),
            TypeError::NoCheckRule => format!("no check rule found"),
            TypeError::InvalidPtr => format!("invalid pointer"),
            TypeError::ParamMism(num) => format!("parameter {} type incorrect",num),
            TypeError::ParamNoSynth(num) => format!("parameter {} unknown type",num),
            TypeError::ParamNoCheck(num) => format!("parameter {} type mismatch ",num),
            TypeError::ProjNotProd => format!("projection of non-product type"),
            TypeError::ValNotArrow => format!("this value requires an arrow type"),
            TypeError::AppNotArrow => format!("application of non-arrow type"),
            TypeError::ScopeNotNmTm => format!("scope value was not a name term"),
            TypeError::GetNotRef => format!("get from a non-ref val"),
            TypeError::ExpNotCons => format!("annotated a expression that was not type-and-effect"),
            TypeError::BadCheck => format!("checked type inappropriate for value"),
            TypeError::DSLiteral => format!("data structure literals not allowed"),
            TypeError::EmptyDT => format!("ambiguous empty data type"),
            TypeError::Unimplemented => format!("Internal Error: type-checking unimplemented"),
            TypeError::CheckFailType(ref t) => format!("check fail for type {}", debug_truncate(t)),
            TypeError::CheckFailCEffect(ref _ce) => format!("check fail for ceffect ..."),
            TypeError::CheckFailArrow(ref _ce) => format!("check fail for ceffect; expected arrow"),
            TypeError::SynthFailVal(ref v) => format!("failed to synthesize type for value {}",debug_truncate(v)),
            TypeError::UnexpectedCEffect(ref ce) => format!("unexpected effect type: {}", debug_truncate(ce)),
            TypeError::UnexpectedType(ref t) => format!("unexpected type: {}", debug_truncate(t)),

            TypeError::Inside(_)  => format!("error inside (the 'primary' subderivation)"),
            TypeError::Later(_)   => format!("error later (the 'secondary' subderivation)"),
            TypeError::Subder     => format!("error in a subderivation (not specific)"),
            
            TypeError::Mismatch   => format!("type mismatch"),
            TypeError::MismatchSort(ref g1, ref g2) => format!("sort mismatch: found {:?}, but expected {:?}", g1, g2),
            TypeError::EffectError(ref err) => format!("effect error: {:?}", err),
            TypeError::SubsumptionFailure(ref x, ref y) => format!("subsumption failure: {:?} =!= {:?}", x, y),
        };
        write!(f,"{}",s)
    }
}

fn wrap_later_error(err:&TypeError) -> TypeError {
    match err {
        &TypeError::Later(_) => err.clone(),
        err => TypeError::Later(Rc::new(err.clone())),
    }
}
fn wrap_inside_error(err:&TypeError) -> TypeError {
    match err {
        &TypeError::Inside(_) => err.clone(),
        err => TypeError::Inside(Rc::new(err.clone())),
    }
}

fn error_is_local(err:&TypeError) -> bool {
    match *err {
        TypeError::VarNotInScope(_) => true,
        TypeError::IdentNotInScope(_) => true,
        TypeError::NoParse(_) => true,
        TypeError::AnnoMism => true,
        TypeError::CheckFailArrow(_) => true,
        TypeError::NoSynthRule => true,
        TypeError::NoCheckRule => true,
        TypeError::InvalidPtr => true,
        TypeError::ProjNotProd => true,
        TypeError::ValNotArrow => true,
        TypeError::AppNotArrow => true,
        TypeError::ScopeNotNmTm => true,
        TypeError::GetNotRef => true,
        TypeError::ExpNotCons => true,
        TypeError::BadCheck => true,
        TypeError::DSLiteral => true,
        TypeError::EmptyDT => true,
        TypeError::Unimplemented => true,
        TypeError::ParamMism(_) => false,
        TypeError::ParamNoSynth(_) => false,
        TypeError::ParamNoCheck(_) => false,
        TypeError::CheckFailType(_) => false,
        TypeError::CheckFailCEffect(_) => false,
        TypeError::SynthFailVal(_) => false,
        TypeError::UnexpectedCEffect(_) => true,
        TypeError::UnexpectedType(_) => true,
        TypeError::Later(_) => false,
        TypeError::Inside(_) => false,
        TypeError::Subder     => false,
        TypeError::Mismatch   => true,
        TypeError::MismatchSort(_,_)  => true,
        TypeError::EffectError(_)  => true,
        TypeError::SubsumptionFailure(_,_)  => true,
    }
}

fn result_is_local_error<X>(x:&Result<X,TypeError>) -> bool {
    match *x {
        Ok(_) => false,
        Err(ref e) => error_is_local(e),
    }
}

fn failure<R:HasClas+debug::DerRule>
    (dir:Dir<R>, ext:&Ext,
     ctx:&Ctx, tm:R::Term, n:R, err:TypeError) -> Der<R>
{    
    if let Some(lbl) = ext.last_label.clone() {print!("After {}, ", lbl)}
    let is_local_err = error_is_local(&err);
    
    println!("Failed to {} {} {}, error: {}", dir.short(), R::term_desc(), n.short(), err);
    if is_local_err {
        println!("  Failure term: {}", debug_truncate(&tm));
    }
    Der{
        //ext: ext.clone(),
        ctx: ctx.clone(),
        term: Rc::new(tm),
        rule: Rc::new(n),
        dir: dir,
        clas: Err(err),
        vis:DerVis{
            tmfam:R::tm_fam(),
            local_err:is_local_err,
        }
    }
}

fn success<R:HasClas+debug::DerRule>
    (dir:Dir<R>, _ext:&Ext,
     ctx:&Ctx, tm:R::Term, rule:R, clas:R::Clas) -> Der<R>
{
    Der{
        //ext: ext.clone(),
        ctx: ctx.clone(),
        term: Rc::new(tm),
        rule: Rc::new(rule),
        dir: dir,
        clas: Ok(clas),
        vis:DerVis{
            tmfam:R::tm_fam(),
            local_err:false,
        }
    }
}

fn propagate<R:HasClas+debug::DerRule>
    (dir:Dir<R>, _ext:&Ext,
     ctx:&Ctx, tm:R::Term, rule:R, result:Result<R::Clas,TypeError>) -> Der<R>
{
    Der{
        //ext: ext.clone(),
        ctx: ctx.clone(),
        term: Rc::new(tm),
        rule: Rc::new(rule),
        dir: dir,
        clas: result,
        vis:DerVis{
            tmfam:R::tm_fam(),
            local_err:false,
        }
    }
}

//TODO: Return a Vec<_>; try each possible decomposition.
pub fn find_defs_for_idxtm_var(ctx:&Ctx, x:&Var) -> Option<IdxTm> {
    match ctx {
        &Ctx::Empty => None,
        &Ctx::PropTrue(_, Prop::Equiv(IdxTm::Var(ref x_), ref i,_)) if x == x_ => Some(i.clone()),
        &Ctx::PropTrue(_, Prop::Equiv(ref i, IdxTm::Var(ref x_),_)) if x == x_ => Some(i.clone()),
        &Ctx::PropTrue(_, Prop::Equiv(ref _i, ref _j, ref _g)) => {
            // This is the not the prop that we are looking for; but perhaps print it.
            //println!("PropTrue: {:?} == {:?} : {:?}", i, j, g);
            find_defs_for_idxtm_var(&*(ctx.rest().unwrap()), x)
        },
        _ => find_defs_for_idxtm_var(&*(ctx.rest().unwrap()), x)
    }
}


/// synthesize sort for index term
pub fn synth_idxtm(ext:&Ext, ctx:&Ctx, idxtm:&IdxTm) -> IdxTmDer {
    let fail = |r:IdxTmRule, err:TypeError| { failure(Dir::Synth, ext, ctx, idxtm.clone(), r, err)  };
    let succ = |r:IdxTmRule, sort:Sort    | { success(Dir::Synth, ext, ctx, idxtm.clone(), r, sort) };
    let fail_inside = |r:IdxTmRule, err:&TypeError| { fail(r, wrap_inside_error(err)) }
    ;
    match idxtm {
        &IdxTm::Ident(ref x) => {
            let rule = IdxTmRule::Var(x.clone());
            match ctx.lookup_idxtm_def(x) {
                None => fail(rule, TypeError::IdentNotInScope(x.clone())),
                Some(i) => synth_idxtm(ext, ctx, &i)
            }
        }
        &IdxTm::Var(ref x) => {
            let rule = IdxTmRule::Var(x.clone());
            match ctx.lookup_ivar(x) {
                None => fail(rule, TypeError::VarNotInScope(x.clone())),
                Some(sort) => succ(rule, sort)
            }   
        }
        &IdxTm::Sing(ref nt) => {
            let td0 = synth_nmtm(ext,ctx,nt);
            let ty0 = td0.clas.clone();
            let td = IdxTmRule::Sing(td0);
            match ty0 {
                Err(ref e) => fail_inside(td, e),
                Ok(ref t) if *t == Sort::Nm => succ(td, Sort::NmSet),
                Ok(_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Empty => {
            succ(IdxTmRule::Empty, Sort::NmSet)
        },
        &IdxTm::Apart(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(ext,ctx,idx0);
            let td1 = synth_idxtm(ext,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::Apart(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmSet),Ok(Sort::NmSet)) => succ(td, Sort::NmSet),
                (Ok(Sort::NmSet),_) => fail(td, TypeError::ParamMism(1)),
                (_,_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Union(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(ext,ctx,idx0);
            let td1 = synth_idxtm(ext,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::Union(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmSet),Ok(Sort::NmSet)) => succ(td, Sort::NmSet),
                (Ok(Sort::NmSet),_) => fail(td, TypeError::ParamMism(1)),
                (_,_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Bin(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(ext,ctx,idx0);
            let td1 = synth_idxtm(ext,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::Bin(td0,td1);
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
            let td0 = synth_idxtm(ext,ctx,idx0);
            let td1 = synth_idxtm(ext,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
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
            let td0 = synth_idxtm(ext,ctx,idx);
            let typ0 = td0.clas.clone();
            let td = IdxTmRule::Proj1(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Sort::Prod(t0,_)) => succ(td, (*t0).clone()),
                _ => fail(td, TypeError::ProjNotProd),
            }
        },
        &IdxTm::Proj2(ref idx) => {
            let td0 = synth_idxtm(ext,ctx,idx);
            let typ0 = td0.clas.clone();
            let td = IdxTmRule::Proj2(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Sort::Prod(_,t1)) => succ(td, (*t1).clone()),
                _ => fail(td, TypeError::ProjNotProd),
            }
        },
        &IdxTm::Lam(ref x, ref x_sort, ref idx) => {
            let ctx_ext = ctx.ivar(x.clone(), x_sort.clone());
            let td0 = synth_idxtm(ext,&ctx_ext,idx);
            let typ0 = td0.clas.clone();
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
        &IdxTm::WriteScope => {
            succ(IdxTmRule::WriteScope, Sort::IdxArrow(
                Rc::new(Sort::NmSet),
                Rc::new(Sort::NmSet)
            ))                        
        }
        &IdxTm::App(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(ext,ctx,idx0);
            let td1 = synth_idxtm(ext,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::App(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::IdxArrow(ref t0,ref t1)),Ok(ref t2)) if **t0 == *t2 => succ(td, (**t1).clone()),
                (Ok(Sort::IdxArrow(ref t0,_)),Ok(ref t2)) => {
                    // error reporting order: found sort, then expected sort
                    //println!("index app term: {:?} {:?}", idx0, idx1);
                    fail(td, TypeError::MismatchSort( (*t2).clone(), (**t0).clone() ))
                },                    
                _ => fail(td, TypeError::AppNotArrow),
            }
        },
        &IdxTm::Map(ref nt, ref idx) => {
            let td0 = synth_nmtm(ext,ctx,nt);
            let td1 = synth_idxtm(ext,ctx,idx);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::Map(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmArrow(n0,n1)),Ok(Sort::NmSet)) => {
                    if (*n0 == Sort::Nm) && (*n1 == Sort::Nm) { succ(td, Sort::NmSet) }
                    else { fail(td, TypeError::ParamMism(0)) }
                },
                (Ok(Sort::NmArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                _ => fail(td, TypeError::AppNotArrow),
            }
        },
        &IdxTm::MapStar(ref nt, ref idx) => {
            let td0 = synth_nmtm(ext,ctx,nt);
            let td1 = synth_idxtm(ext,ctx,idx);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::MapStar(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmArrow(n0,n1)),Ok(Sort::NmSet)) => {
                    if (*n0 == Sort::Nm) && (*n1 == Sort::Nm) { succ(td, Sort::NmSet) }
                    else { fail(td, TypeError::ParamMism(0)) }
                },
                (Ok(Sort::NmArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                _ => fail(td, TypeError::AppNotArrow),
            }
        },
        &IdxTm::FlatMap(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(ext,ctx,idx0);
            let td1 = synth_idxtm(ext,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::FlatMap(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::IdxArrow(n0,n1)),Ok(Sort::NmSet)) => {
                    if *n0 != Sort::Nm {
                        fail(td, TypeError::MismatchSort( (*n0).clone(), Sort::Nm ))
                    } else if *n1 != Sort::NmSet {
                        fail(td, TypeError::MismatchSort( (*n1).clone(), Sort::NmSet ))
                    }
                    else {
                        assert_eq!(*n0, Sort::Nm);
                        assert_eq!(*n1, Sort::NmSet);
                        succ(td, Sort::NmSet)
                    }
/*
                    if (*n0 == Sort::Nm) && (*n1 == Sort::NmSet) { succ(td, Sort::NmSet) }
                    else { fail(td, TypeError::ParamMism(0)) }
*/
                },
                (Ok(Sort::IdxArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                (Ok(_),_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::FlatMapStar(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(ext,ctx,idx0);
            let td1 = synth_idxtm(ext,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::FlatMapStar(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::IdxArrow(n0,n1)),Ok(Sort::NmSet)) => {
                    if (*n0 == Sort::Nm) && (*n1 == Sort::NmSet) { succ(td,Sort::NmSet) }
                    else { fail(td, TypeError::ParamMism(0)) }
                },
                (Ok(Sort::IdxArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                (Ok(_),_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::NmSet(ref _s) => {
            let rule = IdxTmRule::NmSet;
            succ(rule, Sort::NmSet)
        }
        &IdxTm::NoParse(ref s) => {
            fail(IdxTmRule::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },        
    }
}

/// check sort against index term
pub fn check_idxtm(ext:&Ext, ctx:&Ctx, idxtm:&IdxTm, sort:&Sort) -> IdxTmDer {
    // let fail = |td:IdxTmRule, err :TypeError| { failure(Dir::Check, ext, ctx, td, err)  };
    // let succ = |td:IdxTmRule, sort:Sort     | { success(Dir::Check, ext, ctx, td, sort) };
    match idxtm {
        // We're exclusively using synthesis for index terms at the moment
        tm => {
            let mut td = synth_idxtm(ext,ctx,tm);
            let ty = td.clas.clone();
            if let Ok(ty) = ty {
                if ty == *sort { td }
                else {
                    td.clas = Err(TypeError::AnnoMism);
                    td
                }
            } else { td }
        },
    }  
}

/// synthesize sort for name term
pub fn synth_nmtm(ext:&Ext, ctx:&Ctx, nmtm:&NameTm) -> NmTmDer {
    let fail = |td:NmTmRule, err :TypeError| { failure(Dir::Synth, ext, ctx, nmtm.clone(), td, err)  };
    let succ = |td:NmTmRule, sort:Sort     | { success(Dir::Synth, ext, ctx, nmtm.clone(), td, sort) };
    match nmtm {
        &NameTm::Ident(ref x) => {
            // expand the identifier
            let nmtm = expand::expand_nmtm(ctx, NameTm::Ident(x.clone()));
            synth_nmtm(ext, ctx, &nmtm)
        }
        &NameTm::ValVar(ref x) => {
            let td = NmTmRule::ValVar(x.clone());
            match ctx.lookup_var(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(typ) => match typ {
                    Type::Nm(_) => succ(td, Sort::Nm),
                    ty => fail(td, TypeError::UnexpectedType(ty.clone()))
                }
            }        
        },
        &NameTm::Var(ref x) => {
            let td = NmTmRule::Var(x.clone());
            match ctx.lookup_ivar(x) {
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
            let td0 = synth_nmtm(ext, ctx, nt0);
            let td1 = synth_nmtm(ext, ctx, nt1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
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
            let ctx_ext = ctx.ivar(x.clone(), s.clone());
            let td0 = synth_nmtm(ext,&ctx_ext,nt);
            let typ0 = td0.clas.clone();
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
        &NameTm::WriteScope => { succ(NmTmRule::WriteScope, Sort::NmArrow(
            Rc::new(Sort::Nm), Rc::new(Sort::Nm)
        ))}
        &NameTm::App(ref nt0, ref nt1) => {
            let td0 = synth_nmtm(ext,ctx,nt0);
            let td1 = synth_nmtm(ext,ctx,nt1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
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

/// check sort against name term
pub fn check_nmtm(ext:&Ext, ctx:&Ctx, nmtm:&NameTm, sort:&Sort) -> NmTmDer {
    // let fail = |td:IdxTmRule, err :TypeError| { failure(Dir::Check, ext, ctx, td, err)  };
    // let succ = |td:IdxTmRule, sort:Sort     | { success(Dir::Check, ext, ctx, td, sort) };
    match nmtm {
        // We're exclusively using synthesis for name terms at the moment
        tm => {
            let mut td = synth_nmtm(ext,ctx,tm);
            let ty = td.clas.clone();
            if let Ok(ty) = ty {
                if ty == *sort { td }
                else {
                    td.clas = Err(TypeError::AnnoMism);
                    td
                }
            } else { td }
        },
    }  
}

/// synthesize sort for value term
pub fn synth_val(ext:&Ext, ctx:&Ctx, val:&Val) -> ValDer {
    let fail = |td:ValRule, err :TypeError| { failure(Dir::Synth, ext, ctx, val.clone(), td, err)  };
    let succ = |td:ValRule, typ :Type     | { success(Dir::Synth, ext, ctx, val.clone(), td, typ) };
    match val {
        &Val::Var(ref x) => {
            let td = ValRule::Var(x.clone());
            match ctx.lookup_var(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(ty) => succ(td, ty)
            }
        },
        &Val::Unit => {
            succ(ValRule::Unit, Type::Unit)
        },
        &Val::Pair(ref v0, ref v1) => {
            let td0 = synth_val(ext, ctx, v0);
            let td1 = synth_val(ext, ctx, v1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
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
            let td0 = synth_val(ext, ctx, v);
            let td = ValRule::Inj1(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Val::Inj2(ref v) => {
            let td0 = synth_val(ext, ctx, v);
            let td = ValRule::Inj2(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Val::Roll(ref v) => {
            let td0 = synth_val(ext, ctx, v);
            let td = ValRule::Roll(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Val::Pack(ref i, ref v) => {
            let td0 = synth_idxtm(ext, ctx, i);
            let td1 = synth_val(ext, ctx, v);
            let td = ValRule::Pack(td0, td1);
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
            let td0 = synth_nmtm(ext, ctx, nmtm);
            let typ0 = td0.clas.clone();
            let td = ValRule::NameFn(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Sort::NmArrow(n0,n1)) => {
                    if (*n0 == Sort::Nm) && (*n1 == Sort::Nm) {
                        succ(td, Type::NmFn(nmtm.clone()))
                    } else { fail(td, TypeError::ParamMism(0)) }
                },
                _ => fail(td, TypeError::ValNotArrow),
            }
        },
        &Val::Anno(ref v,ref t) => {
            let td0 = check_val(ext, ctx, v, t);
            let typ0 = td0.clas.clone();
            let td = ValRule::Anno(td0, t.clone());
            match typ0 {
                Err(err) => fail(td, err.clone()),
                Ok(typ) => succ(td, typ.clone()),
            }
        },
        &Val::ThunkAnon(ref e) => {
            let td0 = synth_exp(ext, ctx, e);
            let typ0 = td0.clas.clone();
            let td = ValRule::ThunkAnon(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(ty) => succ(td, Type::Thk(IdxTm::Empty, Rc::new(ty))),
            }
        },
        &Val::Bool(b) => {
            succ(ValRule::Bool(b), type_bool())
        },
        &Val::Nat(n) => {
            succ(ValRule::Nat(n), type_nat())
        },
        &Val::Str(ref s) => {
            succ(ValRule::Str(s.clone()), type_string())
        },
        &Val::NoParse(ref s) => {
            fail(ValRule::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },
    }
}

/// check sort against value term
pub fn check_val(ext:&Ext, ctx:&Ctx, val:&Val, typ_raw:&Type) -> ValDer {
    let fail = |td:ValRule, err :TypeError| { failure(Dir::Check(typ_raw.clone()), ext, ctx, val.clone(), td, err)  };
    let succ = |td:ValRule, typ :Type     | { success(Dir::Check(typ_raw.clone()), ext, ctx, val.clone(), td, typ) };
    // Normalize the type
    let typ = &(normal::normal_type(ctx, typ_raw));
    match val {
        &Val::Var(ref x) => {
            let td = ValRule::Var(x.clone());
            match ctx.lookup_var(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(x_typ_raw) => {
                    let subset_flag = decide::subset::decide_type_subset_norm(
                            &decide::relctx_of_ctx(&ctx),
                            x_typ_raw.clone(), typ_raw.clone()
                    );                    
                    if subset_flag {
                        if false { // Super-verbose variable-typing messages:
                            println!("Checked type of variable {}:\n\
                                      \t{:?}\n\
                                      Against:\n\
                                      \t{:?}\n",
                                     x, x_typ_raw, typ_raw);
                        }
                        succ(td, x_typ_raw)
                    }
                    else {
                        println!("================================================================================== BEGIN");
                        println!("Detailed errors for checking type of variable {}:", x);
                        println!(".. Variable {}'s type:\n{:?} \n\n...does not check against type:\n{:?}\n", x, x_typ_raw, typ_raw);
                        println!("");
                        println!(".. type-subset holds: {}\n", subset_flag);
                        println!("");
                        println!(".. Variable {}'s type:\n{:?} \n\n...does not check against type:\n{:?}\n", x,
                                 normal::normal_type(ctx, &x_typ_raw), typ);
                        println!("---------------------------------------------------------------------------------- END ");
                        fail(td, TypeError::AnnoMism)
                    }
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
                let td0 = check_val(ext, ctx, v0, t0);
                let td1 = check_val(ext, ctx, v1, t1);
                let (typ0,typ1) = (td0.clas.clone(), td1.clas.clone());
                let td = ValRule::Pair(td0,td1);
                match (typ0,typ1) {
                    (Err(_),_) => fail(td, TypeError::ParamNoCheck(0)),
                    (_,Err(_)) => fail(td, TypeError::ParamNoCheck(1)),
                    (Ok(_),Ok(_)) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Pair(
                synth_val(ext, ctx, v0),
                synth_val(ext, ctx, v1),
            ), TypeError::AnnoMism) }
        },
        &Val::Inj1(ref v) => {
            if let Type::Sum(ref t1, _) = *typ {
                let td0 = check_val(ext, ctx, v, t1);
                let typ0 = td0.clas.clone();
                let td = ValRule::Inj1(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Ok(_) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Inj1(
                synth_val(ext,ctx, v)
            ), TypeError::AnnoMism) }
        },
        &Val::Inj2(ref v) => {
            if let Type::Sum(_, ref t2) = *typ {
                let td0 = check_val(ext, ctx, v, t2);
                let typ0 = td0.clas.clone();
                let td = ValRule::Inj2(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Ok(_) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Inj2(
                synth_val(ext,ctx, v)
            ), TypeError::AnnoMism) }
        },
        &Val::Roll(ref v) => {
            let vd = check_val(ext, ctx, v, typ);
            let vt = vd.clas.clone();
            propagate(Dir::Check(typ.clone()), ext,
                      ctx, val.clone(), ValRule::Roll(vd), vt)
        },
        &Val::Name(ref n) => {
            let td = ValRule::Name(n.clone());
            if let Type::Nm(ref _idx) = *typ {
                match n { 
                    &Name::NoParse(ref s) => fail(td, TypeError::NoParse(s.clone())),
                    // TODO-Next: check that n is a member of idx
                    _ => succ(td, typ.clone())
                }
            } else { fail(td, TypeError::AnnoMism) }
        },
        &Val::NameFn(ref nmtm) => {
            if let Type::NmFn(ref nt) = *typ {
                let td0 = check_nmtm(ext, ctx, nt, &Sort::NmArrow(
                    Rc::new(Sort::Nm), Rc::new(Sort::Nm),
                ));
                let typ0 = td0.clas.clone();
                let td = ValRule::NameFn(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    // TODO-Soon: check equivalence of nmtm and nt
                    Ok(_) => succ(td, typ.clone())
                }
            } else { fail(ValRule::NameFn(
                synth_nmtm(ext, ctx, nmtm)
            ), TypeError::AnnoMism) }
        },
        &Val::Anno(ref v,ref t) => {
            // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
            if *t == *typ {
                let td0 = check_val(ext, ctx, v, t);
                let typ0 = td0.clas.clone();
                let td = ValRule::Anno(td0, t.clone());
                match typ0 {
                    Err(err) => fail(td, err.clone()),
                    Ok(typ) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Anno(
                synth_val(ext, ctx, v), t.clone()
            ), TypeError::AnnoMism) }
        },
        //
        // Gamma |- i <= g
        // Gamma |= P[i/a] true
        // Gamma |- v <= A[i/a]
        // ---------------------------------------- :: existsi
        // Gamma |- pack(i,v) <= (exists a:g|P. A)
        //
        &Val::Pack(ref i, ref v) => {
            if let Type::Exists(a,g,p,aa) = typ.clone() {
                let td0  = check_idxtm(ext, ctx, i, &g);
                let pi   = subst::subst_term_prop(Term::IdxTm(i.clone()), &a, p);
                // TODO: check that pi = p[i/a] is true
                drop(pi);
                let aai  = subst::subst_term_type(Term::IdxTm(i.clone()), &a, (*aa).clone());
                let td1 = check_val(ext, ctx, v, &aai);
                let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
                let td = ValRule::Pack(td0, td1);
                match (typ0,typ1) {
                    (Err(_),_) => fail(td, TypeError::ParamNoCheck(0)),
                    (_,Err(_)) => fail(td, TypeError::ParamNoCheck(1)),
                    _ => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Pack(
                synth_idxtm(ext, ctx, i),
                synth_val(ext, ctx, v)
            ), TypeError::CheckFailType(typ.clone())) }
        },
        &Val::ThunkAnon(ref e) => {
            if let Type::Thk(ref _idx, ref ce) = *typ {
                let td0 = check_exp(ext, ctx, &*e, &*ce);
                let typ0 = td0.clas.clone();
                let td = ValRule::ThunkAnon(td0);
                // TODO-Next: use this once effects are implemented
                // if IdxTm::Empty != *idx {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ0 {
                    //Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Err(_) => fail(td, TypeError::CheckFailCEffect((**ce).clone())),
                    Ok(_) => succ(td, typ.clone())
                }
            } else { fail(ValRule::ThunkAnon(
                synth_exp(ext, ctx, e)
            ), TypeError::AnnoMism) }
        },
        &Val::Bool(b) => {
            let td = ValRule::Bool(b);
            if type_bool() == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::Nat(n) => {
            let td = ValRule::Nat(n);
            if type_nat() == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::Str(ref s) => {
            let td = ValRule::Str(s.clone());
            if type_string() == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::NoParse(ref s) => {
            fail(ValRule::NoParse(s.clone()), TypeError::NoParse(s.clone()))
        },
        // v => {
        //     let mut td = synth_val(ext,ctx,v);
        //     let ty = td.clas.clone();
        //     if let Ok(ty) = ty {
        //         if ty == *typ { td }
        //         else {
        //             td.clas = Err(TypeError::AnnoMism);
        //             td
        //         }
        //     } else { td }
        // },
    }
}

/// Synthesize typing derivations for a list of declarations (e.g., from a module)
pub fn synth_items(ext:&Ext, ctx:&Ctx, d:&Decls) -> (Vec<ItemRule>, Ctx) {
   
    let mut decls = d;
    let mut tds : Vec<ItemRule> = vec![];
    let mut doc : Option<String> = None;
    let mut ctx = ctx.clone();
    fn der_of(ctx:Ctx, rule:DeclRule,
              res:Result<DeclClas,TypeError>) -> DeclDer
    {
        let is_local_err = result_is_local_error(&res);
        Der{
            ctx:ctx,
            term:Rc::new(()),
            dir:Dir::Synth,
            rule:Rc::new(rule),
            clas:res,
            vis:DerVis{
                tmfam:"Module".to_string(),
                local_err:is_local_err,
            }
        }
    };
    loop {
        match decls {
            &Decls::End => break,
            &Decls::Doc(ref s, ref d) =>
            {
                doc   = Some(s.clone());
                decls = d;
            }            
            &Decls::NoParse(ref s) => {
                tds.push(ItemRule::NoParse(s.clone()));
                break;
            },
            &Decls::UseAll(ref m, ref d) => {
                let der = synth_module(ext, &m.module);
                ctx = ctx.append(&der.ctx_out);
                tds.push(ItemRule::UseAll(UseAllModuleDer{
                    ast:m.clone(),
                    der:der}
                ));
                doc = None;
                decls = d;
            }
            &Decls::NmTm(ref x, ref m, ref d) => {
                let der = synth_nmtm(ext, &ctx, m);
                let sort = der.clas.clone();
                let der = ItemDer{
                    doc:doc.clone(),
                    qual:Qual::NmTm,
                    var:x.clone(),
                    der:der_of(ctx.clone(),
                               DeclRule::NmTm(x.clone(), der),
                               sort.map(|s|DeclClas::Sort(s)))
                };
                doc = None;
                tds.push(ItemRule::Bind(der));
                ctx = ctx.def(x.clone(), Term::NmTm(m.clone()));
                decls = d;
            }
            &Decls::IdxTm(ref x, ref i, ref d) => {
                let der = synth_idxtm(ext, &ctx, i);
                let sort = der.clas.clone();
                let der = ItemDer{
                    doc:doc.clone(),
                    qual:Qual::IdxTm,
                    var:x.clone(),
                    der:der_of(ctx.clone(),
                               DeclRule::IdxTm(x.clone(), der),
                               sort.map(|s|DeclClas::Sort(s)))
                };
                doc = None;
                tds.push(ItemRule::Bind(der));
                ctx = ctx.def(x.clone(), Term::IdxTm(i.clone()));
                decls = d;
            }
            &Decls::Type(ref x, ref a, ref d) => {
                // TODO: synth kinding for type
                let der = ItemDer{
                    doc:doc.clone(),
                    qual:Qual::Type,
                    var:x.clone(),
                    der:der_of(ctx.clone(),
                               DeclRule::Type(x.clone(), a.clone()),
                               Ok(DeclClas::Kind(Kind::NoParse("TODO-XXX-bitype.rs".to_string()))))
                };
                doc = None;
                tds.push(ItemRule::Bind(der));
                ctx = ctx.def(x.clone(), Term::Type(a.clone()));
                decls = d;
            }
            &Decls::Val(ref x, ref oa, ref v, ref d) => {
                let der = match oa {
                    &None        => synth_val(ext, &ctx, v   ),
                    &Some(ref a) => check_val(ext, &ctx, v, a),
                };
                ctx = match der.clas.clone() {
                    Err(_) => match oa {
                        &None        => ctx,
                        &Some(ref a) => ctx.var(x.clone(), a.clone())
                    },
                    Ok(a) => ctx.var(x.clone(), a),
                };
                let der_typ = der.clas.clone();
                let der = ItemDer{
                    doc:doc.clone(),
                    qual:Qual::Val,
                    var:x.clone(),
                    der:der_of(ctx.clone(),
                               DeclRule::Val(x.clone(), der),
                               der_typ.map(|a| DeclClas::Type(a)))
                };
                doc = None;
                tds.push(ItemRule::Bind(der));
                decls = d;
            }
            &Decls::Fn(ref f, ref a, ref e, ref d) => {
                let v : Val = fgi_val![ thunk fix ^f. ^e.clone() ];
                let a2 = a.clone();
                let der = check_val(ext, &ctx, &v, a);
                let der_typ = der.clas.clone();
                let der = ItemDer{
                    doc:doc.clone(),
                    qual:Qual::Val,
                    var:f.clone(),
                    der:der_of(ctx.clone(),
                               DeclRule::Fn(f.clone(), der),
                               der_typ.map(|_| DeclClas::Type(a2)))
                };
                ctx = ctx.var(f.clone(), a.clone());
                tds.push(ItemRule::Bind(der));
                doc = None;
                decls = d;
            }
        }      
    };
    return (tds, ctx)
}

/// Synthesize a typing derivation for a module, given the module AST.
pub fn synth_module(ext:&Ext, m:&Rc<Module>) -> ModuleDer {
    let (item_tds, ctx) = synth_items(ext, &Ctx::Empty, &m.decls);
    ModuleDer{
        ast: m.clone(),
        tds: item_tds,
        ctx_out: ctx,
    } 
}

/// Synthesize a type and effect for a program expression
pub fn synth_exp(ext:&Ext, ctx:&Ctx, exp:&Exp) -> ExpDer {
    let fail = |r:ExpRule, err :TypeError| { failure(Dir::Synth, ext, ctx, exp.clone(), r, err) };
    let succ = |r:ExpRule, typ :CEffect  | { success(Dir::Synth, ext, ctx, exp.clone(), r, typ) };
    let prop = |r:ExpRule, res:Result<CEffect,TypeError> | {
        propagate(Dir::Synth, ext, ctx, exp.clone(), r, res)
    };
    match exp {
        &Exp::Decls(ref decls, ref exp) => {
            let (ds_der, ds_ctx) = synth_items(ext, ctx, &decls);
            let ctx = &ds_ctx;
            //println!("{:?}", ctx);
            let e_der = synth_exp(ext, &ctx, exp);
            let ce = e_der.clas.clone().map(|ce| ce.clone());
            prop(ExpRule::Decls(ds_der, e_der),
                 ce)
        }        
        &Exp::UseAll(ref m, ref exp) => {
            let m_der = synth_module(ext, &m.module);
            let ctx = ctx.append(&m_der.ctx_out);
            let e_der = synth_exp(ext, &ctx, exp);
            let ce = e_der.clas.clone().map(|ce| ce.clone());
            prop(ExpRule::UseAll(
                UseAllModuleDer{
                    ast:m.clone(),
                    der:m_der
                }, e_der),
                 ce)
        }
        &Exp::AnnoC(ref e, ref ctyp) => {
            // XXX/TODO: this is a hack, depending on what you expect it to mean.
            let noeffect = Effect::WR(IdxTm::Empty, IdxTm::Empty);
            let td0 = check_exp(ext, ctx, e, &CEffect::Cons(ctyp.clone(),noeffect));
            let typ0 = td0.clas.clone();
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
            let td0 = check_exp(ext, ctx, e, et);
            let typ0 = td0.clas.clone();
            let td = ExpRule::AnnoE(td0, et.clone());
            match typ0 {
                Ok(ty) => succ(td, ty),
                Err(_err) => {                    
                    fail(td, TypeError::CheckFailCEffect(et.clone()))
                }
            }
        },
        &Exp::Ref(ref v1,ref v2) => {
            let td0 = synth_val(ext, ctx, v1);
            let td1 = synth_val(ext, ctx, v2);
            let (tp0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = ExpRule::Ref(td0,td1);
            match (tp0,typ1) {
                (Err(ref e),_) => fail(td, wrap_inside_error(e)),
                (_,Err(ref e)) => fail(td, wrap_inside_error(e)),
                (Ok(Type::Nm(idx)),Ok(a)) => {
                    let idx = IdxTm::Map(Rc::new(ext.write_scope.clone()), Rc::new(idx));
                    let typ = Type::Ref(idx.clone(),Rc::new(a));
                    let eff = Effect::WR(idx, IdxTm::Empty);
                    succ(td, CEffect::Cons(CType::Lift(typ),eff))
                },
                _ => fail(td, TypeError::ParamMism(1)),
            }
        },
        &Exp::Thunk(ref v,ref e) => {
            let td0 = synth_val(ext, ctx, v);
            let td1 = synth_exp(ext, ctx, e);
            let (tp0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = ExpRule::Thunk(td0,td1);
            match (tp0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Type::Nm(idx)),Ok(ce)) => {
                    let idx = IdxTm::Map(Rc::new(ext.write_scope.clone()), Rc::new(idx));
                    let typ = Type::Thk(idx.clone(),Rc::new(ce));
                    let eff = Effect::WR(idx, IdxTm::Empty);
                    succ(td, CEffect::Cons(CType::Lift(typ),eff))
                },
                _ => fail(td, TypeError::ParamMism(1)),
            }
        },
        &Exp::Force(ref v) => {
            // Sequence an effect _before_ an existing ceffect; get the resulting CEffect
            let td0 = synth_val(ext, ctx, v);
            let typ0 = td0.clas.clone();
            let td = ExpRule::Force(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Type::Thk(ref idx, ref ce)) => {
                    // Substitute the write scope variables away:
                    //
                    // E0  = expand-identifier-definitions( E )
                    // E'  = [ (#x:NmSet.{@@} x) / '@!' ] E0
                    // E'' = [ M / '@@' ] E'
                    //
                    let ce = expand::expand_ceffect(&ctx, (**ce).clone());
                    let ce = subst::subst_term_ceffect(
                        Term::IdxTm( fgi_index!{#x:NmSet.[@@] x} ),
                        & subst::idxtm_writescope_var_str().to_string(),
                        ce
                    );
                    let ce = subst::subst_term_ceffect(
                        Term::NmTm( ext.write_scope.clone() ),
                        & subst::nmtm_writescope_var_str().to_string(),
                        ce
                    );
                    match decide::effect::decide_effect_ceffect_sequencing(
                        ctx, decide::effect::Role::Archivist,
                        Effect::WR(fgi_index![0], idx.clone()), ce)
                    {
                        Ok(ce) => succ(td, ce.clone()),
                        Err(efferr) => fail(td, TypeError::EffectError(efferr))
                    }
                }
                Ok(t) => fail(td, TypeError::UnexpectedType(t.clone())),
            }
        },
        &Exp::DefType(ref x,ref t, ref e) => {
            let ctx = &ctx.def(x.clone(), Term::Type(t.clone()));
            let td2 = synth_exp(ext, ctx, e);
            // TODO: user-type kinding??
            let typ2 = td2.clas.clone();
            let td = ExpRule::DefType(x.clone(), t.clone(), td2);
            match typ2 {
                Err(ref err) => fail(td, wrap_later_error(err)),
                Ok(ty) => succ(td, ty.clone()),
            }
        },
        &Exp::App(ref e, ref v) => {
            let td0 = synth_exp(ext, ctx, e);
            let typ0 = td0.clas.clone();
            match typ0 {
                Err(_) => {
                    let td1 = synth_val(ext, ctx, v);
                    let td = ExpRule::App(td0,td1);
                    fail(td, TypeError::SynthFailVal(v.clone()))
                },
                Ok(CEffect::Cons(CType::Arrow(ref ty,ref ce), ref _ef)) => {
                    let td1 = check_val(ext, ctx, v, ty);
                    let ty1 = td1.clas.clone();
                    let td = ExpRule::App(td0,td1);
                    match ty1 {
                        Err(_) => fail(td, TypeError::ParamMism(1)),
                        Ok(_) => {
                            // TODO-Next: compose effects
                            succ(td, (**ce).clone())
                        }
                    }
                },
                Ok(ce) => {
                    let td1 = synth_val(ext, ctx, v);
                    let td = ExpRule::App(td0,td1);
                    fail(td, TypeError::UnexpectedCEffect(ce.clone()))
                }
            }
        },
        &Exp::IdxApp(ref e, ref i) => {
            let ed = synth_exp(ext,ctx,e);
            let id = synth_idxtm(ext,ctx,i);
            //let edt = ed.clas.clone();
            match (ed.clas.clone(), id.clas.clone())  {
                (Ok(ec), Ok(_is)) => { match ec {
                    CEffect::ForallIdx(x, _g, p, ce) => {
                        let _p = subst::subst_term_prop(Term::IdxTm(i.clone()), &x, p);
                        let ce = subst::subst_term_ceffect(Term::IdxTm(i.clone()), &x, (*ce).clone());
                        // XXX/TODO need to prove (decide) that p is true
                        let td = ExpRule::IdxApp(ed,id);
                        succ(td, ce)
                    }
                    _ => {
                        fail(ExpRule::IdxApp(ed,id),
                             TypeError::Mismatch)
                    }                    
                }}
                (_, _) => {
                    fail(ExpRule::IdxApp(ed,id), TypeError::Subder)
                }
            }
        },
        &Exp::Get(ref v) => {
            let td0 = synth_val(ext, ctx, v);
            let typ0 = td0.clas.clone();
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
            let td0 = synth_val(ext, ctx, v);
            let typ0 = td0.clas.clone();
            let td = ExpRule::Ret(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(ty) => succ(td, CEffect::Cons(
                    CType::Lift(ty),
                    Effect::WR(IdxTm::Empty, IdxTm::Empty)
                )),
            }
        },
        /* Synth/Let
        
        Gamma        |- e1 ==> effect1 F A
        Gamma, x : A |- e2 ==> effect2 C
        Gamma       ||- (effect1 then effect2) = effect3
        --------------------------------------------------:: let
        Gamma |- let x = e1 in e2 => effect3 C
        
         */
        &Exp::Let(ref x, ref e1, ref e2) => {
            let td1 = synth_exp(ext, ctx, e1);
            match td1.clas.clone() {
                Err(_) => fail(ExpRule::Let(x.clone(),td1,
                    synth_exp(ext, ctx, e2)
                ), TypeError::ParamNoSynth(1)),
                Ok(CEffect::Cons(CType::Lift(ty1), eff1)) => {
                    let new_ctx = ctx.var(x.clone(), ty1);
                    let td2 = synth_exp(ext, &new_ctx, e2);
                    let typ2 = td2.clas.clone();
                    match typ2 {
                        Err(ref err) => {
                            let td = ExpRule::Let(x.clone(), td1, td2);
                            fail(td, wrap_later_error(err))
                        }
                        Ok(CEffect::Cons(ty2, eff2)) =>
                        {
                            match decide::effect::decide_effect_sequencing(
                                ctx,
                                /* TODO: Get role from ext structure */
                                decide::effect::Role::Archivist,
                                eff1.clone(), eff2.clone()
                            ) {
                                Ok(eff3) => {
                                    let td = ExpRule::Let(x.clone(), td1, td2);
                                    succ(td, CEffect::Cons(ty2, eff3))
                                }
                                Err(err) => {
                                    println!("{:?}", err);
                                    fail(ExpRule::Let(
                                        x.clone(), td1,
                                        synth_exp(ext, ctx, e2)
                                    ), TypeError::EffectError(err))
                                }
                            }
                        }
                        _ => {
                            let td = ExpRule::Let(x.clone(), td1, td2);
                            fail(td, TypeError::ParamMism(2))
                        }
                    }
                },
                _ => fail(ExpRule::Let(x.clone(),td1,
                    synth_exp(ext, ctx, e2)
                ), TypeError::ParamMism(1)),
            }
        },
        &Exp::PrimApp(PrimApp::NameBin(ref v0,ref v1)) => {
            let td0 = synth_val(ext, ctx, v0);
            let td1 = synth_val(ext, ctx, v1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = ExpRule::PrimApp(PrimAppRule::NameBin(td0,td1));
            match (typ0,typ1) {
                (Err(_),_) => fail(td,TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td,TypeError::ParamNoSynth(1)),
                (Ok(Type::Nm(n1)),Ok(Type::Nm(n2))) => {
                    succ(td, CEffect::Cons(
                        CType::Lift(Type::Nm(
                            IdxTm::Bin(Rc::new(n1),Rc::new(n2))
                        )),
                        Effect::WR(IdxTm::Empty, IdxTm::Empty))
                    )
                },
                (Ok(Type::Nm(_)),_) => fail(td,TypeError::ParamMism(1)),
                _ => fail(td, TypeError::ParamMism(0))
            }
        },
        &Exp::PrimApp(PrimApp::RefThunk(ref v)) => {
            let td0 = synth_val(ext, ctx, v);
            let typ0 = td0.clas.clone();
            let td = ExpRule::PrimApp(PrimAppRule::RefThunk(td0));
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Type::Thk(idx,ce)) => {
                    match *ce {
                        CEffect::Cons(CType::Lift(ref typ),ref eff) => {
                            /*
                            // Substitute the write scope variables away:
                            //
                            // E0  = expand-identifier-definitions( E )
                            // E'  = [ (#x:NmSet.{@@} x) / '@!' ] E0
                            // E'' = [ M / '@@' ] E'
                            //
                            let eff = expand::expand_effect(&ctx, (*eff).clone());
                            let eff = subst::subst_term_effect(
                                Term::IdxTm( fgi_index!{#x:NmSet.[@@] x} ),
                                & subst::idxtm_writescope_var_str().to_string(),
                                eff
                            );
                            let eff = subst::subst_term_effect(
                                Term::NmTm( ext.write_scope.clone() ),
                                & subst::nmtm_writescope_var_str().to_string(),
                                eff
                            );
                             */
                            match decide::effect::decide_effect_sequencing(
                                ctx, decide::effect::Role::Archivist,
                                Effect::WR(fgi_index![0], idx.clone()), eff.clone())
                            {
                                Err(efferr) => fail(td, TypeError::EffectError(efferr)),
                                Ok(eff3) => succ(td, CEffect::Cons(CType::Lift(
                                    Type::Prod(
                                        Rc::new(Type::Ref(idx,Rc::new(typ.clone()))),
                                        Rc::new(typ.clone())
                                    )
                                ), eff3.clone()))
                            }
                        },
                        _ => fail(td, TypeError::ParamMism(0)),
                    }
                },
                _ => fail(td, TypeError::ParamMism(0)),
            }
        },        
        &Exp::PrimApp(PrimApp::NatLt(ref v0,ref v1)) => {
            let td0 = synth_val(ext, ctx, v0);
            let td1 = synth_val(ext, ctx, v1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = ExpRule::PrimApp(PrimAppRule::NatLt(td0,td1));
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Type::Ident(ref n0)), Ok(Type::Ident(ref n1)))
                if (n0 == "Nat") && (n1 == "Nat") => {
                    let ce = CEffect::Cons(
                        CType::Lift(Type::Ident("Bool".to_string())),
                        Effect::WR(IdxTm::Empty, IdxTm::Empty),
                    );
                    succ(td, ce)
                },
                (Ok(Type::Ident(ref n0)),_) if n0 == "Nat" => {
                    fail(td, TypeError::ParamMism(1))
                },
                _ => fail(td, TypeError::ParamMism(0))
            }
        },
        &Exp::Unimp => {
            let td = ExpRule::Unimp;
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::DebugLabel(ref n, ref s,ref e) => {
            let td2 = match s {
                &None => synth_exp(ext, ctx, e),                
                &Some(ref lbl) => {
                    let mut ext = ext.clone();
                    ext.last_label = Some(Rc::new(lbl.to_string()));
                    synth_exp(&ext, ctx, e)
                }
            };
            let typ2 = td2.clas.clone();
            let td = ExpRule::DebugLabel(n.clone(),s.clone(),td2);
            match typ2 {
                Err(ref err) => fail(td, wrap_later_error(err)),
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

        &Exp::WriteScope(ref v,ref e) => {
            let td0 = synth_val(ext, ctx, v);
            match td0.clas.clone() {
                Ok(Type::NmFn(nmlamb)) => {
                    let new_scope = fgi_nametm![
                        #_a:Nm.[^ext.write_scope.clone()][[^nmlamb] _a]
                    ];
                    let new_ext = Ext{write_scope:new_scope, ..ext.clone()};
                    let td1 = synth_exp(&new_ext, ctx, e);
                    let typ1 = td1.clas.clone();
                    let td = ExpRule::WriteScope(td0,td1);
                    match typ1 {
                        Ok(ref ceffect) => succ(td, ceffect.clone()),
                        Err(_) => fail(td, TypeError::ParamNoCheck(1)),
                    }
                }
                _ => fail(
                    ExpRule::WriteScope(td0, synth_exp(ext,ctx,e)),
                    TypeError::ScopeNotNmTm
                ),
            }
        },

        &Exp::Split(ref v, ref x1, ref x2, ref e) => {
            let td0 = synth_val(ext, ctx, v);
            let v_ty = td0.clone().clas.map(|a| normal::normal_type(ctx, &a));
            match v_ty.clone() {
                Err(_) => fail(ExpRule::Split(
                    td0, x1.clone(), x2.clone(),
                    synth_exp(ext, ctx, e)
                ), TypeError::ParamNoSynth(0)),
                Ok(Type::Prod(t1,t2)) => {
                    let new_ctx = ctx
                        .var(x1.clone(),(*t1).clone())
                        .var(x2.clone(),(*t2).clone())
                    ;
                    let td3 = synth_exp(ext, &new_ctx, e);
                    let typ3 = td3.clas.clone();
                    let td = ExpRule::Split(td0, x1.clone(), x2.clone(), td3);
                    match typ3 {
                        Err(ref err) => fail(td, wrap_later_error(err)),
                        Ok(ref ceffect) => succ(td, ceffect.clone())
                    }
                },
                _ => fail(ExpRule::Split(
                    td0, x1.clone(), x2.clone(),
                    synth_exp(ext, ctx, e)
                ), TypeError::ParamMism(0)),
            }
        },
        
        //
        // -------- More cases TODO: low priority:
        //
        
        &Exp::NameFnApp(ref v0,ref v1) => {
            let td0 = synth_val(ext, ctx, v0);
            let td1 = synth_val(ext, ctx, v1);
            let td = ExpRule::NameFnApp(td0,td1);
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatEq(ref v0,ref v1)) => {
            let td0 = synth_val(ext, ctx, v0);
            let td1 = synth_val(ext, ctx, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatEq(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatLte(ref v0,ref v1)) => {
            let td0 = synth_val(ext, ctx, v0);
            let td1 = synth_val(ext, ctx, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatLte(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatPlus(ref v0,ref v1)) => {
            let td0 = synth_val(ext, ctx, v0);
            let td1 = synth_val(ext, ctx, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatPlus(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        //
        // -------- More cases TODO: lowest priority:
        //

        &Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2) => {
            let td0 = synth_val(ext, ctx, v);
            let td2 = synth_exp(ext, ctx, e1);
            let td4 = synth_exp(ext, ctx, e2);
            let td = ExpRule::Case(td0,x1.clone(),td2,x2.clone(),td4);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },
        &Exp::IfThenElse(ref v, ref e1, ref e2) => {
            let td0 = synth_val(ext, ctx, v);
            let td1 = synth_exp(ext, ctx, e1);
            let td2 = synth_exp(ext, ctx, e2);
            let td = ExpRule::IfThenElse(td0,td1,td2);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },

        // ==  
        // == -- No synth rules for these forms
        // ==
        &Exp::Fix(ref x,ref e) => {
            let td1 = synth_exp(ext, ctx, e);
            let td = ExpRule::Fix(x.clone(), td1);
            fail(td, TypeError::NoSynthRule) // Ok
        },
        &Exp::Lam(ref x, ref e) => {
            let td1 = synth_exp(ext, ctx, e);
            let td = ExpRule::Lam(x.clone(), td1);
            fail(td, TypeError::NoSynthRule) // Ok
        },        
        &Exp::Unroll(ref v,ref x,ref e) => {
            let td0 = synth_val(ext, ctx, v);
            let td2 = synth_exp(ext, ctx, e);
            let td = ExpRule::Unroll(td0, x.clone(), td2);
            fail(td, TypeError::NoSynthRule) // Ok
        },
        &Exp::Unpack(ref i, ref x, ref v, ref e) => {
            let td2 = synth_val(ext, ctx, v);
            let td3 = synth_exp(ext, ctx, e);
            let td = ExpRule::Unpack(i.clone(),x.clone(),td2,td3);
            fail(td, TypeError::NoSynthRule)
        }
    }
}

/// Check a type and effect against a program expression
pub fn check_exp(ext:&Ext, ctx:&Ctx, exp:&Exp, ceffect:&CEffect) -> ExpDer {
    let fail = |td:ExpRule, err :TypeError| { failure(Dir::Check(ceffect.clone()), ext, ctx, exp.clone(), td, err) };
    let succ = |td:ExpRule, typ :CEffect  | { success(Dir::Check(ceffect.clone()), ext, ctx, exp.clone(), td, typ) };
    match exp {
        &Exp::Fix(ref x,ref e) => {            
            let new_ctx = ctx.var(x.clone(), Type::Thk(IdxTm::Empty, Rc::new(ceffect.clone())));
            let td = check_exp(ext, &new_ctx, e, ceffect);
            let td_typ = td.clas.clone();
            match td_typ {
                Err(_) => fail(ExpRule::Fix(x.clone(),td), TypeError::CheckFailCEffect(ceffect.clone())),
                Ok(_)  => succ(ExpRule::Fix(x.clone(),td), ceffect.clone())
            }
        },
        &Exp::Lam(ref x, ref e) => {
            // Strip off "forall" quantifiers in the ceffect type, moving their assumptions into the context.
            fn strip_foralls (ctx:&Ctx, ceffect:&CEffect) -> (Ctx, CEffect) {
                match ceffect {
                    &CEffect::ForallType(ref a, ref k, ref ceffect) => {
                        let ctx = ctx.tvar(a.clone(), k.clone());
                        strip_foralls(&ctx, ceffect)
                    },
                    &CEffect::ForallIdx(ref a, ref g, ref p, ref ceffect) => {
                        let ctx = ctx.ivar(a.clone(),g.clone());
                        let ctx = ctx.prop(p.clone());
                        strip_foralls(&ctx, ceffect)
                    },
                    &CEffect::Cons(_, _) => { (ctx.clone(), ceffect.clone()) }
                    &CEffect::NoParse(_) => { (ctx.clone(), ceffect.clone()) }
                }
            }
            let (ctx, ceffect) = strip_foralls(ctx, ceffect);            
            if let CEffect::Cons(CType::Arrow(ref at,ref et),ref _ef) = ceffect {
                let new_ctx = ctx.var(x.clone(),at.clone());
                let td1 = check_exp(ext, &new_ctx, e, et);
                let typ1 = td1.clas.clone();
                let td = ExpRule::Lam(x.clone(), td1);
                // TODO: use this once effects are properly implemented
                // if *ef != Effect::WR(IdxTm::Empty,IdxTm::Empty) {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ1 {
                    Err(_) => fail(td, TypeError::CheckFailCEffect(ceffect.clone())),
                    Ok(_) => succ(td, ceffect.clone()),
                }
            } else { fail(ExpRule::Lam(
                x.clone(), synth_exp(ext, &ctx, e)
            ), TypeError::CheckFailArrow(ceffect.clone())) }
        },
        &Exp::Unroll(ref v,ref x,ref e) => {
            let v_td = synth_val(ext, ctx, v);
            match v_td.clas.clone() {
                Err(_) => {
                    let td0 = check_exp(ext, ctx, e, ceffect);
                    fail(ExpRule::Unroll(v_td, x.clone(), td0),
                         TypeError::SynthFailVal(v.clone()))
                }
                Ok(v_ty) => {
                    let v_ty = normal::normal_type(ctx, &v_ty);
                    let v_ty = normal::unroll_type(&v_ty);
                    let new_ctx = ctx.var(x.clone(), v_ty);
                    let td0 = check_exp(ext, &new_ctx, e, ceffect);
                    let td0_typ = td0.clas.clone();
                    let td = ExpRule::Unroll(v_td, x.clone(), td0);
                    match td0_typ {
                        Err(_) => fail(td, TypeError::CheckFailCEffect(ceffect.clone())),
                        Ok(_)  => succ(td, ceffect.clone())
                    }
                }
            }
        },
        //
        // Gamma |- v => (exists a:g|P. A)
        // Gamma, b:g, [b/a]P true, x:[b/a]A |- e <= E
        // -------------------------------------------- :: unpack2
        // Gamma |- unpack(v,x.b.e) <= E                                   
        //
        &Exp::Unpack(ref a1, ref x, ref v, ref e) => {
            let v_td = synth_val(ext, ctx, v);
            let v_ty = v_td.clone().clas.map(|a| normal::normal_type(ctx, &a));
            match v_ty.clone() {
                Ok(Type::Exists(ref a2, ref g, ref p, ref aa)) => {
                    let p  = subst::subst_term_prop(Term::IdxTm(IdxTm::Var(a1.clone())), a2, p.clone());
                    let aa = subst::subst_term_type(Term::IdxTm(IdxTm::Var(a1.clone())), a2, (**aa).clone());
                    let new_ctx = ctx
                        .ivar(a1.clone(),(**g).clone())
                        .prop(p.clone())
                        .var(x.clone(),aa)
                        ;
                    let td3 = check_exp(ext, &new_ctx, e, &ceffect);
                    let typ3 = td3.clas.clone();
                    let rule = ExpRule::Unpack(a1.clone(),x.clone(),v_td,td3);
                    match typ3 {
                        Err(ref err) => fail(rule, wrap_later_error(err)),
                        Ok(_) => succ(rule, ceffect.clone())
                    }
                },
                rt => {
                    let td3 = synth_exp(ext, ctx, e);
                    let td = ExpRule::Unpack(a1.clone(),x.clone(),v_td,td3);
                    if let Err(_) = rt { fail(td, TypeError::ParamNoSynth(2)) }
                    else { fail(td, TypeError::ParamMism(2)) }
                }
            }
        },
        &Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2) => {
            let v_td = synth_val(ext, ctx, v);
            let v_ty = v_td.clone().clas.map(|a| normal::normal_type(ctx, &a));
            match v_ty {
                Ok(Type::Sum(ty1, ty2)) => {
                    let new_ctx1 = ctx.var(x1.clone(), (*ty1).clone());
                    let new_ctx2 = ctx.var(x2.clone(), (*ty2).clone());
                    let td1 = check_exp(ext, &new_ctx1, e1, ceffect);
                    let td1_typ = td1.clas.clone();
                    let td2 = check_exp(ext, &new_ctx2, e2, ceffect);
                    let td2_typ = td2.clas.clone();
                    let td = ExpRule::Case(v_td, x1.clone(), td1, x2.clone(), td2);
                    match (td1_typ, td2_typ) {
                        (Ok(_),Ok(_)) => succ(td, ceffect.clone()),
                        (_    ,_    ) => fail(td, TypeError::CheckFailCEffect(ceffect.clone())),
                    }
                }
                Ok(t) => {
                    let td1 = check_exp(ext, ctx, e1, ceffect);
                    let td2 = check_exp(ext, ctx, e2, ceffect);
                    fail(ExpRule::Case(v_td, x1.clone(), td1, x2.clone(), td2),
                         TypeError::UnexpectedType(t))
                }
                _ => {
                    let td1 = check_exp(ext, ctx, e1, ceffect);
                    let td2 = check_exp(ext, ctx, e2, ceffect);
                    fail(ExpRule::Case(v_td, x1.clone(), td1, x2.clone(), td2),
                         TypeError::SynthFailVal(v.clone()))
                }
            }
        },
        /* Check/Let
        
        Gamma        |- e1 ==> effect1 F A
        Gamma, x : A |- e2 <== effect2 C
        Gamma       ||- (effect1 then effect2) = effect3
        --------------------------------------------------:: let
        Gamma |- let x = e1 in e2 <== effect3 C
        
         */
        &Exp::Let(ref x, ref e1, ref e2) => {
            if let CEffect::Cons(ref ctyp, ref eff3) = *ceffect {
                let td1 = synth_exp(ext, ctx, e1);
                let typ1 = td1.clas.clone();
                match typ1 {
                    Err(ref err) => {
                        fail(ExpRule::Let(
                        x.clone(), td1,
                        synth_exp(ext, ctx, e2)
                    ), err.clone()) },
                    Ok(CEffect::Cons(CType::Lift(ref ct1), ref eff1)) => {
                        match decide::effect::decide_effect_subtraction(
                            ctx,
                            /* TODO: Get role from ext structure */
                            decide::effect::Role::Archivist,
                            eff3.clone(), eff1.clone())
                        {
                            Ok(eff2) => {
                                let new_ctx = ctx.var(x.clone(),ct1.clone());
                                let typ2 = CEffect::Cons(ctyp.clone(), eff2);
                                let td2 = check_exp(ext, &new_ctx, e2, &typ2);
                                let typ2res = td2.clas.clone();
                                let td = ExpRule::Let(x.clone(), td1,td2);
                                match typ2res {
                                    Err(ref err) => fail(td, wrap_later_error(err)),
                                    Ok(_) => succ(td, ceffect.clone()),
                                }
                            }
                            Err(err) => {
                                fail(ExpRule::Let(
                                    x.clone(), td1,
                                    synth_exp(ext,ctx,e2)
                                ), TypeError::EffectError(err))
                            }
                        }
                    }
                    _ => fail(ExpRule::Let(
                        x.clone(), td1,
                        synth_exp(ext,ctx,e2)
                    ), TypeError::ParamMism(1))
                }
            } else { fail(ExpRule::Let(x.clone(),
                synth_exp(ext, ctx, e1),
                synth_exp(ext, ctx, e1),
            ), TypeError::AnnoMism) }
        },
        &Exp::Ret(ref v) => {
            if let CEffect::Cons(CType::Lift(ref t),ref _ef) = *ceffect {
                let td0 = check_val(ext, ctx, v, t);
                let typ0 = td0.clas.clone();
                let td = ExpRule::Ret(td0);
                // TODO: use this once effects are properly implemented
                // if *ef != Effect::WR(IdxTm::Empty,IdxTm::Empty) {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ0 {
                    Err(_) => fail(td, TypeError::CheckFailType(t.clone())),
                    Ok(_) => succ(td, ceffect.clone())
                }
            } else { fail(ExpRule::Ret(
                synth_val(ext,ctx,v)
            ), TypeError::AnnoMism) }
        },
        &Exp::Split(ref v, ref x1, ref x2, ref e) => {
            let td0 = synth_val(ext, ctx, v);
            let v_ty = td0.clone().clas.map(|a| normal::normal_type(ctx, &a));
            match v_ty.clone() {
                Err(_) => fail(ExpRule::Split(
                    td0, x1.clone(), x2.clone(),
                    synth_exp(ext, ctx, e)
                ), TypeError::ParamNoSynth(0)),
                Ok(Type::Prod(t1,t2)) => {
                    let new_ctx = ctx
                        .var(x1.clone(),(*t1).clone())
                        .var(x2.clone(),(*t2).clone())
                    ;
                    let td3 = check_exp(ext, &new_ctx, e, ceffect);
                    let typ3 = td3.clas.clone();
                    let td = ExpRule::Split(td0, x1.clone(), x2.clone(), td3);
                    match typ3 {
                        Err(ref err) => fail(td, wrap_later_error(err)),
                        Ok(_) => succ(td, ceffect.clone())
                    }
                },
                _ => fail(ExpRule::Split(
                    td0, x1.clone(), x2.clone(),
                    synth_exp(ext, ctx, e)
                ), TypeError::ParamMism(0)),
            }
        },
        &Exp::IfThenElse(ref v, ref e1, ref e2) => {
            let td0 = synth_val(ext, ctx, v);
            let td1 = check_exp(ext, ctx, e1, ceffect);
            let td2 = check_exp(ext, ctx, e2, ceffect);
            let v_ty = td0.clas.clone().map(|a| normal::normal_type(ctx, &a));
            let (_t0,t1,t2) = (td0.clas.clone(),td1.clas.clone(),td2.clas.clone());
            let td = ExpRule::IfThenElse(td0,td1,td2);
            match (v_ty,t1,t2) {
                (Err(_),_,_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_),_) => fail(td, TypeError::ParamNoCheck(1)),
                (_,_,Err(_)) => fail(td, TypeError::ParamNoCheck(2)),
                (Ok(Type::Ident(ref b)),_,_) if b == "Bool" => {
                    // the exps are correct, because of the check above
                    succ(td, ceffect.clone())
                },
                _ => fail(td, TypeError::ParamMism(0)),
            }
        },
        &Exp::Thunk(ref v,ref e) => {
            if let &CEffect::Cons(
                CType::Lift(Type::Thk(ref idx,ref ce)),
                Effect::WR(ref _w,ref _r)
            ) = ceffect {
                // TODO/XXX --- check effects: that write set _w contains idx
                //
                let td0 = check_val(ext,ctx,v,&Type::Nm(idx.clone()));
                let td1 = check_exp(ext,ctx,e,&**ce);
                let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
                let td = ExpRule::Thunk(td0,td1);
                match (typ0,typ1) {
                    (Err(_),_) => fail(td, TypeError::ParamNoCheck(0)),
                    (_,Err(_)) => fail(td, TypeError::ParamNoCheck(1)),
                    (Ok(_),Ok(_)) => succ(td, ceffect.clone()),
                }
            } else { fail(ExpRule::Thunk(
                synth_val(ext, ctx, v),
                synth_exp(ext, ctx, e),
            ),TypeError::AnnoMism)}
        },
        &Exp::Ref(ref v1,ref v2) => {
            if let &CEffect::Cons(
                CType::Lift(Type::Ref(ref rf_idx,ref a)),
                Effect::WR(ref _w, ref _r)
            ) = ceffect {
                let td0 = synth_val(ext, ctx, v1);
                let td0ty = td0.clas.clone();
                let td1 = check_val(ext, ctx, v2, a);
                let td = ExpRule::Ref(td0, td1);
                match td0ty {
                    Ok(Type::Nm(ref _v1_idx)) => {
                        // TODO/XXX --- check effects: that write set _w contains rf_idx
                        // TODO/XXX -- check that v1_idx in the current write scope matches rf_idx
                        succ(td, ceffect.clone())
                    },
                    Ok(_) => fail(td, TypeError::Mismatch),
                    Err(ref err) => fail(td, TypeError::Inside(Rc::new(err.clone())))
                }
            } else { fail(ExpRule::Ref(
                synth_val(ext, ctx, v1),
                synth_val(ext, ctx, v2),
            ),TypeError::AnnoMism)}
        },
        &Exp::WriteScope(ref v,ref e) => {
            if let CEffect::Cons(_,_) = *ceffect {
                let td0 = synth_val(ext,ctx,v);
                match td0.clas.clone() {
                    Ok(Type::NmFn(nmlamb)) => {
                        let new_scope = fgi_nametm![
                            #n:Nm.[^ext.write_scope.clone()][[^nmlamb] n]
                        ];
                        let new_ext = Ext{write_scope:new_scope, ..ext.clone()};
                        let td1 = check_exp(&new_ext,ctx,e,ceffect);
                        let typ1 = td1.clas.clone();
                        let td = ExpRule::WriteScope(td0,td1);
                        match typ1 {
                            Ok(_) => succ(td, ceffect.clone()),
                            Err(_) => fail(td, TypeError::ParamNoCheck(1)),
                        }
                    }
                    _ => fail(
                        ExpRule::WriteScope(td0, synth_exp(ext,ctx,e)),
                        TypeError::ScopeNotNmTm
                    ),
                }
            } else { fail(ExpRule::WriteScope(
                synth_val(ext, ctx, v),
                synth_exp(ext, ctx, e),
            ), TypeError::AnnoMism)}
        },        
        //
        // Later and/or use synth rule:
        //   &Exp::App(ref e, ref v) => {},
        //   &Exp::IdxApp(ref e, ref i) => {},
        //   &Exp::Force(ref v) => {},
        //   &Exp::Get(ref v) => {},
        //   &Exp::DefType(ref x,Type,ref e) => {},
        //   &Exp::AnnoC(ref e,ref ct) => {},
        //   &Exp::AnnoE(ref e,ref et) => {},      
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
                &None => check_exp(ext, ctx, e, ceffect),
                &Some(ref lbl) => {
                    let mut ext = ext.clone();
                    ext.last_label = Some(Rc::new(lbl.to_string()));
                    check_exp(&ext, ctx, e, ceffect)
                }
            }            
        },
        &Exp::NoParse(ref s) => {
            fail(ExpRule::NoParse(s.clone()), TypeError::NoParse(s.clone()))
        },
        e => {
            let mut td = synth_exp(ext,ctx,e);
            let ty = td.clas.clone();
            if let Ok(ty) = ty {
                // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
                let rctx = decide::relctx_of_ctx(ctx);
                if decide::subset::decide_ceffect_subset(&rctx, ty.clone(), ceffect.clone()) {
                    td
                }
                else {
                    use bitype::debug::*;
                    println!("================================================================================== BEGIN");
                    println!("Detailed errors for checking an `Exp::{}` via subsumption:", td.rule.short());
                    println!(".. {}'s type:\n{:?} \n\n...does not check against type:\n{:?}\n", td.rule.short(), ty, ceffect);
                    println!("");
                    if false {
                        // may be very verbose
                        println!(".. {}'s type:\n{:?} \n\n...does not check against type:\n{:?}\n", td.rule.short(),
                                 normal::normal_ceffect(ctx, ty.clone()),
                                 normal::normal_ceffect(ctx, ceffect.clone()),
                        );
                    }
                    println!("---------------------------------------------------------------------------------- END ");
                    td.clas = Err(TypeError::SubsumptionFailure(ty, ceffect.clone()));
                    td
                }
            } else { td }
        },
    }
}



/// Stringification for debugging derivation rules
pub mod debug {
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
                NmTmRule::ValVar(_) => "ValVar",
                NmTmRule::Name(_) => "Name",
                NmTmRule::Bin(_, _) => "Bin",
                NmTmRule::Lam(_,_,_) => "Lam",
                NmTmRule::WriteScope => "WriteScope",
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
                IdxTmRule::Apart(_, _) => "Apart",
                IdxTmRule::Union(_, _) => "Union",
                IdxTmRule::Bin(_, _) => "Bin",
                IdxTmRule::Unit => "Unit",
                IdxTmRule::Pair(_, _) => "Pair",
                IdxTmRule::Proj1(_) => "Proj1",
                IdxTmRule::Proj2(_) => "Proj2",
                IdxTmRule::Lam(_, _, _) => "Lam",
                IdxTmRule::WriteScope => "WriteScope",
                IdxTmRule::App(_, _) => "App",
                IdxTmRule::Map(_, _) => "Map",
                IdxTmRule::MapStar(_, _) => "MapStar",
                IdxTmRule::FlatMap(_, _) => "FlatMap",
                IdxTmRule::FlatMapStar(_, _) => "FlatMapStar",
                IdxTmRule::NoParse(_) => "NoParse",
                IdxTmRule::NmSet => "NmSet",
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
                ExpRule::UseAll(_,_) => "UseAll",
                ExpRule::Decls(_,_) => "Decls",
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
                ExpRule::IdxApp(_, _) => "IdxApp",
                ExpRule::Split(_, _, _, _) => "Split",
                ExpRule::Case(_, _, _, _, _) => "Case",
                ExpRule::IfThenElse(_, _, _) => "IfThenElse",
                ExpRule::Ref(_,_) => "Ref",
                ExpRule::Get(_) => "Get",
                ExpRule::WriteScope(_,_) => "WriteScope",
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
    impl DerRule for DeclRule {
        fn term_desc() -> &'static str { "primitive expression" }
        fn short(&self) -> &str {
            match *self {
                _ => "TODO"
            }
        }
    }
}
//use self::debug::*;
