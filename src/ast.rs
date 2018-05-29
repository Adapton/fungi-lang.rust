//! Syntax: abstract (via Rust datatypes) and concrete (via Rust macros).
//!
//! **Program terms**:  
//!  - Declarations (`d`):        [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_decls.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Decls.html).   
//!  - Expressions (`e`):         [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_exp.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Exp.html).   
//!  - Values (`v`):              [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_val.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Val.html).  
//!
//! **Types and effects**:  
//!  - Value types (`A,B`):       [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_vtype.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Type.html).  
//!  - Computation types (`C,D`): [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_ctype.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.CType.html).  
//!  - Effect types (`E`):        [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_ceffect.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.CEffect.html).  
//!  - Effects (`ε`):             [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_effect.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Effect.html).  
//!  - Propositions (`P`):        [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_prop.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Prop.html).  
//!  - Kinds (`K`):               [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_kind.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Kind.html).  
//!
//! **Index terms, name terms, sorts**:  
//!  - Name literals (`n`):       [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_name.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Name.html).  
//!  - Name terms (`N,M`):        [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_nametm.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.NameTm.html).  
//!  - Index terms (`i,j,X,Y,Z`): [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_index.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.IdxTm.html).  
//!  - Sorts (`g`):               [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_sort.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Sort.html).  
//!

use std::rc::Rc;
use shared::Shared;
use std::fmt;
use std::fmt::{Debug,Formatter};
//use std::fmt::{Debug,Result};
use std::hash::{Hash,Hasher};

use normal;
use dynamics;

pub type Var = String;
// type of identifiers
pub type Ident = String;

/// Name Literals
///
/// In Fungi, names are binary trees, whose leaves are (optionally)
/// enriched with atomic data symbols (e.g., numbers and strings).
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize,PartialOrd,Ord)]
pub enum Name {
    /// Form a binary tree from two existing trees
    Bin(NameRec, NameRec),
    /// Form empty binary tree
    Leaf,
    /// Atomic string literal
    Sym(String),
    /// Atomic number literal
    Num(usize),
    NoParse(String),
}
pub type NameRec = Rc<Name>;

/// Name Terms
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize,PartialOrd,Ord)]
pub enum NameTm {
    /// Name-term level variable `x`, of some sort `g`:
    ///
    /// ```text
    ///  Γ(x) = g
    /// ----------- :: Var
    ///  Γ ⊢ x : g
    /// ```
    Var(Var),
    /// ```text
    ///  Γ(x) = (Γ', i)
    ///  Γ' ⊢ i : g
    /// ----------------- :: Ident  (contextual definition)
    ///  Γ ⊢ i : g
    /// ```    
    Ident(Ident),
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
    Bin(NameTmRec, NameTmRec),
    /// ```text
    ///  Γ, x:g1 ⊢ M : g2
    /// ------------------------- :: Lam
    ///  Γ ⊢ #x:g1. M : g1 -> g2
    /// ```
    Lam(Var, Sort, NameTmRec),
    /// ```text
    ///  Γ ⊢ M : g1 -> g2
    ///  Γ ⊢ N : g1
    /// ------------------ :: App
    ///  Γ ⊢ [M] N : g2
    /// ```
    App(NameTmRec, NameTmRec),
    /// `@@ : Nm -> Nm`
    ///
    /// This is the initial/default/neutral/ambient write scope.  All
    /// other write scopes are functions that compose with this one
    /// (where this function is always the "last" function in the
    /// composition).
    WriteScope,
    NoParse(String),
}
pub type NameTmRec = Rc<NameTm>;

/// Index terms
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize,PartialOrd,Ord)]
pub enum IdxTm {
    /// ```text
    ///  Γ(x) = g
    /// ----------- :: Var
    ///  Γ ⊢ x : g
    /// ```    
    Var(Var),
    /// ```text
    ///  Γ(x) = (Γ', i)
    ///  Γ' ⊢ i : g
    /// ----------------- :: Ident  (contextual definition)
    ///  Γ ⊢ i : g
    /// ```    
    Ident(Ident),
    /// ```text
    ///  Γ ⊢ M : Nm
    /// ------------------ :: Sing
    ///  Γ ⊢ { M } : NmSet
    /// ```    
    Sing(NameTm),
    /// ```text
    /// -------------- :: Empty
    ///  Γ ⊢ 0 : NmSet
    /// ```
    Empty,
    /// ```text
    ///  Γ ⊢ i : NmSet
    ///  Γ ⊢ j : NmSet
    /// ------------------- :: Apart
    ///  Γ ⊢ i % j : NmSet
    /// ```
    Apart(IdxTmRec, IdxTmRec),
    /// ```text
    ///  Γ ⊢ i : NmSet
    ///  Γ ⊢ j : NmSet
    /// ------------------- :: Union
    ///  Γ ⊢ i U j : NmSet
    /// ```
    Union(IdxTmRec, IdxTmRec),
    /// ```text
    /// -------------- :: Unit
    ///  Γ ⊢ () : ??
    /// ```    
    Unit,
    /// ```text
    ///  Γ ⊢ i : NmSet
    ///  Γ ⊢ j : NmSet
    /// ----------------------- :: Bin
    ///  Γ ⊢ i * j : NmSet
    /// ```
    Bin(IdxTmRec, IdxTmRec),
    /// ```text
    ///  Γ ⊢ i : g1
    ///  Γ ⊢ j : g2
    /// ------------------------- :: Pair
    ///  Γ ⊢ (i , j) : g1 x g2
    /// ```
    Pair(IdxTmRec, IdxTmRec),
    /// ```text
    ///  Γ ⊢ i : g1 x g2
    /// ------------------ :: Proj1
    ///  Γ ⊢ proj1 i : g1
    /// ```    
    Proj1(IdxTmRec),
    /// ```text
    ///  Γ ⊢ i : g1 x g2
    /// ------------------ :: Proj2
    ///  Γ ⊢ proj2 i : g2
    /// ```        
    Proj2(IdxTmRec),
    /// `@! : NmSet -> NmSet`
    ///
    /// The ambient write scope (`@@ : Nm -> Nm`), lifted to name sets.
    ///
    WriteScope,
    /// A normalized form for union/apart name sub-sets; never written
    /// directly by the programmer.  This form is used by the `normal`
    /// module for distributing set-level functions over a sets'
    /// constructors, for a uniform choice of type `NmSetCons`.
    NmSet(normal::NmSet),
    /// ```text
    ///  Γ, x:g1 ⊢ i : g2
    /// -------------------------- :: Lam
    ///  Γ ⊢ #x:g1. i : g1 -> g2
    /// ```
    Lam(Var, Sort, IdxTmRec),
    /// ```text
    ///  Γ ⊢ i : g1 -> g2
    ///  Γ ⊢ j : g1
    /// ------------------ :: App
    ///  Γ ⊢ {i} j : g2
    /// ```
    App(IdxTmRec, IdxTmRec),
    /// ```text
    ///  Γ ⊢ M : Nm -> Nm
    ///  Γ ⊢ j : NmSet
    /// ------------------ :: Map
    ///  Γ ⊢ [M] j : NmSet
    /// ```
    Map(NameTmRec, IdxTmRec),
    /// ```text
    ///  Γ ⊢ M : Nm -> Nm
    ///  Γ ⊢ j : NmSet
    /// ------------------ :: MapStar
    ///  Γ ⊢ [M]^* j : NmSet
    /// ```
    MapStar(NameTmRec, IdxTmRec),
    /// ```text
    ///  Γ ⊢ i : Nm -> NmSet
    ///  Γ ⊢ j : NmSet
    /// ----------------------- :: FlatMap
    ///  Γ ⊢ (i) j : NmSet
    /// ```
    FlatMap(IdxTmRec, IdxTmRec),
    /// ```text
    ///  Γ ⊢ i : Nm -> NmSet
    ///  Γ ⊢ j : NmSet
    /// ----------------------- :: FlatMapStar
    ///  Γ ⊢ (i)^* j : NmSet
    /// ```    
    FlatMapStar(IdxTmRec, IdxTmRec),
    NoParse(String),
    Unknown,
}
pub type IdxTmRec = Rc<IdxTm>;

/// Sorts (classify name and index terms)
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize,PartialOrd,Ord)]
pub enum Sort {
    Nm,
    NmSet,
    NmArrow(SortRec,SortRec),
    IdxArrow(SortRec,SortRec),
    Unit,
    Prod(SortRec,SortRec),
    NoParse(String),
}
pub type SortRec = Rc<Sort>;

/// Kinds (classify types)
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum Kind {
    Type,
    TypeParam(KindRec),
    IdxParam(Sort, KindRec),
    NoParse(String),
}
pub type KindRec = Rc<Kind>;

/// Propositions about name and index terms
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum Prop {
    Tt,
    Equiv(IdxTm, IdxTm, Sort),
    Apart(IdxTm, IdxTm, Sort),
    Conj(PropRec, PropRec),
    NoParse(String),
}
pub type PropRec = Rc<Prop>;

/// Effects
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum Effect {
    WR(IdxTm, IdxTm),
    //Then(EffectRec, EffectRec),
    NoParse(String),
}
pub type EffectRec = Rc<Effect>;

/// Value types
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum Type {
    Var(Var),
    Ident(Ident),
    Sum(TypeRec, TypeRec),
    Prod(TypeRec, TypeRec),
    Unit,
    Ref(IdxTm, TypeRec),
    Thk(IdxTm, CEffectRec),
    IdxApp(TypeRec, IdxTm),
    TypeApp(TypeRec, TypeRec),
    Nm(IdxTm),
    NmFn(NameTm),
    TypeFn(Var, Kind, TypeRec),
    IdxFn(Var, Sort, TypeRec),
    Rec(Var, TypeRec),
    // Exists for index-level variables; they are classified by sorts
    Exists(Var, SortRec, Prop, TypeRec),
    NoParse(String),
}
pub type TypeRec = Rc<Type>;

pub fn ident_nat()    -> Ident { "Nat".to_string() }
pub fn ident_bool()   -> Ident { "Bool".to_string() }
pub fn ident_string() -> Ident { "String".to_string() }

pub fn type_string()  -> Type { Type::Ident(ident_string()) }
pub fn type_nat()     -> Type { Type::Ident(ident_nat()) }
pub fn type_bool()    -> Type { Type::Ident(ident_bool()) }

/// Computation types
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum CType {
    Lift(Type),
    Arrow(Type,CEffectRec),
    NoParse(String),
}

/// Computation effects
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum CEffect {
    Cons(CType,Effect),
    ForallType(Var,Kind,CEffectRec),
    ForallIdx(Var,Sort,Prop,CEffectRec),
    NoParse(String),
}
pub type CEffectRec = Rc<CEffect>;

/// Value terms
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum Val {
    Var(Var),
    Unit,
    Pair(ValRec, ValRec),
    Inj1(ValRec),
    Inj2(ValRec),
    Roll(ValRec),
    Name(Name),
    NameFn(NameTm),
    Anno(ValRec,Type),

    /// Pack an index term that describes a given value.
    ///
    /// E.g., value `pack {@1} name @1` checks against type
    /// `exists a:NmSet | a in {@1,@2}. Nm[a]`.
    ///
    Pack(IdxTm, ValRec),
    
    /// Anonymous thunks ("ordinary" CBPV thunks).
    ///
    /// They can be written in the source program, and unlike named
    /// (store-allocated) thunks, and closed, run-time thunks, these
    /// thunks exist in the pre-evaluation AST (not the store); also,
    /// they don't yet have a run-time environment.
    ThunkAnon(ExpRec),

    /// Primitive (Rust) `bool`, injected into `Val` type
    Bool(bool),
    /// Primitive (Rust) `usize`, injected into `Val` type
    Nat(usize),
    /// Primitive (Rust) `String`, injected into `Val` type
    Str(String),

    // Parse errors
    NoParse(String),
}
pub type ValRec = Rc<Val>;

/// Host-language evaluation function (extend Rust-based Fungi interpreter).
///
/// For use as a trapdoor for many different primitives in Fungi's
/// standard library (e.g., vectors, strings, etc.).
#[derive(Clone,Serialize)]
pub struct HostEvalFn {
    pub path:String,
    pub arity:usize,
    #[serde(skip_serializing)]
    pub eval:Rc<Fn(Vec<dynamics::RtVal>) -> dynamics::ExpTerm>
}
impl Hash for HostEvalFn {
    fn hash<H:Hasher>(&self, hasher: &mut H) {
        self.path.hash(hasher)        
    }
}
impl Debug for HostEvalFn {
    fn fmt(&self, f:&mut Formatter) -> fmt::Result {
        write!(f, "HostEvalFn({:?})", self.path)
    }
}
impl PartialEq for HostEvalFn {
    fn eq(&self, other:&Self) -> bool {
        // TODO: FIX THIS; make this (more) sound, somehow.
        self.path == other.path
    }
}
impl Eq for HostEvalFn { }

/// Expressions (aka, computation terms)
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum PrimApp {
    // Binary combination of two names; produces a name.
    NameBin(Val,Val),

    // Force a value-producing thunk into a ref cell that holds this
    // produced value. (This operation forces the thunk).
    //
    // In detail: A practical variation of force, for when the forced
    // computation produces a value, and in particular, a data
    // structure (e.g., not an arrow); this primitive returns that
    // produced value, along with a reference cell that holds it;
    // behind the scenes, this reference cell is really just a pointer
    // to the forced thunk's cached value.
    //
    // Note: the only sound way to coerce a thunk into a reference
    // cell is to _force_ that thunk, and determine what value it
    // produces --- otherwise, the ref cell is not an "eager" data
    // value that can be inspected without forcing arbitrary effects,
    // but rather, a suspended computation, like the thunk, with such
    // effects.  Hence the value-computation duality of CBPV.
    RefThunk(Val),
    
    // Natural number equality test; produces a boolean
    NatEq(Val,Val),
    // Natural number less-than test; produces a boolean
    NatLt(Val,Val),
    // Natural number less-than-or-equal test; produces a boolean
    NatLte(Val,Val),
    // Natural number addition; produces a natural number
    NatPlus(Val,Val),

}

/// Expressions (aka, computation terms)
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum Exp {
    Doc(String, ExpRec),
    UseAll(UseAllModule, ExpRec),
    Decls(DeclsRec, ExpRec),
    AnnoE(ExpRec,CEffect),
    AnnoC(ExpRec,CType),
    Force(Val),
    Thunk(Val,ExpRec),
    Unroll(Val,Var,ExpRec),
    // unpack (a)x = (v) e
    Unpack(Var,Var,Val,ExpRec),
    Fix(Var,ExpRec),
    Ret(Val),
    DefType(Var,Type,ExpRec),
    Let(Var,ExpRec,ExpRec),
    Lam(Var, ExpRec),
    // Host language (Rust) function. Use cautiously.
    //
    // Generally unsafe, since this term checks against all
    // computation types of the correct arity.  Fungi does not check
    // the host language function; it trusts the programmer's
    // annotation to check the remainder of the Fungi program.  This
    // term does not synthesize a type; it only checks against a type
    // annotation, which is generally required.
    HostFn(HostEvalFn),
    App(ExpRec, Val),
    IdxApp(ExpRec, IdxTm),
    Split(Val, Var, Var, ExpRec),
    Case(Val, Var, ExpRec, Var, ExpRec),
    IfThenElse(Val, ExpRec, ExpRec),
    Ref(Val,Val),
    Get(Val),
    WriteScope(Val,ExpRec),
    NameFnApp(Val,Val),
    PrimApp(PrimApp),
    Unimp,
    DebugLabel(Option<Name>,Option<String>,ExpRec),
    NoParse(String),
}
pub type ExpRec = Rc<Exp>;

/// Each module consists of a declaration list body
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub struct Module {
    pub path:  String,
    pub body:  String,
    pub decls: Decls,
}

/// Declaration lists of pure terms; the body of each module.
///
/// Each declaration is a definition (an alias) for a pure term of
/// some `Type`, `Kind` or `Sort`.
///
/// Declaration lists are pure: There is no form for naming an
/// unthunked, effectful expression. In particular, there is no `let`
/// binding form for sequencing effects among the definitions here.
/// In particular, the `Val` and `Fn` forms can each express
/// recursive, effectful functions as values (thunks), but cannot
/// express unthunked applications of these terms. Consequently,
/// declaration lists are "pure" terms, when included within larger
/// expressions via the `UseAll` form, or other future import forms.
///
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum Decls {
    /// Use all of the definitions of another module
    UseAll(UseAllModule,    DeclsRec),
    /// Documentation string; from rustdoc
    Doc( String,            DeclsRec),
    /// Define a name term
    NmTm( String,NameTm,    DeclsRec),
    /// Define an index term
    IdxTm(String,IdxTm,     DeclsRec),
    /// Define a type
    Type( String,Type,      DeclsRec),
    /// Define a value   
    Val(  String,Option<Type>, Val, DeclsRec),
    /// Define a function
    Fn(   String,Type,Exp, DeclsRec),
    End,
    NoParse(String),
}
pub type DeclsRec = Rc<Decls>;

/// Declaration that uses (imports) all decls from another module
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub struct UseAllModule {
    pub path: String,
    pub module: Shared<Module>
}
