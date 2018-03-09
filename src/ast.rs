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
//!  - Propositions (`P`):        [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_prop.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Prop.html).  
//!  - Sorts (`g`):               [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_sort.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Sort.html).  
//!

use std::rc::Rc;
use std::fmt;
use std::fmt::{Debug,Formatter};
//use std::fmt::{Debug,Result};
use std::hash::{Hash,Hasher};

use eval;
use normal;

pub type Var = String;
// type of identifiers
pub type Ident = String;

/// Name Literals
#[derive(Clone,Debug,Eq,PartialEq,Hash,PartialOrd,Ord)]
pub enum Name {
    Leaf,
    Sym(String),
    Num(usize),
    Bin(NameRec, NameRec),
    NoParse(String),
}
pub type NameRec = Rc<Name>;

/// Name Terms
#[derive(Clone,Debug,Eq,PartialEq,Hash,PartialOrd,Ord)]
pub enum NameTm {
    Var(Var),
    Name(Name),
    Bin(NameTmRec, NameTmRec),
    Lam(Var, Sort, NameTmRec),
    App(NameTmRec, NameTmRec),
    /// @@ : Nm -> Nm
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
#[derive(Clone,Debug,Eq,PartialEq,Hash,PartialOrd,Ord)]
pub enum IdxTm {
    Var(Var),
    Ident(Ident),
    Sing(NameTm),
    Empty,
    Apart(IdxTmRec, IdxTmRec),
    Union(IdxTmRec, IdxTmRec),
    Unit,
    /// All binary combinations of two name sets.
    ///
    /// This is a common special case of curried nameset mapping:
    ///
    /// `( i ,, j ) := (#a:Nm. ((#b:Nm. a,,b) j)) i`
    ///
    /// Since this double-mapping pattern is very common, we introduce
    /// a special AST node for it.
    ///
    /// `Bin` Sorting rule:
    ///
    /// ```text
    /// Gamma |- i : NmSet
    /// Gamma |- j : NmSet
    /// ---------------------------- :: Bin
    /// Gamma |- ( i ,, j ) : NmSet
    /// ```
    Bin(IdxTmRec, IdxTmRec),
    /// `Pair` Sorting rule:
    ///
    /// ```text
    /// Gamma |- i : g1
    /// Gamma |- j : g2
    /// ----------------------------- :: Pair
    /// Gamma |- ( i , j ) : g1 x g2
    /// ```
    Pair(IdxTmRec, IdxTmRec),
    Proj1(IdxTmRec),
    Proj2(IdxTmRec),
    /// @! : NmSet -> NmSet
    WriteScope,
    /// A normalized form for union/apart name sub-sets; never written
    /// directly by the programmer.  This form is used by the `normal`
    /// module for distributing set-level functions over a sets'
    /// constructors, for a uniform choice of type `NmSetCons`.
    NmSet(normal::NmSet),
    Lam(Var, Sort, IdxTmRec),
    App(IdxTmRec, IdxTmRec),
    Map(NameTmRec, IdxTmRec),
    FlatMap(IdxTmRec, IdxTmRec),
    Star(IdxTmRec, IdxTmRec),
    NoParse(String),
}
pub type IdxTmRec = Rc<IdxTm>;

/// Sorts (classify name and index terms)
#[derive(Clone,Debug,Eq,PartialEq,Hash,PartialOrd,Ord)]
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
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Kind {
    Type,
    TypeParam(KindRec),
    IdxParam(Sort, KindRec),
    NoParse(String),
}
pub type KindRec = Rc<Kind>;

/// Propositions about name and index terms
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Prop {
    Tt,
    Equiv(IdxTm, IdxTm, Sort),
    Apart(IdxTm, IdxTm, Sort),
    Conj(PropRec, PropRec),
    NoParse(String),
}
pub type PropRec = Rc<Prop>;

/// Effects
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Effect {
    WR(IdxTm, IdxTm),
    //Then(EffectRec, EffectRec),
    NoParse(String),
}
pub type EffectRec = Rc<Effect>;

/// Value types
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum CType {
    Lift(Type),
    Arrow(Type,CEffectRec),
    NoParse(String),
}

/// Computation effects
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum CEffect {
    Cons(CType,Effect),
    ForallType(Var,Kind,CEffectRec),
    ForallIdx(Var,Sort,Prop,CEffectRec),
    NoParse(String),
}
pub type CEffectRec = Rc<CEffect>;

/// Value terms
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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
#[derive(Clone)]
pub struct HostEvalFn {
    pub path:String,
    pub arity:usize,
    pub eval:Rc<Fn(Vec<eval::ast_dynamic::RtVal>) -> eval::ast_dynamic::ExpTerm>
}
impl Hash for HostEvalFn {
    fn hash<H:Hasher>(&self, _hasher: &mut H) {
        panic!("XXX")
    }
}
impl Debug for HostEvalFn {
    fn fmt(&self, f:&mut Formatter) -> fmt::Result {
        write!(f, "HostEvalFn({:?})", self.path)
    }
}
impl PartialEq for HostEvalFn {
    fn eq(&self, _other:&Self) -> bool {
        panic!("XXX")        
    }
}
impl Eq for HostEvalFn { }

/// Expressions (aka, computation terms)
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Exp {
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
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct UseAllModule {
    pub path: String,
    pub module: Rc<Module>
}
