//! Target language AST --- aka, typed adapton AST defs

use std::rc::Rc;

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Pointer(pub Name);
pub type Var = String;

pub type NameRec = Rc<Name>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Name {
    Leaf,
//    Sym(String),
//    Fileline(String,usize,Option<usize>),
    Bin(NameRec, NameRec)
}

pub type NameTmRec = Rc<NameTm>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Name Terms
pub enum NameTm {
    Name(Name),
    Bin(NameTmRec, NameTmRec),
    Var(Var),
    Lam(Var,NameTmRec),
    App(NameTmRec, NameTmRec),
}

pub type IdxTmRec = Box<IdxTm>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Index terms
pub enum IdxTm {
    Var,
    Sing(NameTm),
    Empty,
    Disj(IdxTmRec, IdxTmRec),
    Union(IdxTmRec, IdxTmRec),
    Unit,
    Pair(IdxTmRec, IdxTmRec),
    Proj1(IdxTmRec),
    Proj2(IdxTmRec),
    Lam(Var, IdxTmRec),
    App(IdxTmRec, IdxTmRec),
    Map(NameTmRec, IdxTmRec),
    FlatMap(IdxTmRec, IdxTmRec),
    Star(IdxTmRec, IdxTmRec),
}

pub type SortRec = Rc<Sort>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Sorts (classify name and index terms)
pub enum Sort {
    Nm,
    NmSet,
    NmArrow(SortRec,SortRec),
    IdxArrow(SortRec,SortRec),
    Unit,
    Prod(SortRec,SortRec),
}

pub type KindRec = Rc<Kind>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Kinds (classify types)
pub enum Kind {
    Type,
    TypeParam(KindRec),
    IdxParam(Sort, KindRec)
}

pub type PropRec = Rc<Prop>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Propositions about name and index terms
pub enum Prop {
    Tt,
    Equiv(IdxTm, IdxTm, Sort),
    Disj(IdxTm, IdxTm, Sort),
    Conj(PropRec, PropRec),
}

pub type EffectRec = Rc<Effect>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Effects
pub enum Effect {
    WR(IdxTm, IdxTm),
    Then(EffectRec, EffectRec),
}

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Type constructors
pub enum TypeCons {
    D,
    Seq,
    Nat
}

pub type TypeRec = Rc<Type>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Value types
pub enum Type {
    TVar(Var)
    Var(Var),
    Cons(TypeCons),
    Sum(TypeRec, TypeRec),
    Prod(TypeRec, TypeRec),
    Unit,
    Ref(IdxTm, TypeRec),
    Thk(IdxTm, CEffectRec),
    IdxApp(TypeRec, IdxTm),
    TypeApp(TypeCons, TypeRec),
    Nm(IdxTm),
    NmFn(NameTm),
    Rec(Var, TypeRec)
}

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Computation types
pub enum CType {
    Lift(Type),
    Arrow(Type,CEffectRec)
}

pub type CEffectRec = Rc<CEffect>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Computation effects
pub enum CEffect {
    Cons(CType,Effect),
    ForallType(Var,Kind,CEffectRec),
    ForallIdx(Var,Sort,Prop,CEffectRec)
}

pub type TCtxtRec = Rc<TCtxt>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum TCtxt {
    Empty,
    Var(TCtxtRec,Var,Type),
    IVar(TCtxtRec,Var,Sort),
    TVar(TCtxtRec,Var,Kind),
    TCons(TCtxtRec,TCons,Kind),
    Ref(TCtxtRec,Pointer,Type),
    Thunk(TCtxtRec,Pointer,CType),
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
        TCtxt::TCons(Rc::new(self.clone()),v,k)
    }
    /// bind a pointer and value type
    pub fn ref(&self,p:Pointer,t:Type) -> TCtxt {
        TCtxt::Ref(Rc::new(self.clone()),p,t)
    }
    /// bind a pointer and computation type
    pub fn thk(&self,p:Pointer,ct:CType) -> TCtxt {
        TCtxt::Thunk(Rc::new(self.clone()),p,ct)
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

pub type ValRec = Rc<Val>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Value terms
pub enum Val {
    Var(Var),
    Unit,
    Pair(ValRec, ValRec),
    Inj1(ValRec),
    Inj2(ValRec),
    Name(Name),
    NameFn(NameTm),
    Ref(Pointer),
    Thunk(Pointer),
    Anno(ValRec,Type),
    Nat(usize),
    Str(String),
}

pub type ExpRec = Rc<Exp>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Expressions (aka, computation terms)
pub enum Exp {
    Anno(ExpRec,CType),
    Force(Val),
    Thunk(ExpRec),
    Fix(Var,ExpRec),
    Ret(Val),
    Let(Var,ExpRec,ExpRec),
    Lam(Var, ExpRec),
    App(ExpRec, Val),
    Split(Val, Var, Var, ExpRec),
    Case(Val, Var, ExpRec, Var, ExpRec),
    Ref(Val),
    Get(Val),
    Scope(NameTm,ExpRec),
    // TODO: One more, `v_M v`
    DebugLabel(String,ExpRec),
}

/**********
TODO: Include additional features from Source Language

/// Primitive applications
///
/// TODO: Add optional ambient names as arguments (and results) to these primitives
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum PrimApp {
    // Scalars (implemented with Rust primitive types)
    // -----------------------------------------------
    NatAdd(Val, Val),
    NatLte(Val, Val),
    BoolAnd(Val, Val),
    NatOfChar(Val),
    CharOfNat(Val),
    StrOfNat(Val),
    /// parses nat into string; produces an optional nat, if no parse
    NatOfStr(Val),

    // Sequences (implemented as level trees, an IODyn collection)
    // ------------------------------------------------------------
    SeqEmpty,
    SeqGetFirst(Val),
    SeqSingleton(Val),
    SeqIsEmpty(Val),
    SeqDup(Val),
    SeqAppend(Val, Val),
    SeqFoldSeq(Val, Val, ExpRec),
    SeqFoldUp(Val, Val, ExpRec, ExpRec),
    SeqIntoStack(Val),
    SeqIntoQueue(Val),
    SeqIntoHashmap(Val),
    SeqIntoKvlog(Val),
    SeqMap(Val, ExpRec),
    SeqFilter(Val, ExpRec),
    SeqSplit(Val, ExpRec),
    SeqReverse(Val),

    // Stacks
    // ---------
    StackEmpty,
    StackIsEmpty(Val),
    /// asdfasdf
    ///
    /// ```text
    /// asdf
    /// -----
    /// asdfas
    /// ```
    StackDup(Val),
    StackPush(Val, Val),
    StackPop(Val),
    StackPeek(Val),
    StackIntoSeq(Val),

    // Queues
    // ---------
    QueueEmpty,
    QueueIsEmpty(Val),
    QueueDup(Val),
    QueuePush(Val, Val),
    QueuePop(Val),
    QueuePeek(Val),
    QueueIntoSeq(Val),

    // Kvlog
    // --------------
    KvlogEmpty,
    KvlogDup(Val),
    KvlogIsEmpty(Val),
    KvlogGet(Val,Val),
    KvlogPut(Val,Val,Val),
    KvlogIntoSeq(Val),
    KvlogIntoHashmap(Val),
}

/// Representations of ASTs as typing derivations.
///
/// One may think of a **typing derivation** as an AST that is
/// _annotated with typing contexts and types_.  The constructors of
/// this typing derivation correspond 1-1 with the constructors for
/// values and expressions, where the syntax tree structures of the
/// program term (expression or value) and its typing derivation
/// correspond 1-1.
//
pub mod typing {
    use std::rc::Rc;
    use super::{TCtxt,CType,Type,CEffect,Var,Pointer,Name,PrimApp,NameTm};

    /// Bidirectional bit: Synth or Check
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum Dir {
        Synth,
        Check,
    }

    /// Value typing derivation
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub struct ValTD {
        pub ctxt:TCtxt,
        pub val:Rc<Val>,
        pub dir:Dir,
        pub typ:Type,
    }

    /// Value forms, with typing sub-derivations for sub-values
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum Val {
        Var(Var),
        Unit,
        Pair(ValTD,ValTD),
        Inj1(ValTD),
        Inj2(ValTD),
        NameTm(NameTm),
        Ref(Pointer),
        Thunk(Pointer),
        Anno(ValTD,Type),
        Nat(usize),
        Str(String),
    }

    /// Expression typing derivation
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub struct ExpTD {
        pub ctxt:TCtxt,
        pub exp:Rc<Exp>,
        pub dir:Dir,
        pub ceffect:CEffect,
    }

    /// Expression forms, with typing sub-derivations for sub-expressions
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum Exp {
        Anno(ExpTD,CType),
        Force(Val),
        Thunk(ExpTD),
        Fix(Var,ExpTD),
        Ret(Val),
        Let(Var,ExpTD,ExpTD),
        Lam(Var, ExpTD),
        App(ExpTD, Val),
        Split(Val, Var, Var, ExpTD),
        Case(Val, Var, ExpTD, Var, ExpTD),
        Ref(Val),
        Get(Val),
        Name(Name,ExpTD),
        PrimApp(PrimApp),
    }
}

**************/
