//! Target language AST --- aka, typed adapton AST defs

use std::rc::Rc;
use ast::{Var,Name,Pointer};

pub type NameTmRec = Rc<NameTm>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Name Terms
pub enum NameTm {
    Unit,
    Name(Name),
    Bin(NameTmRec, NameTmRec),
    Pair(NameTmRec, NameTmRec),
    Var(Var),
    Lam(Var,NameTmRec)
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
}


pub type SortRec = Rc<Sort>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Sorts (classify name and index terms)
pub enum Sort {
    Nm,
    NmSet,
    Arrow(SortRec,SortRec),
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
    Var(Var),
    Cons(TypeCons),
    Sum(TypeRec, TypeRec),
    Prod(TypeRec, TypeRec),
    Unit,
    Ref(IdxTm, TypeRec),
    Thk(IdxTm, CEffectRec),
    IdxApp(TypeRec, IdxTm),
    TypeApp(TypeRec, TypeRec),
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
    Cell(TCtxtRec,Pointer,Type),
    Thunk(TCtxtRec,Pointer,CType),
    Equiv(IdxTm,IdxTm,Sort),
    Apart(IdxTm,IdxTm,Sort),
    PropTrue(Prop),
}
impl TCtxt {
    /// bind a var and type
    pub fn var(&self,v:Var,t:Type) -> TCtxt {
        TCtxt::Var(Rc::new(self.clone()),v,t)
    }
    /// bind a pointer and value type
    pub fn cell(&self,p:Pointer,t:Type) -> TCtxt {
        TCtxt::Cell(Rc::new(self.clone()),p,t)
    }
    /// bind a pointer and computation type
    pub fn thk(&self,p:Pointer,ct:CType) -> TCtxt {
        TCtxt::Thunk(Rc::new(self.clone()),p,ct)
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
    NameTm(NameTm),
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
    Name(Name,ExpRec),
    PrimApp(PrimApp)
}

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
    SeqDup,
    SeqAppend(Val, Val),
    SeqFoldSeq(Val, Val, ExpRec),
    SeqFoldUp(Val, Val, ExpRec, ExpRec),
    SeqIntoStack(Val, Val),
    SeqIntoQueue(Val, Val),
    SeqIntoHashmap(Val),
    SeqIntoKvlog(Val),
    SeqMap(Val, ExpRec),
    SeqFilter(Val, ExpRec),
    SeqReverse(Val),

    // Stacks
    // ---------
    StackEmpty,
    StackIsEmpty(Val),
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
    KvlogDup,
    KvlogEmpty,
    KvlogIsEmpty,
    KvlogGet,
    KvlogPut,
    KvlogIntoSeq,
    KvlogIntoHashmap,
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
