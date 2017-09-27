//! Target language AST --- aka, typed adapton AST defs

/// Name Terms
pub struct NameTmRec ( Box<NameTm> );
pub enum NameTm {
    Unit,
    Name(Name),
    Bin(NameTmRec, NameTmRec),
    Pair(NameTmRec, NameTmRec),
    Var(Var),
    Lam(Var,NameTmRec)
}

/// Index terms
pub struct IdxTmRec ( Box<IdxTm> );
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

pub struct KindRec ( Box<Kind> );
pub enum Kind {
    Type,
    TypeParam(KindRec),
    IdxParam(Sort, KindRec)
}

pub struct PropRec ( Box<Prop> );
pub enum Prop {
    Tt,
    Equiv(IdxTm, IdxTm, Sort),
    Disj(IdxTm, IdxTm, Sort),
    Conj(PropRec, PropRec),
}

pub struct EffectRec (Box<Effect>);
pub enum Effect {
    WR(IdxTm, IdxTm),
    Then(EffectRec, EffectRec),
}

pub enum TypeCons {
    D,
    Seq,
    Nat
} 

pub enum Type {
    Var(Var),
    Cons(TypeCons),
    Sum(TypeRec, TypeRec),
    Prod(TypeRec, TypeRec),
    Unit,
    Ref(IdxTm, TypeRec),
    Thk(IdxTm, CEffect),
    IdxApp(TypeRec, IdxTm),
    TypeApp(TypeRec, TypeRec),
    Nm(IdxTm),
    NmFn(NameTm),
    Rec(Var, TypeRec)
}

pub enum CType {
    Lift,
    Fun(Type,CEffect)
}

pub enum CEffect {
    Cons(CType,Effect),
    ForallType(Var,Kind,CEffect),
    ForallIdx(Var,Sort,Prop,CEffect)
}

pub enum Value {
    Var(Var),
    Unit,
    Pair(ValueRec, ValueRec),
    Inj1(ValueRec),
    Inj2(ValueRec),
    NameTm(NameTm),
    Ref(

}
