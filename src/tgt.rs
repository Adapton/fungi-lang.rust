pub struct NameRec ( Box<Name> );
pub enum Name {
    Leaf,
    Bin(NameRec, NameRec)
}

pub fn name_from_usize(n:usize) -> Name {
    match n {
        0 => Name::Leaf,
        n => Name::Bin(NameRec(Box::new(Name::Leaf)), 
                       NameRec(Box::new(name_from_usize(n - 1))))
    }
}

pub type Var = String;

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
