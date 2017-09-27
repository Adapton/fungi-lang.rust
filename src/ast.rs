//!  IODyn Source AST definitions

use std::rc::Rc;

pub type Var = String;

pub type NameRec = Rc<Name>;
#[derive(Clone,Eq,PartialEq)]
pub enum Name {
    Leaf,
    Bin(NameRec, NameRec)
}

impl From<usize> for Name {
    fn from(n: usize) -> Self {
        match n {
            0 => Name::Leaf,
            n => Name::Bin(
                Rc::new(Name::Leaf),
                Rc::new(Name::from(n - 1))
            )
        }
    }
}

pub type TypeRec = Rc<Type>;
#[derive(Clone,Eq,PartialEq)]
pub enum Type {
    Base,      
    Pair(TypeRec, TypeRec),
    Sum(TypeRec, TypeRec),
    Ref(TypeRec),
    U(CTypeRec)
}

pub type CTypeRec = Rc<CType>;
#[derive(Clone,Eq,PartialEq)]
pub enum CType {
    Arrow(TypeRec,CTypeRec),
    F(TypeRec)
}

pub type TCtxtRec = Rc<TCtxt>;
#[derive(Clone,Eq,PartialEq)]
pub enum  TCtxt {
    Empty,
    Val(TCtxtRec,Var,Type),
    Cell(TCtxtRec,Pointer,Type),
    Thunk(TCtxtRec,Pointer,CType),
}

pub type ExpRec = Rc<Exp>;
#[derive(Clone,Eq,PartialEq)]
pub enum Exp {
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
}

#[derive(Clone,Eq,PartialEq)]
pub enum ExpTerm {
    Lam(Var, ExpRec),
    Ret(Val),
}

pub type ValRec = Rc<Val>;
#[derive(Clone,Eq,PartialEq)]
pub enum Val {
    Unit,
    Pair(ValRec,ValRec),
    Injl(ValRec),
    Injr(ValRec),
    Var(Var),
    Ref(Pointer),
    Thunk(Pointer),
}

#[derive(Clone,Eq,PartialEq)]
pub struct Pointer(Name);

pub type StoreRec = Rc<Store>;
#[derive(Clone,Eq,PartialEq)]
pub enum Store {
    Empty,
    Val(StoreRec,Name,Val),
    Exp(StoreRec,Name,Exp),
}
