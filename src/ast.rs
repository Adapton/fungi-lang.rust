//!  IODyn Source AST definitions

pub type Var = String;

pub struct NameRec ( Box<Name> );
pub enum Name {
    Leaf,
    Bin(NameRec, NameRec)
}

impl From<usize> for Name {
    fn from(n: usize) -> Self {
        match n {
            0 => Name::Leaf,
            n => Name::Bin(NameRec(Box::new(Name::Leaf)),
                           NameRec(Box::new(Name::from(n - 1))))
        }
    }
}

pub type TypeRec = Box<Type>;
pub enum Type {
    Base,      
    Pair(TypeRec, TypeRec),
    Sum(TypeRec, TypeRec),
    Ref(TypeRec),
    U(CTypeRec)
}

pub type CTypeRec = Box<CType>;
pub enum CType {
    Arrow(TypeRec,CTypeRec),
    F(TypeRec)
}

pub type TCtxtRec = Box<TCtxt>;
pub enum  TCtxt {
    Empty,
    BindVal(TCtxtRec,Var,Type),
    PointVal(TCtxtRec,Pointer,Type),
    PointThunk(TCtxtRec,Pointer,CType),
}

pub type ExpRec = Box<Exp>;
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

pub enum ExpTerm {
    Lam(Var, ExpRec),
    Ret(Val),
}

pub type ValRec = Box<Val>;
pub enum Val {
    Unit,
    Pair(ValRec,ValRec),
    Injl(ValRec),
    Injr(ValRec),
    Var(Var),
    Ref(Pointer),
    Thunk(Pointer),
}

pub struct Pointer(Name);

pub type StoreRec = Box<Store>;
pub enum Store {
    Empty,
    BindVal(StoreRec,Name,Val),
    BindExp(StoreRec,Name,Exp),
}
