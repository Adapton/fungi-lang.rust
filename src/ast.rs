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

type TypeRec = Box<Type>;
enum Type {
    Base,      
    Pair(TypeRec, TypeRec),
    Sum(TypeRec, TypeRec),
    Ref(TypeRec),
    U(TypeRec)
}

type CTypeRec = Box<CType>;
enum CType {
    Arrow(Type,CTypeRec),
    F(Type)
}

type ExpRec = Box<Exp>;
enum Exp {
    Force(Val),
    Fix(Var,ExpRec),
    Ret(Val),
    Let(Var,ExpRec,ExpRec),
    Lam(Var, ExpRec, ExpRec),
    App(ExpRec, Val),
    Split(Val, Var, Var, ExpRec),
    Case(Val, Var, ExpRec, Var, ExpRec),
    Ref(Val),
    Get(Val),
    Name(Name,ExpRec),
}

enum ExpTerm {
    Lam(Var, ExpRec),
    Ret(Val)
}

type ValRec = Box<Val>;
enum Val {
    TODO
}
