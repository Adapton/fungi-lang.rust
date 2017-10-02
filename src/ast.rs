//!  IODyn Source AST definitions

use std::rc::Rc;

pub type Var = String;

pub type NameRec = Rc<Name>;
#[derive(Clone,Debug,Eq,PartialEq)]
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
#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Type {
    Unit,
    Pair(TypeRec, TypeRec),
    Sum(TypeRec, TypeRec),
    Ref(TypeRec),
    U(CTypeRec),
    PrimApp(PrimTyApp)
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum PrimTyApp {
    Bool,
    Char,
    Nat,
    Int,
    Option(TypeRec),
    Seq(TypeRec),
    List(TypeRec),
    Queue(TypeRec),
    // Temporaries:
    /// Tok -- TEMP(matthewhammer),
    Tok,
    /// LexSt -- TEMP(matthewhammer),
    LexSt
}

pub type CTypeRec = Rc<CType>;
#[derive(Clone,Debug,Eq,PartialEq)]
pub enum CType {
    Arrow(TypeRec,CTypeRec),
    F(TypeRec)
}

pub type TCtxtRec = Rc<TCtxt>;
#[derive(Clone,Debug,Eq,PartialEq)]
pub enum TCtxt {
    Empty,
    Var(TCtxtRec,Var,Type),
    Cell(TCtxtRec,Pointer,Type),
    Thunk(TCtxtRec,Pointer,CType),
}
impl TCtxt {
    /// bind a var and type
    pub fn var(self,v:Var,t:Type) -> TCtxt {
        TCtxt::Var(Rc::new(self),v,t)
    }
    /// bind a pointer and value type
    pub fn cell(self,p:Pointer,t:Type) -> TCtxt {
        TCtxt::Cell(Rc::new(self),p,t)
    }
    /// bind a pointer and computation type
    pub fn thk(self,p:Pointer,ct:CType) -> TCtxt {
        TCtxt::Thunk(Rc::new(self),p,ct)
    }
}

pub type ExpRec = Rc<Exp>;
#[derive(Clone,Debug,Eq,PartialEq)]
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

/// Primitive operation application forms.
///
/// We build-in collection primitives because doing so permits us
/// to avoid the machinery of polymorphic, higher-order functions in
/// the type system and translation of simple examples.  Eventually,
/// we want to handle these as "primitives" as "ordinary functions"
/// (not built-in special cases), but for now, doing so is more
/// complex than we'd like (again, due to each of these functions
/// generally requiring a polymorphic, higher-order type).
#[derive(Clone,Debug,Eq,PartialEq)]
pub enum PrimApp {
    // Scalars (implemented with Rust primitive types)
    // -----------------------------------------------
    /// nat_add
    NatAdd(Val, Val),
    /// nat_lte
    NatLte(Val, Val),
    /// bool_and
    BoolAnd(Val, Val),
    /// nat_of_char
    NatOfChar(Val),
    /// char_of_nat
    CharOfNat(Val),
    /// str_of_nat
    StrOfNat(Val),
    /// nat_of_str (produces an optional nat, if no parse)
    NatOfStr(Val),

    // Sequences (implemented as level trees, an IODyn collection)
    // ------------------------------------------------------------
    /// seq_empty
    SeqEmpty,
    /// seq_fold_seq( seq, accum0, \elm.\accum. ... )
    SeqFoldSeq(Val, Val, ExpRec),
    /// seq_fold_up( seq, v_emp, \elm. ..., \l.\r. ... )
    SeqFoldUp(Val, Val, ExpRec, ExpRec),
    /// seq_map( seq, \elm. ... )
    SeqMap(Val, ExpRec),
    /// seq_filter( seq, \elm. ... )
    SeqFilter(Val, ExpRec),
    /// seq_reverse( seq )
    SeqReverse(Val),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum ExpTerm {
    Lam(Var, ExpRec),
    Ret(Val),
}

pub type ValRec = Rc<Val>;
#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Val {
    Anno(ValRec,Type),
    Unit,
    Nat(usize),
    Str(String),
    Pair(ValRec,ValRec),
    Injl(ValRec),
    Injr(ValRec),
    Var(Var),
    Ref(Pointer),
    Thunk(Pointer),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct Pointer(Name);

pub type StoreRec = Rc<Store>;
#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Store {
    Empty,
    Val(StoreRec,Name,Val),
    Exp(StoreRec,Name,Exp),
}

/// Utilities for constructing ASTs, including common constructor patterns.
///
/// The objectives of the construction functions and macros are to:
/// - avoid Rc::new(_) in client code, or thinking about when it's needed.
/// - avoid quoting variable names in client code, or introducing strings for them.
/// - avoid all of the parens for nested lets, lambdas, and
///   applications (when these constructors are repeated in a nested
///   way, we can use macros to make the concrete syntax use fewer
///   parens)
///
pub mod cons {
    use super::*;
    pub fn val_nat(n:usize) -> Val { Val::Nat(n) }
    pub fn exp_ret(v:Val) -> Exp { Exp::Ret(v) }
    pub fn exp_anno(e:Exp, ct:CType) -> Exp { Exp::Anno(Rc::new(e), ct) }
    pub fn exp_force(v:Val) -> Exp { Exp::Force(v) }

    pub fn exp_nat_of_char(v:Val) -> Exp {
        Exp::PrimApp(PrimApp::NatOfChar(v))
    }
    pub fn exp_char_of_nat(v:Val) -> Exp {
        Exp::PrimApp(PrimApp::CharOfNat(v))
    }
    pub fn exp_nat_add(v1:Val, v2:Val) -> Exp {
        Exp::PrimApp(PrimApp::NatAdd(v1, v2))
    }
    pub fn exp_nat_lte(v1:Val, v2:Val) -> Exp {
        Exp::PrimApp(PrimApp::NatLte(v1, v2))
    }
    pub fn exp_bool_and(v1:Val, v2:Val) -> Exp {
        Exp::PrimApp(PrimApp::BoolAnd(v1, v2))
    }
    pub fn exp_nat_of_str(v:Val) -> Exp {
        Exp::PrimApp(PrimApp::NatOfStr(v))
    }
    pub fn exp_str_of_nat(v:Val) -> Exp {
        Exp::PrimApp(PrimApp::StrOfNat(v))
    }
    pub fn exp_seq_empty() -> Exp {
        Exp::PrimApp(PrimApp::SeqEmpty)
    }
    pub fn exp_seq_fold_seq(v_seq:Val, v_acc:Val, e_body:Exp) -> Exp {
        Exp::PrimApp(PrimApp::SeqFoldSeq(v_seq, v_acc, Rc::new(e_body)))
    }
    pub fn exp_seq_fold_up(v1:Val, v_nil:Val, e_elm:Exp, e_bin:Exp) -> Exp {
        Exp::PrimApp(PrimApp::SeqFoldUp(v1, v_nil, Rc::new(e_elm), Rc::new(e_bin)))
    }
    pub fn exp_seq_map(v1:Val, e_elm:Exp) -> Exp {
        Exp::PrimApp(PrimApp::SeqMap(v1, Rc::new(e_elm)))
    }
    pub fn exp_seq_filter(v1:Val, e_elm:Exp) -> Exp {
        Exp::PrimApp(PrimApp::SeqFilter(v1, Rc::new(e_elm)))
    }
    pub fn exp_seq_reverse(v1:Val) -> Exp {
        Exp::PrimApp(PrimApp::SeqReverse(v1))
    }
}

#[macro_export]
macro_rules! val_var {
    ( $var:ident ) => {
        Val::Var(stringify!($var).to_string())
    }
}

#[macro_export]
macro_rules! exp_lam {
  { $var:ident => $body:expr } => {{
    Exp::Lam(stringify!($var).to_string(), Rc::new($body))
  }};
  { $var1:ident , $( $var2:ident ),+ => $body:expr } => {{
    exp_lam!( $var1 => exp_lam!( $( $var2 ),+ => $body ) )
  }}
}

#[macro_export]
macro_rules! exp_app {
  ( $exp:expr ) => {{ $exp }}
  ;
  ( $exp:expr , $val:expr ) => {{
    Exp::App(Rc::new($exp), $val)
  }}
  ;
  ( $exp:expr , $val1:expr , $( $val2:expr ),+ ) => {{
    exp_app!( exp_app!($exp, $val1), $( $val2 ),+ )
  }}
}

#[macro_export]
macro_rules! exp_let {
  { $var:ident = $rhs:expr ; $body:expr } => {{
    Exp::Let(stringify!($var).to_string(), Rc::new($rhs), Rc::new($body))
  }};
  { $var1:ident = $rhs1:expr , $( $var2:ident = $rhs2:expr ),+ ; $body:expr } => {{
    exp_let!($var1 = $rhs1 ; exp_let!( $( $var2 = $rhs2 ),+ ; $body ))
  }};
}
