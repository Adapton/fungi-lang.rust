//!  IODyn Source AST definitions

use std::cell::RefCell;
use std::fmt::{self,Debug};
use std::rc::Rc;
use std::collections::hash_map::HashMap;
use std::hash::Hash;
use eval::Env;

pub type Var = String;

pub type NameRec = Rc<Name>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Name {
    Leaf,
    Sym(String),
    Bin(NameRec, NameRec)
}
impl fmt::Display for Name {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match *self {
            Name::Leaf => write!(f,"[]"),
            Name::Sym(ref s) => write!(f,"[{}]",s),
            Name::Bin(ref n1, ref n2) => write!(f,"[{}{}]",&**n1,&**n2),
        }
    }
}
#[macro_export]
/// Constructor for Name
///
/// ```text
/// n ::=
///     []              (leaf)
///     [sym s]         (symbol)
///     [n]             (extra braces ignored)
///     [[n][n]...]     (extended bin)
/// ```
macro_rules! make_name {
    // [] (leaf)
    { [] } => { Name::Leaf };
    // [sym s] (symbol)
    { [sym $($s:tt)+]} => { Name::Sym(stringify![$($s)+].to_string())};
    // [n] (extra braces ignored)
    { [$(name:tt)+] } => { make_name![$(name)+] };
    // [[n][n]...] (extended bin)
    { [[$(name:tt)*] $($names:tt)+] } => {
        Name::Bin(Rc::new(make_name![[$(name)*]]),Rc::new(make_name![$($names)+]))
    };
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
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Type {
    Unit,
    Pair(TypeRec, TypeRec),
    Sum(TypeRec, TypeRec),
    Ref(TypeRec),
    U(CTypeRec),
    PrimApp(PrimTyApp)
}
#[macro_export]
/// Constructor for Type
///
/// ```text
/// t ::=
///     outerctx rust_expr  (insert variables, etc.)
///     (t1 x t2 x ...)     (extended product, unit, extra parens)
///     [t1 + t2 + ...]     (extended coproduct, unit, extra parens)
///     ref t
///     U ct
///     Prim
///     Prim(vars)
/// ```
macro_rules! make_type {
    // outerctx rust_expr (insert variables, etc.)
    { outerctx $out:expr } => { $out };
    // (t1 x t2 x ...) (extended product, unit, extra parens)
    { ($($types:tt)*) } => { split_cross![parse_product <= $($types)*] };
    // [t1 + t2 + ...] (extended coproduct, unit, extra parens)
    { [$($types:tt)*] } => { split_plus![parse_coproduct <= $($types)*] };
    // ref t
    { ref $($t:tt)+ } => { Type::Ref(Rc::new(make_type![$($t)+]))};
    // U ct
    { U $($ct:tt)+ } => { Type::U(Rc::new(make_ctype![$($ct)+]))};
    // F t  (not a value type, parse it and let the typechecker handle it)
    { F $($t:tt)+ } => { CType::F(Rc::new(make_type![$($t)+]))};
    // Prim
    { $ty:ident } => { Type::PrimApp(parse_prim_t![$ty]) };
    // Prim(vars)
    { $ty:ident($($vars:tt)*) } => { Type::PrimApp(split_comma![parse_prim_t ($ty) <= $($vars)*]) };
}
#[macro_export]
macro_rules! parse_product {
    // ()
    { } => { Type::Unit };
    // (t)
    { ($($type:tt)+) } => { make_type![$($type)+] };
    // (t x ...)
    { ($($type:tt)+) $($types:tt)+ } => { Type::Pair(
        Rc::new(make_type![$($type)+]),
        Rc::new(parse_type![$($types)+]),
    )};
}
#[macro_export]
macro_rules! parse_coproduct {
    // [] (empty type, using: unit type)
    { } => { Type::Unit };
    // [t]
    { ($($type:tt)+) } => { make_type![$($type)+] };
    // [t + ...]
    { ($($type:tt)+) $($types:tt)+ } => { Type::Sum(
        Rc::new(make_type![$($type)+]),
        Rc::new(parse_type![$($types)+]),
    )};
}

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum PrimTyApp {
    Bool,
    Char,
    Nat,
    Int,
    String,
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
#[macro_export]
macro_rules! parse_prim_t {
    {} => { PrimTyApp::Bool };
    { bool } => { PrimTyApp::Bool };
    { char } => { PrimTyApp::Char };
    { nat } => { PrimTyApp::Nat };
    { int } => { PrimTyApp::Int };
    { string } => { PrimTyApp::String };
    { Option($($type:tt)+) } => { PrimTyApp::Option(Rc::new(
        make_type![$($type)+]
    )) };
    { Seq($($type:tt)+) } => { PrimTyApp::Seq(Rc::new(
        make_type![$($type)+]
    )) };
    { List($($type:tt)+) } => { PrimTyApp::List(Rc::new(
        make_type![$($type)+]
    )) };
    { Queue($($type:tt)+) } => { PrimTyApp::Queue(Rc::new(
        make_type![$($type)+]
    )) };
    { Tok } => { PrimTyApp::Tok };
    { LexSt } => { PrimTyApp::LexSt };
}

pub type CTypeRec = Rc<CType>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum CType {
    Arrow(TypeRec,CTypeRec),
    F(TypeRec)
}
#[macro_export]
/// Constructor for CType
///
/// ```text
/// ct ::=
///     outerctx rust_expr          (insert variables, etc.)
///     F t
///     (ct)
///     t1 -> t2 -> ... -> ct       (arrow)
/// ```
macro_rules! make_ctype {
    // outerctx rust_expr (insert variables, etc.)
    { outerctx $out:expr } => { $out };
    // F t
    { F $($vt:tt)+} => { CType::F(Rc::new(make_type![$($vt)+])) };
    // (ct)
    { ( $($ct:tt)+ ) } => { make_ctype![$($ct)+] };
    // t1 -> t2 -> ... -> ct (arrow)
    { $($arrows:tt)+ } => { split_arrow![parse_arrow <= $($arrows)+] };
}
#[macro_export]
macro_rules! parse_arrow {
    // t (no arrow, make type and leave it up to the type checker)
    { ($($type:tt)+) } => { make_type![$($type)+] };
    // t -> ct
    { ($($type:tt)+) ($($ctype:tt)+) } => { CType::Arrow (
        Rc::new(make_type![$($type)+]),
        Rc::new(make_ctype![$($ctype)+]),
    )};
    // t1 -> t2 -> ... ct
    { ($($type1:tt)+) ($($type2:tt)+) $(($(types)+))+ } => { CType::Arrow(
        Rc::new(make_type![$($type1)+]),
        Rc::new(parse_arrow![($($type2)+) $(($(types)+))+]),
    )};
}

pub type TCtxtRec = Rc<TCtxt>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum TCtxt {
    Empty,
    Var(TCtxtRec,Var,Type),
    Cell(TCtxtRec,Pointer,Type),
    Thunk(TCtxtRec,Pointer,CType),
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

pub type ExpRec = Rc<Exp>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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
#[macro_export]
/// Constructor for Exp
///
/// ```text
/// e ::=
///     {e} : t                 (annotation)
///     get v
///     force v                 (force)
///     ref v
///     thk e
///     lam r.e                 (lambda)
///     fix f.e
///     {e} v                   (application)
///     let a = {e} e
///     split(v) x.y.e
///     case(v) x.{e0} y.{e1}
///     case(v) x.{e0} y.{e1} z.{e2} ...
///     ret v
///     [n] e                   (name-scoped)
///     prim(vars)
///     {e}
/// ```
macro_rules! make_exp {
    // {e} : t (annotation)
    { { $($exp:tt)* } : $($ty:tt)+ } => {{
        Exp::Anno(Rc::new(make_exp![$($exp)*]),make_ctype![$($ty)+])
    }};
    // get v
    { get $($ref:tt)+ } => {{ Exp::Get(make_val![$($ref)+]) }};
    // force v (force)
    { force $($ref:tt)+ } => {{ Exp::Force(make_val![$($ref)+]) }};
    // ref v
    { ref $($val:tt)+ } => {{ Exp::Ref(make_val![$($val)+]) }};
    // thk e
    { thk $($exp:tt)+ } => {{ Exp::Thunk(make_exp![$($exp)+]) }};
    // lam r.e (lambda)
    { lam $var:ident . $($body:tt)+ } => {{
        Exp::Lam(stringify![$var].to_string(),Rc::new(make_exp![$($body)+]))
    }};
    // fix f.e
    { fix $var:ident . $($body:tt)+ } => {{
        Exp::Fix(stringify![$var].to_string(),Rc::new(make_exp![$($body)+]))
    }};
    // {e} v (application)
    { { $($fun:tt)+ } $($par:tt)+ } => {{
        Exp::App(Rc::new(make_exp![$($fun)+]),make_val![$($par)+])
    }};
    // let a = {e} e
    { let $var:ident = {$($rhs:tt)+} $($body:tt)+} => {{
        Exp::Let(stringify![$var].to_string(), Rc::new(make_exp![$($rhs)+]), Rc::new(make_exp![$($body)*]))
    }};
    // TODO: let (a,b,...) = {e} e (split)
    // split(v) x.y.e
    { split($($v:tt)+) $x:ident . $y:ident . $($body:tt)+ } => {{
        Exp::Split(
            make_val![$($v:tt)+],
            stringify![$x].to_string(),
            stringify![$y].to_string(),
            Rc::new(make_exp![$($body)+]),
        )
    }};
    // case(v) x.{e0} y.{e1}
    { case($($v:tt)*) $var0:ident . {$(e0:tt)+} $var1:ident . {$(e1:tt)+} } => {{
        Exp::Case(
            make_val![$($v:tt)*],
            stringify![$var0].to_string(),
            Rc::new(make_exp![$(e0)+]),
            stringify![$var1].to_string(),
            Rc::new(make_exp![$(e1)+]),
        )
    }};
    // case(v) x.{e0} y.{e1} z.{e2} ...
    { case($($v:tt)*) $var0:ident . {$(e0:tt)+} $var1:ident . {$(e1:tt)+} $( $var2:ident . {$(e2:tt)+} )+} => {{
        Exp::Case(
            make_val![$($v:tt)*],
            stringify![$var0].to_string(),
            Rc::new(make_exp![$(e0)+]),
            stringify![case].to_string(),
            Rc::new(make_exp![case(case) $var1 . {$(e1)+} $( $var2 . {$(e2)+} )+]),
        )
    }};
    // ret v
    { ret $($ret:tt)+ } => {{ Exp::Ret(make_val![$($ret)+]) }};
    // [n] e (name-scoped)
    { [$($nm:tt)*] $($exp:tt)+ } => {{ Exp::Name(make_name!([$($nm)*]),Rc::new(make_exp![$($exp)+])) }};
    // prim(vars)
    { $fun:ident($($vars:tt)*)} => {{ Exp::PrimApp(split_comma![parse_prim_e ($fun) <= $($vars)*]) }};
    // {e}
    { {$($exp:tt)+} } => {{ make_exp![$($exp)+] }};
}
/// Primitive operation application forms.
///
/// We build-in collection primitives because doing so permits us to
/// avoid the machinery of polymorphic, higher-order functions in the
/// type system and translation of simple examples.  Eventually, we
/// want to handle these "primitives" as "ordinary functions" (not
/// built-in special cases), but for now, doing so is more complex
/// than we'd like (again, due to each of these functions generally
/// requiring a polymorphic, higher-order type).
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
    KvlogDup,
    KvlogEmpty,
    KvlogIsEmpty,
    KvlogGet,
    KvlogPut,
    KvlogIntoSeq,
    KvlogIntoHashmap,
}
#[macro_export]
macro_rules! parse_prim_e {
    { NatAdd($($v1:tt)+)($($v2:tt)+) } => {
        PrimApp::NatAdd(make_val![$($v1)+],make_val![$($v2)+])
    };
    { NatLte($($v1:tt)+)($($v2:tt)+) } => {
        PrimApp::NatLte(make_val![$($v1)+],make_val![$($v2)+])
    };
    { BoolAnd($($v1:tt)+)($($v2:tt)+) } => {
        PrimApp::BoolAnd(make_val![$($v1)+],make_val![$($v2)+])
    };
    { NatOfChar($($v:tt)+) } => {
        PrimApp::NatOfChar(make_val![$($v)+])
    };
    { CharOfNat($($v:tt)+) } => {
        PrimApp::CharOfNat(make_val![$($v)+])
    };
    { StrOfNat($($v:tt)+) } => {
        PrimApp::StrOfNat(make_val![$($v)+])
    };
    { NatOfStr($($v:tt)+) } => {
        PrimApp::NatOfStr(make_val![$($v)+])
    };
    { SeqEmpty } => { PrimApp::SeqEmpty };
    { SeqDup } => { PrimApp::SeqDup };
    { SeqAppend($($v1:tt)+)($($v2:tt)+) } => {
        PrimApp::SeqPush(make_val![$($v1)+],make_val![$($v2)+])
    };
    { SeqFoldSeq($($v1:tt)+)($($v2:tt)+)($($e1:tt)+) } => {
        PrimApp::SeqFoldSeq(
            make_val![$($v1)+],
            make_val![$($v2)+],
            Rc::new(make_exp![$($e1)+]),
        )
    };
    { SeqFoldUp($($v1:tt)+)($($v2:tt)+)($($e1:tt)+)($($e2:tt)+) } => {
        PrimApp::SeqFoldUp(
            make_val![$($v1)+],
            make_val![$($v2)+],
            Rc::new(make_exp![$($e1)+]),
            Rc::new(make_exp![$($e2)+]),
        )
    };
    { SeqIntoStack($($v1:tt)+)($($v2:tt)+) } => {
        PrimApp::SeqIntoStack(make_val![$($v1)+],make_val![$($v2)+])
    };
    { SeqIntoQueue($($v1:tt)+)($($v2:tt)+) } => {
        PrimApp::SeqIntoQueue(make_val![$($v1)+],make_val![$($v2)+])
    };
    { SeqIntoHashmap($($v:tt)+) } => {
        PrimApp::SeqIntoHashmap(make_val![$($v)+])
    };
    { SeqIntoKvlog($($v:tt)+) } => {
        PrimApp::SeqIntoKvlog(make_val![$($v)+])
    };
    { SeqMap($($v1:tt)+)($($e1:tt)+) } => {
        PrimApp::SeqMap(
            make_val![$($v1)+],
            Rc::new(make_exp![$($e1)+]),
        )
    };
    { SeqFilter($($v1:tt)+)($($e1:tt)+) } => {
        PrimApp::SeqFilter(
            make_val![$($v1)+],
            Rc::new(make_exp![$($e1)+]),
        )
    };
    { SeqReverse($($v:tt)+) } => {
        PrimApp::SeqReverse(make_val![$($v)+])
    };
    { StackEmpty } => { PrimApp::StackEmpty };
    { StackIsEmpty($($v:tt)+) } => {
        PrimApp::StackIsEmpty(make_val![$($v)+])
    };

    { StackDup($($v:tt)+) } => {
        PrimApp::StackDup(make_val![$($v)+])
    };
    { StackPush($($v1:tt)+)($($v2:tt)+) } => {
        PrimApp::StackPush(make_val![$($v1)+],make_val![$($v2)+])
    };
    { StackPop($($v:tt)+) } => {
        PrimApp::StackPop(make_val![$($v)+])
    };
    { StackPeek($($v:tt)+) } => {
        PrimApp::StackPeek(make_val![$($v)+])
    };
    { StackIntoSeq($($v:tt)+) } => {
        PrimApp::StackIntoSeq(make_val![$($v)+])
    };

    { QueueEmpty } => { PrimApp::QueueEmpty };
    { QueueIsEmpty($($v:tt)+) } => {
        PrimApp::QueueIsEmpty(make_val![$($v)+])
    };
    { QueueDup($($v:tt)+) } => {
        PrimApp::QueueDup(make_val![$($v)+])
    };
    { QueuePush($($v1:tt)+)($($v2:tt)+) } => {
        PrimApp::QueuePush(make_val![$($v1)+],make_val![$($v2)+])
    };
    { QueuePop($($v:tt)+) } => {
        PrimApp::QueuePop(make_val![$($v)+])
    };
    { QueuePeek($($v:tt)+) } => {
        PrimApp::QueuePeek(make_val![$($v)+])
    };
    { QueueIntoSeq($($v:tt)+) } => {
        PrimApp::QueueIntoSeq(make_val![$($v)+])
    };

    { KvlogDup } => { PrimApp::KvlogDup };
    { KvlogEmpty } => { PrimApp::KvlogEmpty };
    { KvlogIsEmpty } => { PrimApp::KvlogIsEmpty };
    { KvlogGet } => { PrimApp::KvlogGet };
    { KvlogPut } => { PrimApp::KvlogPut };
    { KvlogIntoSeq } => { PrimApp::KvlogIntoSeq };
    { KvlogIntoHashmap } => { PrimApp::KvlogIntoHashmap };
}

/*
#[derive(IODynAst)]
pub enum Option<A> { None, Some(A) }

let s = ...
let t = filter(dup(s), ...)
let r = map(s, ...)

type      : Val::get_iodyn_type() : Type
toIOdyn   : Option<Val> -> Val
fromIODyn : Val -> Option<Val>
fromIODyn(toIOdyn(None)) = None
//let t : Type = Val::get_iodyn_type() 
*/

pub type ValRec = Rc<Val>;
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Val {
    /// free variable
    Var(Var),
    /// Unit value
    Unit,
    /// Value pair
    Pair(ValRec,ValRec),
    /// Left injection
    Injl(ValRec),
    /// Right injection
    Injr(ValRec),
    /// Allocated reference; a pointer
    Ref(Pointer),
    /// Allocated thunk; a pointer
    Thunk(Pointer),
    /// Value type annotations
    Anno(ValRec,Type),
    /// Primitive natural number value
    Nat(usize),
    /// Primitive string value
    Str(String),

    /// Sequence of values
    ///
    /// Permits folds, splitting, concatenation
    Seq(Seq),

    /// Stack of values
    ///
    /// A sequence converts to a queue in XXX time.
    Stack(Stack),

    // /// Queue of values
    // ///
    // /// A sequence converts to a queue in XXX time.
    // //Queue(Queue<ValRec>),

    // /// Finite map of values, based on hashing key
    // ///
    // /// Hashmaps in IODyn permit lookups, extensions and folds, which
    // /// see the most recent value for each key (if any); older values,
    // /// if any, are forgotten.  A key-value log converts (in O(n)
    // /// time) to a hashmap that admits only the "most recent view" of
    // /// the key-value log to its folds.
    // //Hashmap(Hashmap<ValRec,ValRec>),

    // /// Key-value logs record key-value association history.
    // ///
    // /// Key-value logs in IODyn permit lookups and extension.  Each
    // /// log permits folds in chronological and reverse-chronological
    // /// order over its key-value entries.  Unlike a Hashmap, the fold
    // /// may revisit a key multiple times (if it is associated with
    // /// multiple values).  A hashmap converts (in O(n) time) to a
    // /// key-value log.
    // // Kvlog(Vec<(ValRec,ValRec)>),

    // /// Graphs are maps from node ids to
    // Graph(Graph)
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
    use super::{TCtxt,Type,CType,Var,Pointer,Name,PrimApp,Seq,Stack};

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
        Injl(ValTD),
        Injr(ValTD),
        Ref(Pointer),
        Thunk(Pointer),
        Anno(ValTD,Type),
        Nat(usize),
        Str(String),
        Seq(Seq),
        Stack(Stack),
    }

    /// Expression typing derivation
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub struct ExpTD { 
        pub ctxt:TCtxt,
        pub exp:Rc<Exp>,
        pub dir:Dir,
        pub ctyp:CType,
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
        PrimApp(PrimApp)
    }
}

#[macro_export]
/// Constructor for Val
///
/// ```text
/// v ::=
///     (v) : t         (annotation)
///     (v1,v2,...)     (tuples, unit, extra parens)
///     injl v
///     injr v
///     ref n
///     thk n           (thunk)
///     Stack(v,v,...)
///     "string"
///     a               (var)
///     num
/// ```
macro_rules! make_val {
    // (v) : t (annotation)
    { ($($v:tt)+) : $($t:tt)+ } => { Val::Anno(
        Rc::new(make_val![$($v:tt)+]),
        make_type![$($t:tt)+]
    )};
    // (v1,v2,...) (tuples, unit, extra parens)
    { ($($vals:tt)*) } => { split_comma![parse_tuple <= $($vals)*] };
    // TODO: better injections?
    // injl v
    { injl $($v:tt)+ } => { Val::Injl(Rc::new(make_val![$($v:tt)+])) };
    // injr v
    { injr $($v:tt)+ } => { Val::Injr(Rc::new(make_val![$($v:tt)+])) };
    // ref n
    { ref $($name:tt)+ } => { Val::Ref(Pointer(make_name![$($name:tt)+])) };
    // thk n (thunk)
    { thk $($name:tt)+ } => { Val::Thunk(Pointer(make_name![$($name:tt)+])) };
    // TODO: Seq
    // Stack(v,v,...)
    { Stack($($v:tt)*) } => { Val::Stack(split_comma![parse_valvec <= $($v:tt)*])};
    // "string"
    { "$($s:tt)*" } => { Val::Str(stringify![$($s)*].to_string()) };
    // a (var)
    { $a:ident } => { Val::Var(stringify![$a].to_string())};
    // num
    { $num:expr } => { Val::Nat($num) };
}
#[macro_export]
macro_rules! parse_tuple {
    // ()
    { } => { Val::Unit };
    // (v)
    { ($($val:tt)+) } => { make_val![$($val:tt)+] };
    // (v, ...)
    { ($($val:tt)+) $($vals:tt)+ } => { Val::Pair(
        Rc::new(make_val![$($val:tt)+]),
        Rc::new(parse_tuple![$($vals)+]),
    )};
}
#[macro_export]
macro_rules! parse_valvec {
    { $(($(v:tt)+))* } => { vec![$(Rc::new(make_val![$(v:tt)+]))*] };
}

// ///
// /// XXX: Move push and pop into the Stack/Queue trait only?
// ///
// /// Note on observable effects: The mutation in a sequence's
// /// implementation is not observable from within the IODyn program,
// /// however, since the IODyn language enforces an affine typing
// /// discipline (like Rust), with explicit cloning (like Rust).
// ///
// /// Cost to clone/duplicate: Unlike Rust, IODyn lacks a notion of
// /// "borrowing", and cloning is O(1) for collections that use
// /// Adapton. By contrast, cloning with ordinary Rust collections is
// /// typically O(n).  We use the term "duplicate" instead of "clone" to
// /// disambiguate the IODyn primitive from the Rust primitive.

/// Sequences of values, whose implementations of push and pop must
/// use mutation.
pub trait SeqObj : Debug {
    fn dup(&self) -> Box<SeqObj>;
    fn empty(&self) -> Box<SeqObj>;
    fn append(&self, Val) -> Box<SeqObj>;
    fn fold_seq(&self, Val, &Env, &Exp) -> Val;
    fn fold_up(&self, Val, &Env, &Exp, &Exp) -> Val;
    fn map(&self, &Env, &Exp) -> Box<SeqObj>;
    fn reverse(&mut self);
    fn filter(&self, &Env, &Exp) -> Box<SeqObj>;
    fn into_stack(&self, rev:bool) -> Box<StackObj>;
    fn into_queue(&self, rev:bool) -> Box<QueueObj>;
    fn into_hashmap(&self) -> Box<HashmapObj>;
    fn into_kvlog(&self) -> Box<KvlogObj>;
}

pub trait HashmapObj : Debug {
    fn dup(&self) -> Box<SeqObj>;
    fn empty(&self) -> Box<SeqObj>;
    fn append(&self, Val) -> Box<SeqObj>;
    fn get(&self, Val) -> Option<Val>;
    fn fold_seq(&self, Val, &Env, &Exp) -> Val;
    fn fold_up(&self, Val, &Env, &Exp, &Exp) -> Val;
    fn into_seq(&self) -> Box<SeqObj>;
    fn into_kvlog(&self) -> Box<KvlogObj>;
}

pub trait StackObj : Debug {
    fn dup(&self) -> Box<SeqObj>;
    fn empty(&self) -> Box<SeqObj>;
    fn is_empty(&self) -> bool;
    fn push(&mut self, Val);
    fn pop(&mut self) -> Option<Val>;
    fn peek(&self) -> Option<Val>;
    fn into_seq(&self) -> Box<SeqObj>;
}

pub trait QueueObj : Debug {
    fn dup(&self) -> Box<SeqObj>;
    fn empty(&self) -> Box<SeqObj>;
    fn is_empty(&self) -> bool;
    fn push(&mut self, Val);
    fn pop(&mut self) -> Option<Val>;
    fn peek(&self) -> Option<Val>;
    fn into_seq(&self) -> Box<SeqObj>;
}

pub trait KvlogObj : Debug {
    fn dup(&self) -> Box<SeqObj>;
    fn empty(&self) -> Box<SeqObj>;
    fn is_empty(&self) -> bool;
    fn get(&mut self, Val) -> Option<Val>;
    fn put(&mut self, Val, Val) -> Option<Val>;
    fn into_seq(&self) -> Box<SeqObj>;
    fn into_hashmap(&self) -> Box<HashmapObj>;
}

/// A graph is a binary relation between node identifiers, where nodes
/// and edges carry data.
///
/// A graph is a set of nodes, each with a distinct identifier (a
/// value).  Each node has data associated with it (another value,
/// possibly different from its identifier).  Each edge of each node
/// is identified by the node identifier of the edge's target (again,
/// a value).  Each edge carries data (a value).  This edge
/// representation does not (directly) permit graphs where there may
/// be several edges between two nodes, though we can encode such
/// graphs by using the data associated with each edge.
pub trait GraphObj : Debug {

}

#[derive(Clone,Debug)]
pub struct Seq {
    pub seq:Rc<RefCell<SeqObj>>
}
impl Eq        for Seq { }
impl PartialEq for Seq { fn eq(&self, _other:&Self) -> bool { unimplemented!() } }
impl Hash      for Seq { fn hash<H>(&self, _state: &mut H) { unimplemented!() } }

#[derive(Clone,Debug)]
pub struct Stack {
    pub stack:Rc<RefCell<StackObj>>
}
impl Eq        for Stack { }
impl PartialEq for Stack { fn eq(&self, _other:&Self) -> bool { unimplemented!() } }
impl Hash      for Stack { fn hash<H>(&self, _state: &mut H) { unimplemented!() } }

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Pointer(pub Name);

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
///   way, we can use macros to make the concrete syntax in Rust use
///   fewer parens)
///
pub mod cons {
    use super::*;
    pub fn val_nat(n:usize) -> Val { Val::Nat(n) }
    pub fn val_pair(v1:Val, v2:Val) -> Val { Val::Pair(Rc::new(v1), Rc::new(v2)) }
    pub fn val_option(v:Option<Val>) -> Val {
        match v {
            None     => val_none(),
            Some(v1) => val_some(v1),
        }
    }
    pub fn val_none() -> Val { Val::Injl(Rc::new(Val::Unit)) }
    pub fn val_some(v:Val) -> Val { Val::Injr(Rc::new(v)) }
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

////////////////////////
// Macro parsing helpers
////////////////////////

#[macro_export]
/// run a macro on a list of lists after splitting the input at commas
macro_rules! split_comma {
    // no defaults
    {$fun:ident <= $($item:tt)*} => {
        split_comma![$fun () () () <= $($item)*]
    };
    // give initial params to the function
    {$fun:ident ($($first:tt)*) <= $($item:tt)*} => {
        split_comma![$fun ($($first)*) () () <= $($item)*]
    };
    // give inital params and initial inner items in every group
    {$fun:ident ($($first:tt)*) ($($every:tt)*) <= $($item:tt)*} => {
        split_comma![$fun ($($first)*) ($($every)*) ($($every)*) <= $($item)*]
    };
    // on non-final seperator, stash the accumulator and restart it
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)*) <= , $($item:tt)+} => {
        split_comma![$fun ($($first)* ($($current)*)) ($($every)*) ($($every)*) <= $($item)*]
    };
    // ignore final seperator, run the function
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)+) <= , } => {
        $fun![$($first)* ($($current)*)]
    };
    // on next item, add it to the accumulator
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)*) <= $next:tt $($item:tt)*} => {
        split_comma![$fun ($($first)*) ($($every)*) ($($current)* $next)  <= $($item)*]
    };
    // at end of items, run the function
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)+) <= } => {
        $fun![$($first)* ($($current)*)]
    };
    // if there were no items and no default, run with only initial params, if any
    {$fun:ident ($($first:tt)*) () () <= } => {
        $fun![$($first)*]
    };
}
#[macro_export]
/// run a macro on a list of lists after splitting the input at x (product types)
macro_rules! split_cross {
    // no defaults
    {$fun:ident <= $($item:tt)*} => {
        split_cross![$fun () () () <= $($item)*]
    };
    // give initial params to the function
    {$fun:ident ($($first:tt)*) <= $($item:tt)*} => {
        split_cross![$fun ($($first)*) () () <= $($item)*]
    };
    // give inital params and initial inner items in every group
    {$fun:ident ($($first:tt)*) ($($every:tt)*) <= $($item:tt)*} => {
        split_cross![$fun ($($first)*) ($($every)*) ($($every)*) <= $($item)*]
    };
    // on non-final seperator, stash the accumulator and restart it
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)*) <= x $($item:tt)+} => {
        split_cross![$fun ($($first)* ($($current)*)) ($($every)*) ($($every)*) <= $($item)*]
    };
    // ignore final seperator, run the function
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)+) <= x } => {
        $fun![$($first)* ($($current)*)]
    };
    // on next item, add it to the accumulator
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)*) <= $next:tt $($item:tt)*} => {
        split_cross![$fun ($($first)*) ($($every)*) ($($current)* $next)  <= $($item)*]
    };
    // at end of items, run the function
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)+) <= } => {
        $fun![$($first)* ($($current)*)]
    };
    // if there were no items and no default, run with only initial params, if any
    {$fun:ident ($($first:tt)*) () () <= } => {
        $fun![$($first)*]
    };
}
#[macro_export]
/// run a macro on a list of lists after splitting the input at + (coproduct types)
macro_rules! split_plus {
    // no defaults
    {$fun:ident <= $($item:tt)*} => {
        split_plus![$fun () () () <= $($item)*]
    };
    // give initial params to the function
    {$fun:ident ($($first:tt)*) <= $($item:tt)*} => {
        split_plus![$fun ($($first)*) () () <= $($item)*]
    };
    // give inital params and initial inner items in every group
    {$fun:ident ($($first:tt)*) ($($every:tt)*) <= $($item:tt)*} => {
        split_plus![$fun ($($first)*) ($($every)*) ($($every)*) <= $($item)*]
    };
    // on non-final seperator, stash the accumulator and restart it
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)*) <= + $($item:tt)+} => {
        split_plus![$fun ($($first)* ($($current)*)) ($($every)*) ($($every)*) <= $($item)*]
    };
    // ignore final seperator, run the function
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)+) <= + } => {
        $fun![$($first)* ($($current)*)]
    };
    // on next item, add it to the accumulator
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)*) <= $next:tt $($item:tt)*} => {
        split_plus![$fun ($($first)*) ($($every)*) ($($current)* $next)  <= $($item)*]
    };
    // at end of items, run the function
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)+) <= } => {
        $fun![$($first)* ($($current)*)]
    };
    // if there were no items and no default, run with only initial params, if any
    {$fun:ident ($($first:tt)*) () () <= } => {
        $fun![$($first)*]
    };
}
#[macro_export]
/// run a macro on a list of lists after splitting the input at -> (arrow types)
macro_rules! split_arrow {
    // no defaults
    {$fun:ident <= $($item:tt)*} => {
        split_arrow![$fun () () () <= $($item)*]
    };
    // give initial params to the function
    {$fun:ident ($($first:tt)*) <= $($item:tt)*} => {
        split_arrow![$fun ($($first)*) () () <= $($item)*]
    };
    // give inital params and initial inner items in every group
    {$fun:ident ($($first:tt)*) ($($every:tt)*) <= $($item:tt)*} => {
        split_arrow![$fun ($($first)*) ($($every)*) ($($every)*) <= $($item)*]
    };
    // on non-final seperator, stash the accumulator and restart it
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)*) <= -> $($item:tt)+} => {
        split_arrow![$fun ($($first)* ($($current)*)) ($($every)*) ($($every)*) <= $($item)*]
    };
    // don't! ignore final seperator, run the function
    // {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)+) <= -> } => {
    //     $fun![$($first)* ($($current)*)]
    // };
    // on next item, add it to the accumulator
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)*) <= $next:tt $($item:tt)*} => {
        split_arrow![$fun ($($first)*) ($($every)*) ($($current)* $next)  <= $($item)*]
    };
    // at end of items, run the function
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)+) <= } => {
        $fun![$($first)* ($($current)*)]
    };
    // if there were no items and no default, run with only initial params, if any
    {$fun:ident ($($first:tt)*) () () <= } => {
        $fun![$($first)*]
    };
}
