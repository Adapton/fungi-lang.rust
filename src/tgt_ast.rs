//! Target language AST --- aka, typed adapton AST defs

use std::rc::Rc;

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Pointer(pub Name);
pub type Var = String;

/// Name Literals
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Name {
    Leaf,
    Sym(String),
    Num(usize),
    Bin(NameRec, NameRec)
}
pub type NameRec = Rc<Name>;

/// Parser for Name Literals
///
/// ```text
/// n ::=
///     fromast ast_expr    (inject ast nodes)
///     []                  (leaf)
///     @s                  (symbol)
///     [n][n]...           (extended bin)
///     1                   (Number)
/// ```
#[macro_export]
macro_rules! tgt_name {
    // fromast ast_expr    (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    // [] (leaf)
    { [] } => { Name::Leaf };
    // @s (symbol)
    { @$($s:tt)+ } => { Name::Sym(stringify![$($s)+].to_string())};
    // [][n]... (extended bin with leaf)
    { [] $([$names:tt])+ } => {
        Name::Bin(Rc::new(Name::Leaf),Rc::new(tgt_name![$($names)+]))
    };
    // [n][n]... (extended bin)
    { [$(name:tt)+] $([$names:tt])+ } => {
        Name::Bin(Rc::new(tgt_name![$($name)*]),Rc::new(tgt_name![$($names)+]))
    };
    // 1 (Number)
    { $s:expr } => { Name::Num($s) };
}


/// Name Terms
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum NameTm {
    Var(Var),
    Name(Name),
    Bin(NameTmRec, NameTmRec),
    Lam(Var,NameTmRec),
    App(NameTmRec, NameTmRec),
}
pub type NameTmRec = Rc<NameTm>;

/// Parser for Name Terms
///
/// ```text
/// M,N ::=
///     fromast ast_expr    (inject ast nodes)
///     [N]                 (parens)
///     n, n, ...           (extended bin)
///     #a.M                (abstraction)
///     M N ...             (curried application)
///     a                   (Variable)
///     n                   (literal Name)
/// ```
#[macro_export]
macro_rules! tgt_nametm {
    //     fromast ast_expr    (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     [N]                 (parens)
    { [$($nmtm:tt)+] } => { tgt_nametm![$($nmtm:tt)+] };
    //     n, n,...            (extended bin)
    { $nmtm:tt, $($nmtms:tt)+ } => { NameTm::Bin(
        Rc::new(tgt_nametm![[$nmtm]]),
        Rc::new(tgt_nametm![$($nmtms)+])
    )};
    //     #a.M                (abstraction)
    { # $var:ident . $($body:tt)+ } => { NameTm::Lam(
        stringify![$var].to_string(),
        Rc::new(tgt_nametm![$($body)+]),
    )};
    //     M N               (single application)
    { $nmfn:tt $par:tt } => { NameTm::App(
        Rc::new(tgt_nametm![$($nmfn)+]),
        Rc::new(tgt_nametm![$par]),
    )};
    //     M N ...           (curried application)
    { $nmfn:tt $par:tt $($pars:tt)+ } => {
        tgt_nametm![[fromast NameTm::App(
            Rc::new(tgt_nametm![$nmfn]),
            Rc::new(tgt_nametm![$par]),
        )] $($pars)+]
    };
    //     a                   (Variable)
    { $var:ident } => { NameTm::Var(stringify![$var].to_string()) };
    //     n                   (literal Name)
    { $($nm:tt)+ } => { NameTm::Name(tgt_name![$($nm)+]) };
}

/// Index terms
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum IdxTm {
    Var(Var),
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
pub type IdxTmRec = Rc<IdxTm>;

/// Parser for Index Terms
///
/// ```text
/// i,j,X,Y ::=
///     fromast ast (inject ast nodes)
///     (i)         (parens)
///     {N}         (singleton name set)
///     0           (empty set)
///     X % Y       (separating union)
///     X U Y       (union)
///     ()          (unit)
///     (i,j)       (pairing)
///     prj1 i      (projection)
///     prj2 i      (projection)
///     #a.i        (abstraction)
///     {i} j ...   (curried application)
///     [M] j ...   (curried mapping)
///     (i) j ...   (curried flatmapping)
///     (i)* j      (iterated flatmapping)
///     a           (variable)
/// ```
#[macro_export]
macro_rules! tgt_index {
    //     fromast ast (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     (i)         (parens)
    { ($($i:tt)+) } => { tgt_index![$($i)+] };
    //     {N}         (singleton name set)
    { {$($nmtm:tt)+} } => { IdxTm::Sing(tgt_nametm![$($nmtm)+])};
    //     0           (empty set)
    { 0 } => { IdxTm::Empty };
    //     X % Y       (separating union)
    { $x:tt % $y:tt } => { IdxTm::Disj(
        Rc::new(tgt_index![$x]),
        Rc::new(tgt_index![$y]),
    )};
    //     X % Y ...   (separating union extended)
    { $x:tt % $y:tt $($more:tt)+ } => {
        tgt_index![(fromast IdxTm::Disj(
            Rc::new(tgt_index![$x]),
            Rc::new(tgt_index![$y]),
        )) $($more)+]
    };
    //     X U Y       (union)
    { $x:tt U $y:tt } => { IdxTm::Union(
        Rc::new(tgt_index![$x]),
        Rc::new(tgt_index![$y]),
    )};
    //     X U Y ...   (union extended)
    { $x:tt U $y:tt $($more:tt)+ } => {
        tgt_index![(fromast IdxTm::Union(
            Rc::new(tgt_index![$x]),
            Rc::new(tgt_index![$y]),
        )) $($more)+]
    };
    //     ()          (unit)
    { () } => { IdxTm::Unit };
    //     (i,j)       (pairing)
    { ($i:tt,$j:tt) } => { IdxTm::Pair(
        Rc::new(tgt_index![$i]),
        Rc::new(tgt_index![$j]),
    )};
    //     prj1 i      (projection)
    { prj1 $i:tt } => {
        IdxTm::Proj1(Rc::new(tgt_index![$i]))
    };
    //     prj2 i      (projection)
    { prj2 $i:tt } => {
        IdxTm::Proj2(Rc::new(tgt_index![$i]))
    };
    //     #a.i        (abstraction)
    { # $a:ident . $($body:tt)+ } => { IdxTm::Lam(
        stringify![$a].to_string(),
        Rc::new(tgt_index![$($body)+]),
    )};
    //     {i} j       (single application)
    { {$($i:tt)+} $par:tt } => { IdxTm::App(
        Rc::new(tgt_index![$($i)+]),
        Rc::new(tgt_index![$par]),
    )};
    //     {i} j ...   (curried application)
    { {$($i:tt)+} $par:tt $($pars:tt)+ } => {
        tgt_index![{fromast IdxTm::App(
            Rc::new(tgt_index![$($i)+]),
            Rc::new(tgt_index![$par]),
        )} $($pars)+]
    };
    //     [M] j       (single mapping)
    { {$($m:tt)+} $par:tt } => { IdxTm::Map(
        Rc::new(tgt_nametm![$($i)+]),
        Rc::new(tgt_index![$par]),
    )};
    //     [M] j ...   (curried mapping)
    { {$($m:tt)+} $par:tt $($pars:tt)+ } => {
        tgt_index![[fromast IdxTm::Map(
            Rc::new(tgt_nametm![$($m)+]),
            Rc::new(tgt_index![$par]),
        )] $($pars)+]
    };
    //     (i)* j      (iterated flatmapping)
    { ($($i:tt)+)* $($j:tt)+ } => { IdxTm::Star(
        Rc::new(tgt_index![$($i)+]),
        Rc::new(tgt_index![$($j)+]),
    )};
    //     (i) j ...   (curried flatmapping)
    { ($($i:tt)+) $($pars:tt)+ } => { IdxTm::FlatMap(
        curry_idxfmap![tgt_index![$($i)+] ; $($pars)+]
    )};
    //     (i) j       (single flatmapping)
    { ($($i:tt)+) $par:tt } => { IdxTm::FlatMap(
        Rc::new(tgt_index![$($i)+]),
        Rc::new(tgt_index![$par]),
    )};
    //     (i) j ...   (curried flatmapping)
    { ($($i:tt)+) $par:tt $($pars:tt)+ } => {
        tgt_index![(fromast IdxTm::FlatMap(
            Rc::new(tgt_index![$($i)+]),
            Rc::new(tgt_index![$par]),
        )) $($pars)+]
    };
    //     a           (variable)
    { $var:ident } => { IdxTm::Var(stringify![$var].to_string()) };
}

/// Sorts (classify name and index terms)
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Sort {
    Nm,
    NmSet,
    NmArrow(SortRec,SortRec),
    IdxArrow(SortRec,SortRec),
    Unit,
    Prod(SortRec,SortRec),
}
pub type SortRec = Rc<Sort>;

/// Parser for Sorts
///
/// ```text
/// g ::=
///     fromast ast         (inject ast nodes)
///     Nm                  (name)
///     NmSet               (name set)
///     1                   (unit index)
///     (g1 x g2 x ...)     (extended product index)
///     [g1 -> g2 -> ...]   (extended name term functions)
///     {g1 -> g2 -> ...}   (extended index functions)
///     (g)                 (parens)
/// ```
#[macro_export]
macro_rules! tgt_sort {
    //     fromast ast (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     Nm                  name
    { Nm } => { Sort::Nm };
    //     NmSet               name set
    { NmSet } => { Sort::NmSet };
    //     1                   unit index
    { 1 } => { Sort::Unit };
    //     (g1 x g2)           single product index
    { ($g1:tt x $g2:tt) } => { Sort::Prod(
        Rc::new(tgt_sort![$g1]),
        Rc::new(tgt_sort![$g2]),
    )};
    //     (g1 x g2 x ...)     extended product index
    { ($g1:tt x g2:tt x $($more:tt)+) } => { Sort::Prod(
        Rc::new(tgt_sort![$g1]),
        Rc::new(tgt_sort![($g2 x $($more)+)]),
    )};
    //     (g1 -> g2)          single name term functions
    { ($g1:tt -> $g2:tt) } => { Sort::NmArrow(
        Rc::new(tgt_sort![$g1]),
        Rc::new(tgt_sort![$g2]),
    )};
    //     [g1 -> g2 -> ...]     extended name term functions
    { ($g1:tt x g2:tt x $($more:tt)+) } => { Sort::NmArrow(
        Rc::new(tgt_sort![$g1]),
        Rc::new(tgt_sort![[$g2 x $($more)+]]),
    )};
    //     {g1 -> g2}            single index functions
    { ($g1:tt -> $g2:tt) } => { Sort::IdxArrow(
        Rc::new(tgt_sort![$g1]),
        Rc::new(tgt_sort![$g2]),
    )};
    //     {g1 -> g2 -> ...}     extended index functions
    { ($g1:tt x g2:tt x $($more:tt)+) } => { Sort::IdxArrow(
        Rc::new(tgt_sort![$g1]),
        Rc::new(tgt_sort![{$g2 x $($more)+}]),
    )};
    //     (g)                 (parens)
    { ($($sort:tt)+) } => { tgt_sort![$($sort:tt)+] }
}

/// Kinds (classify types)
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Kind {
    Type,
    TypeParam(KindRec),
    IdxParam(Sort, KindRec)
}
pub type KindRec = Rc<Kind>;

/// Parser for Kinds
///
/// ```text
/// K ::=
///     fromast ast (inject ast nodes)
///     (K)         (parens)
///     type        (kind of value types)
///     type => K   (type argument)
///     g => K      (index argument)
/// ```
#[macro_export]
macro_rules! tgt_kind {
    //     fromast ast (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     (K)         (parens)
    { ($($kind:tt)+) } => { tgt_kind![$($kind)+] };
    //     type        (kind of value types)
    { type } => { Kind::Type };
    //     type => K   (type argument)
    { type => $($kinds:tt)+ } => { Kind::TypeParam(
        Rc::new(tgt_kind![$($kinds)+])
    )};
    //     g => K      (index argument)
    { $g:tt => $($kinds:tt)+ } => { Kind::IdxParam(
        tgt_sort![$g],
        Rc::new(tgt_kind![$($kinds)+]),
    )};
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
    TVar(Var),
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
    Thunk(Val,ExpRec),
    Fix(Var,ExpRec),
    Ret(Val),
    Let(Var,ExpRec,ExpRec),
    Lam(Var, ExpRec),
    App(ExpRec, Val),
    Split(Val, Var, Var, ExpRec),
    Case(Val, Var, ExpRec, Var, ExpRec),
    Ref(Val,Val),
    Get(Val),
    Scope(NameTm,ExpRec),
    NameApp(Val,Val),
    Unimp,
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


////////////////////////
// Macro parsing helpers
////////////////////////

#[macro_export]
/// run a macro on a list of lists after splitting the input
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
/// run a macro on a list of lists after splitting the input
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
/// run a macro on a list of lists after splitting the input
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
    // // ignore final seperator, run the function
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
