//! Syntax: abstract (via Rust datatypes) and concrete (via Rust macros).
//!
//! **Program terms**:  
//!  - Expressions (`e`):         [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_exp.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Exp.html).   
//!  - Values (`v`):              [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_val.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Val.html).  
//!
//! **Types and effects**:  
//!  - Value types (`A,B`):       [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_vtype.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Type.html).  
//!  - Computation types (`C,D`): [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_ctype.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.CType.html).  
//!  - Effect types (`E`):        [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_ceffect.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.CEffect.html).  
//!  - Effects (`ε`):             [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_effect.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Effect.html).  
//!  - Kinds (`K`):               [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_kind.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Kind.html).  
//!
//! **Index terms, name terms, sorts**:  
//!  - Name literals (`n`):       [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_name.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Name.html).  
//!  - Name terms (`N,M`):        [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_nametm.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.NameTm.html).  
//!  - Index terms (`i,j,X,Y,Z`): [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_index.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.IdxTm.html).  
//!  - Propositions (`P`):        [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_prop.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Prop.html).  
//!  - Sorts (`g`):               [concrete](https://docs.rs/fungi-lang/0/fungi_lang/macro.fgi_sort.html),
//!                               [abstract](https://docs.rs/fungi-lang/0/fungi_lang/ast/enum.Sort.html).  
//!

use std::rc::Rc;
use std::fmt;
use std::fmt::{Debug,Formatter,Result};
use std::hash::{Hash,Hasher};

use eval;

pub type Var = String;

/// Name Literals
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Name {
    Leaf,
    Sym(String),
    Num(usize),
    Bin(NameRec, NameRec),
    NoParse(String),
}
pub type NameRec = Rc<Name>;

/// Parser for Name Literals
///
/// ```text
/// n ::=
///     fromast ast_expr    (inject ast nodes)
///     []                  (leaf)
///     n,n, ...            (extended bin)
///     @@str               (symbol)
///     @123                (number)
/// ```
#[macro_export]
macro_rules! fgi_name {
    // fromast ast_expr    (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    // [] (leaf)
    { [] } => { Name::Leaf };
    // n,n, ... (extended bin)
    { name:tt, $($names:tt)+ } => {
        Name::Bin(Rc::new(fgi_name![$name]),Rc::new(fgi_name![$($names)+]))
    };
    // @@str (symbol)
    { @@$($s:tt)+ } => { Name::Sym(stringify![$($s)+].to_string())};
    // @123 (number)
    { @$n:expr } => { Name::Num($n) };
    // failure
    { $($any:tt)* } => { Name::NoParse(stringify![$($any)*].to_string())};
}


/// Name Terms
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum NameTm {
    Var(Var),
    Name(Name),
    Bin(NameTmRec, NameTmRec),
    Lam(Var, Sort, NameTmRec),
    App(NameTmRec, NameTmRec),
    NoParse(String),
}
pub type NameTmRec = Rc<NameTm>;

/// Parser for Name Terms
///
/// ```text
/// M,N ::=
///     fromast ast_expr    (inject ast nodes)
///     [N]                 (parens)
///     #a:g.M              (abstraction)
///     [M] N ...           (curried application)
///     a                   (Variable)
///     M, N, ...           (extended bin)
///     n                   (literal Name)
/// ```
#[macro_export]
macro_rules! fgi_nametm {
    //     fromast ast_expr    (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     [N]                 (parens)
    { [$($nmtm:tt)+] } => { fgi_nametm![$($nmtm)+] };
    //     @n                  (literal name)
    { @$($nm:tt)+ } => { NameTm::Name(fgi_name![@$($nm)+]) };
    //     #a:g.M                (abstraction)
    { # $var:ident : $sort:tt . $($body:tt)+ } => { NameTm::Lam(
        stringify![$var].to_string(),
        fgi_sort![$sort],
        Rc::new(fgi_nametm![$($body)+]),
    )};
    //     [M] N             (single application)
    { [$($nmfn:tt)+] $par:tt } => { NameTm::App(
        Rc::new(fgi_nametm![$($nmfn)+]),
        Rc::new(fgi_nametm![$par]),
    )};
    //     [M] N ...         (curried application)
    { [$($nmfn:tt)+] $par:tt $($pars:tt)+ } => {
        fgi_nametm![[fromast NameTm::App(
            Rc::new(fgi_nametm![$($nmfn)+]),
            Rc::new(fgi_nametm![$par]),
        )] $($pars)+]
    };
    //     a                   (Variable)
    { $var:ident } => { NameTm::Var(stringify![$var].to_string()) };
    //     M, N, ...           (extended bin, literal names)
    { $($nmtms:tt)+ } => { split_comma![parse_fgi_name_bin <= $($nmtms)+]};
    // failure
    { $($any:tt)* } => { NameTm::NoParse(stringify![$($any)*].to_string())};
}
/// this macro is a helper for fgi_nametm, not for external use
#[macro_export]
macro_rules! parse_fgi_name_bin {
    // M
    { ($($n:tt)+) } => { NameTm::Name(fgi_name![$($n)+]) };
    // M,N
    { ($($n:tt)+)($($m:tt)+) } => { NameTm::Bin(
        Rc::new(fgi_nametm![$($n)+]),
        Rc::new(fgi_nametm![$($m)+]),
    )};
    // M,N, ...
    { ($($n:tt)+)($($m:tt)+) $($more:tt)+ } => { NameTm::Bin(
        Rc::new(fgi_nametm![$($n)+]),
        Rc::new(parse_fgi_name_bin![($($m)+) $($more)+]),
    )};
    // failure
    { $($any:tt)* } => { NameTm::NoParse(stringify![(, $($any)*)].to_string())};
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
    Lam(Var, Sort, IdxTmRec),
    App(IdxTmRec, IdxTmRec),
    Map(NameTmRec, IdxTmRec),
    FlatMap(IdxTmRec, IdxTmRec),
    Star(IdxTmRec, IdxTmRec),
    NoParse(String),
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
///     X % Y ...   (separating union extended - left to right)
///     X U Y ...   (union extended - left to right)
///     ()          (unit)
///     (i,j)       (pairing)
///     prj1 i      (projection)
///     prj2 i      (projection)
///     #a:g.i      (abstraction)
///     {i} j ...   (curried application)
///     [M] j       (mapping)
///     (i) j       (flatmapping)
///     (i)* j      (iterated flatmapping)
///     a           (variable)
/// ```
#[macro_export]
macro_rules! fgi_index {
    //     fromast ast (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     (i)         (parens)
    { ($($i:tt)+) } => { fgi_index![$($i)+] };
    //     {N}         (singleton name set)
    { {$($nmtm:tt)+} } => { IdxTm::Sing(fgi_nametm![$($nmtm)+])};
    //     0           (empty set)
    { 0 } => { IdxTm::Empty };
    //     X % Y       (separating union)
    { $x:tt % $y:tt } => { IdxTm::Disj(
        Rc::new(fgi_index![$x]),
        Rc::new(fgi_index![$y]),
    )};
    //     X % Y ...   (separating union extended - left to right)
    { $x:tt % $y:tt $($more:tt)+ } => {
        fgi_index![(fromast IdxTm::Disj(
            Rc::new(fgi_index![$x]),
            Rc::new(fgi_index![$y]),
        )) $($more)+]
    };
    //     X U Y       (union)
    { $x:tt U $y:tt } => { IdxTm::Union(
        Rc::new(fgi_index![$x]),
        Rc::new(fgi_index![$y]),
    )};
    //     X U Y ...   (union extended - left to right)
    { $x:tt U $y:tt $($more:tt)+ } => {
        fgi_index![(fromast IdxTm::Union(
            Rc::new(fgi_index![$x]),
            Rc::new(fgi_index![$y]),
        )) $($more)+]
    };
    //     ()          (unit)
    { () } => { IdxTm::Unit };
    //     (i,j)       (pairing)
    { ($i:tt,$j:tt) } => { IdxTm::Pair(
        Rc::new(fgi_index![$i]),
        Rc::new(fgi_index![$j]),
    )};
    //     prj1 i      (projection)
    { prj1 $($i:tt)+ } => {
        IdxTm::Proj1(Rc::new(fgi_index![$i]))
    };
    //     prj2 i      (projection)
    { prj2 $($i:tt)+ } => {
        IdxTm::Proj2(Rc::new(fgi_index![$i]))
    };
    //     #a:g.i        (abstraction)
    { # $a:ident : $sort:tt . $($body:tt)+ } => { IdxTm::Lam(
        stringify![$a].to_string(),
        fgi_sort![$sort],
        Rc::new(fgi_index![$($body)+]),
    )};
    //     {i} j       (single application)
    { {$($i:tt)+} $par:tt } => { IdxTm::App(
        Rc::new(fgi_index![$($i)+]),
        Rc::new(fgi_index![$par]),
    )};
    //     {i} j ...   (curried application)
    { {$($i:tt)+} $par:tt $($pars:tt)+ } => {
        fgi_index![{fromast IdxTm::App(
            Rc::new(fgi_index![$($i)+]),
            Rc::new(fgi_index![$par]),
        )} $($pars)+]
    };
    //     [M] j       (mapping)
    { [$($m:tt)+] $($par:tt)+ } => { IdxTm::Map(
        Rc::new(fgi_nametm![$($m)+]),
        Rc::new(fgi_index![$($par)+]),
    )};
    //     (i)* j      (iterated flatmapping)
    { ($($i:tt)+)* $($j:tt)+ } => { IdxTm::Star(
        Rc::new(fgi_index![$($i)+]),
        Rc::new(fgi_index![$($j)+]),
    )};
    //     (i) j       (flatmapping)
    { ($($i:tt)+) $($par:tt)+ } => { IdxTm::FlatMap(
        Rc::new(fgi_index![$($i)+]),
        Rc::new(fgi_index![$($par)+]),
    )};
    //     a           (variable)
    { $var:ident } => { IdxTm::Var(stringify![$var].to_string()) };
    // failure
    { $($any:tt)* } => { IdxTm::NoParse(stringify![$($any)*].to_string())};
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
    NoParse(String),
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
macro_rules! fgi_sort {
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
        Rc::new(fgi_sort![$g1]),
        Rc::new(fgi_sort![$g2]),
    )};
    //     (g1 x g2 x ...)     extended product index
    { ($g1:tt x g2:tt x $($more:tt)+) } => { Sort::Prod(
        Rc::new(fgi_sort![$g1]),
        Rc::new(fgi_sort![($g2 x $($more)+)]),
    )};
    //     (g1 -> g2)          single name term functions
    { ($g1:tt -> $g2:tt) } => { Sort::NmArrow(
        Rc::new(fgi_sort![$g1]),
        Rc::new(fgi_sort![$g2]),
    )};
    //     [g1 -> g2 -> ...]     extended name term functions
    { ($g1:tt -> g2:tt -> $($more:tt)+) } => { Sort::NmArrow(
        Rc::new(fgi_sort![$g1]),
        Rc::new(fgi_sort![[$g2 -> $($more)+]]),
    )};
    //     {g1 -> g2}            single index functions
    { ($g1:tt -> $g2:tt) } => { Sort::IdxArrow(
        Rc::new(fgi_sort![$g1]),
        Rc::new(fgi_sort![$g2]),
    )};
    //     {g1 -> g2 -> ...}     extended index functions
    { ($g1:tt -> g2:tt -> $($more:tt)+) } => { Sort::IdxArrow(
        Rc::new(fgi_sort![$g1]),
        Rc::new(fgi_sort![{$g2 -> $($more)+}]),
    )};
    //     (g)                 (parens)
    { ($($sort:tt)+) } => { fgi_sort![$($sort:tt)+] };
    // failure
    { $($any:tt)* } => { Sort::NoParse(stringify![$($any)*].to_string())};
}

/// Kinds (classify types)
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Kind {
    Type,
    TypeParam(KindRec),
    IdxParam(Sort, KindRec),
    NoParse(String),
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
macro_rules! fgi_kind {
    //     fromast ast (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     (K)         (parens)
    { ($($kind:tt)+) } => { fgi_kind![$($kind)+] };
    //     type        (kind of value types)
    { type } => { Kind::Type };
    //     type => K   (type argument)
    { type => $($kinds:tt)+ } => { Kind::TypeParam(
        Rc::new(fgi_kind![$($kinds)+])
    )};
    //     g => K      (index argument)
    { $g:tt => $($kinds:tt)+ } => { Kind::IdxParam(
        fgi_sort![$g],
        Rc::new(fgi_kind![$($kinds)+]),
    )};
    // failure
    { $($any:tt)* } => { Kind::NoParse(stringify![$($any)*].to_string())};
}

/// Propositions about name and index terms
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Prop {
    Tt,
    Equiv(IdxTm, IdxTm, Sort),
    Disj(IdxTm, IdxTm, Sort),
    Conj(PropRec, PropRec),
    NoParse(String),
}
pub type PropRec = Rc<Prop>;

/// Parser for Propositions
///
/// ```text
/// P ::=
///     fromast ast     (inject ast nodes)
///     (P)             (parens)
///     tt              (truth)
///     P and P and ... (extended conjunction)
///     i % j : g       (index apartness)
///     i = j : g       (index equivalence)
/// ```
#[macro_export]
macro_rules! fgi_prop {
    //     fromast ast     (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     (P)             (parens)
    { ($($prop:tt)+) } => { fgi_prop![$($prop)+] };
    //     tt              (truth)
    { tt } => { Prop::Tt };
    //     P and P and ... (extended conjunction)
    { $p1:tt and $p2:tt and $($more:tt)+ } => {
        fgi_prop![(fromast Prop::Conj(
            Rc::new(fgi_prop![$p1]),
            Rc::new(fgi_prop![$p2]),
        )) and $($more)+ ]
    };
    //     P and P         (single conjunction)
    { $p1:tt and $($p2:tt)+ } => { Prop::Conj(
        Rc::new(fgi_prop![$p1]),
        Rc::new(fgi_prop![$($p2)+]),
    )};
    //     i % j : g       (index apartness)
    { $i:tt % $j:tt : $($g:tt)+ } => { Prop::Disj(
        fgi_index![$i],
        fgi_index![$j],
        fgi_sort![$g],
    )};
    //     i = j : g       (index equivalence)
    { $i:tt = $j:tt : $($g:tt)+ } => { Prop::Equiv(
        fgi_index![$i],
        fgi_index![$j],
        fgi_sort![$g],
    )};
    // failure
    { $($any:tt)* } => { Prop::NoParse(stringify![$($any)*].to_string())};
}

/// Effects
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Effect {
    WR(IdxTm, IdxTm),
    Then(EffectRec, EffectRec),
    NoParse(String),
}
pub type EffectRec = Rc<Effect>;

/// Parser for Effects
///
/// ```text
/// ε ::=
///     fromast ast        (inject ast nodes)
///     (ε)                (parens)
///     {X;Y}              (<Write; Read> effects)
///     0                  (sugar - {0;0})
///     ε1 then ε2 ...     (extended effect sequencing)
/// ```
#[macro_export]
macro_rules! fgi_effect {
    //     fromast ast        (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     (ε)                (parens)
    { ($($e:tt)+) } => { fgi_effect![$($e)+] };
    //     {X;Y}              (<Write; Read> effects)
    { {$($wr:tt)+} } => { split_semi![parse_fgi_eff <= $($wr)+]};
    //     0                  (sugar - {0;0})
    { 0 } => { fgi_effect![ {0;0} ] };
    //     ε1 then ε2         (sinlge effect sequencing)
    { $e1:tt then $e2:tt } => { Effect::Then(
        Rc::new(fgi_effect![$e1]),
        Rc::new(fgi_effect![$e2]),
    )};
    //     ε1 then ε2 ...     (extended effect sequencing)
    { $e1:tt then $e2:tt $($more:tt)+ } => {
        fgi_effect![(fromast Effect::Then(
            Rc::new(fgi_effect![$e1]),
            Rc::new(fgi_effect![$e2]),
        )) $($more)+]
    };
    // failure
    { $($any:tt)* } => { Effect::NoParse(stringify![$($any)*].to_string())};
}
/// this macro is a helper for fgi_effect, not for external use
#[macro_export]
macro_rules! parse_fgi_eff {
    { ($($w:tt)+)($($r:tt)+) } => { Effect::WR(
        fgi_index![$($w)+],
        fgi_index![$($r)+],
    )};
    // failure
    { $($any:tt)* } => { Effect::NoParse(stringify![(; $($any)*)].to_string())};
}

/// Type constructors
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum TypeCons {
    D,
    Bool,
    Nat,
    String,
    Seq,
    User(String),
    NoParse(String),
}
/// Parser for TypeConstructors
#[macro_export]
macro_rules! fgi_tcons {
    { D } => { TypeCons::D };
    { Bool } => { TypeCons::Bool };
    { Nat } => { TypeCons::Nat };
    { String } => { TypeCons::String };
    { Seq } => { TypeCons::Seq };
    { $s:ident } => { TypeCons::User(stringify![$s].to_string()) };
    // failure
    { $($any:tt)* } => { TypeCons::NoParse(stringify![$($any)*].to_string())};
}

/// Value types
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
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
    TypeFn(Var, Kind, TypeRec),
    IdxFn(Var, Sort, TypeRec),
    Rec(Var, TypeRec),
    // Exists for index-level variables; they are classified by sorts
    Exists(Var, SortRec, Prop, TypeRec),
    NoParse(String),
}
pub type TypeRec = Rc<Type>;

/// Parser for value types
/// 
/// ```text
/// A,B ::=
///     fromast ast     (inject ast nodes)
///     (A)             (parens)
///     D,Bool,Seq,...  (type constructors)
///     user(type)      (user-defined)
///     Unit            (unit)
///     + A + B ...     (extended sums)
///     x A x B ...     (extended product)
///     Ref[i] A        (named ref cell)
///     Thk[i] E        (named thunk with effects)
///     Nm[i]           (name type)
///     A[i]...         (extended application of type to index)
///     (Nm->Nm)[M]     (name function type)
///     forallt (a,b,...):K.A   (type parameter)
///     foralli (a,b,...):g.A   (index parameter)
///     rec a.A         (recursive type)
///     exists (X,Y,...):g | P . A
///                     (existential index variables, with common sort g)
///     A B ...         (extended application of type constructor to type)
///     a               (type var)
/// ```
#[macro_export]
macro_rules! fgi_vtype {
    //     fromast ast     (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     (A)             (parens)
    { ($($type:tt)+) } => { fgi_vtype![$($type)+] };
    //     D,Seq,Nat       (type constructors)
    { D } => { Type::Cons(TypeCons::D) };
    { Bool } => { Type::Cons(TypeCons::Bool) };
    { Nat } => { Type::Cons(TypeCons::Nat) };
    { String } => { Type::Cons(TypeCons::String) };
    { Seq } => { Type::Cons(TypeCons::Seq) };
    //     user(type)      (user-defined)
    { user($s:ident) } => { Type::Cons(TypeCons::User(
        stringify![$s].to_string()
    ))};
    //     Unit            (unit)
    { Unit } => { Type::Unit };
    //     + A + B ...     (extended sums)
    { + $($sum:tt)+ } => { split_plus![parse_fgi_sum <= $($sum)+] };
    //     x A x B ...     (extended product)
    { x $($prod:tt)+ } => { split_cross![parse_fgi_prod <= $($prod)+] };
    //     Ref[i] A        (named ref cell)
    { Ref[$($i:tt)+] $($t:tt)+ } => { Type::Ref(
        fgi_index![$($i)+],
        Rc::new(fgi_vtype![$($t)+]),
    )};
    //     Thk[i] E        (named thunk with effects)
    { Thk[$($i:tt)+] $($e:tt)+ } => { Type::Thk(
        fgi_index![$($i)+],
        Rc::new(fgi_ceffect![$($e)+]),
    )};
    //     Nm[i]           (name type)
    { Nm[$($i:tt)+] } => { Type::Nm(fgi_index![$($i)+]) };
    //     A[i]            (single application of type to index)
    { $a:tt [$($i:tt)+] } => { Type::IdxApp(
        Rc::new(fgi_vtype![$a]),
        fgi_index![$($i)+],
    )};
    //     A[i] ...        (extended application of type to index)
    { $a:tt [$($i:tt)+] $($more:tt)+ } => {
        fgi_vtype![(fromast Type::IdxApp(
            Rc::new(fgi_vtype![$a]),
            fgi_index![$($i)+],
        )) $($more)+]
    };
    //     (Nm->Nm)[M]     (name function type)
    { (Nm->Nm)[$($m:tt)+] } => { Type::NmFn(fgi_nametm![$($m)+]) };
    //     forallt x:K.A   (type parameter)
    { forallt $x:ident : $k:tt. $($a:tt)+ } => {Type::TypeFn(
        stringify![$x].to_string(),
        fgi_kind![$k],
        Rc::new(fgi_vtype![$($a)+]),
    )};
    //     forallt (x):K.A   (type parameter - multivar base case)
    { forallt ($x:ident) : $k:tt. $($a:tt)+ } => {
        fgi_vtype![forallt $x : $k . $($a)+]
    };
    //     forallt (x,y,...):K.A   (type parameter - multivar)
    { forallt ($x:ident,$($xs:ident),+):$k:tt.$($a:tt)+ } => { Type::TypeFn(
        stringify![$x].to_string(),
        fgi_kind![$k],
        Rc::new(fgi_vtype![forallt ($($xs),+):$k.$($a)+])
    )};
    //     foralli x:g.A   (index parameter)
    { foralli $x:ident : $g:tt. $($a:tt)+ } => {Type::IdxFn(
        stringify![$x].to_string(),
        fgi_sort![$g],
        Rc::new(fgi_vtype![$($a)+]),
    )};
    //     foralli (x):g.A   (index parameter - multivar base case)
    { foralli ($x:ident) : $g:tt. $($a:tt)+ } => {
        fgi_vtype![foralli $x : $g . $($a)+]
    };
    //     foralli (x,y,...):g.A   (index parameter - multivar)
    { foralli ($x:ident,$($xs:ident),+):$g:tt.$($a:tt)+ } => { Type::IdxFn(
        stringify![$x].to_string(),
        fgi_sort![$g],
        Rc::new(fgi_vtype![foralli ($($xs),+):$g.$($a)+])
    )};
    //     rec a.A            (recursive type)
    { rec $a:ident.$($body:tt)+ } => { Type::Rec(
        stringify![$a].to_string(),
        Rc::new(fgi_vtype![$($body)+]),
    )};
    //    exists X : g . B  (existential - true prop)
    { exists $var:ident : $a:tt . $($b:tt)+ } => {
        fgi_vtype![exists $var : $a | tt . $($b)+]
    };
    //    exists (X) : g . B  (existential - true prop, base multi vars)
    { exists ($var:ident) : $a:tt . $($b:tt)+ } => {
        fgi_vtype![exists $var : $a | tt . $($b)+]
    };
    //    exists X : g | P . B  (existential)
    { exists $var:ident : $a:tt | $p:tt . $($b:tt)+ } => { Type::Exists(
        stringify![$var].to_string(),
        Rc::new(fgi_sort![$a]),
        fgi_prop![$p],
        Rc::new(fgi_vtype![$($b)+]),
    )};
    //    exists (X) : g | P . B  (existential - base case multi vars)
    { exists ($var:ident) : $a:tt | $p:tt . $($b:tt)+ } => {
        fgi_vtype![exists $var : $a | $p . $($b)+]
    };
    //    exists (X,Y,...) : g . B  (extended existential, true prop)
    { exists ($($vars:ident),+) : $a:tt . $($b:tt)+ } => {
        fgi_vtype![exists ($($vars),+) : $a | tt . $($b)+]
    };
    //    exists (X,Y,...) : g | P . B  (extended existential)
    { exists ($var:ident,$($vars:ident),+) : $a:tt | $p:tt . $($b:tt)+ } => {
        Type::Exists(
            stringify![$var].to_string(),
            Rc::new(fgi_sort![$a]),
            Prop::Tt,
            Rc::new(fgi_vtype![exists ($($vars),+):$a|$p.$($b)+])
        )
    };
    //     (A) B           (single application of type constructor to type)
    { $a:tt $b:tt } => { Type::TypeApp(
        Rc::new(fgi_vtype![$a]),
        Rc::new(fgi_vtype![$b]),
    )};
    //     (A) B ...       (extended application of type constructor to type)
    { $a:tt $b:tt $($more:tt)+ } => {
        fgi_vtype![(fromast Type::TypeApp(
            Rc::new(fgi_vtype![$a]),
            Rc::new(fgi_vtype![$b]),
        )) $($more)+]
    };
    //     a               (type var)
    { $a:ident } => { Type::Var(stringify![$a].to_string()) };
    // failure
    { $($any:tt)* } => { Type::NoParse(stringify![$($any)*].to_string())};
}
/// this macro is a helper for fgi_vtype, not for external use
#[macro_export]
macro_rules! parse_fgi_sum {
    // A + B
    { ($($a:tt)+)($($b:tt)+) } => { Type::Sum(
        Rc::new(fgi_vtype![$($a)+]),
        Rc::new(fgi_vtype![$($b)+]),
    )};
    // A + ...
    { ($($a:tt)+)$($more:tt)+ } => { Type::Sum(
        Rc::new(fgi_vtype![$($a)+]),
        Rc::new(parse_fgi_sum![$($more)+]),
    )};
    // failure
    { $($any:tt)* } => { Type::NoParse(stringify![(+ $($any)*)].to_string())};
}
/// this macro is a helper for fgi_vtype, not for external use
#[macro_export]
macro_rules! parse_fgi_prod {
    // A x B
    { ($($a:tt)+)($($b:tt)+) } => { Type::Prod(
        Rc::new(fgi_vtype![$($a)+]),
        Rc::new(fgi_vtype![$($b)+]),
    )};
    // A x ...
    { ($($a:tt)+)$($more:tt)+ } => { Type::Prod(
        Rc::new(fgi_vtype![$($a)+]),
        Rc::new(parse_fgi_prod![$($more)+]),
    )};
    // failure
    { $($any:tt)* } => { Type::NoParse(stringify![(x $($any)*)].to_string())};
}
/// Computation types
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum CType {
    Lift(Type),
    Arrow(Type,CEffectRec),
    NoParse(String),
}

/// Parser for computation types
///
/// ```text
/// C,D ::=
///     fromast ast     (inject ast nodes)
///     (C)             (parens)
///     F A             (lifted types)
///     A -> E          (functions with effects)
/// ```
#[macro_export]
macro_rules! fgi_ctype {
    //     fromast ast     (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     (C)             (parens)
    { ($($c:tt)+) } => { fgi_ctype![$($c)+] };
    //     F A             (lifted types)
    { F $($a:tt)+ } => { CType::Lift(fgi_vtype![$($a)+]) };
    //     A -> E   (extended functions with effects)
    { $($arrow:tt)+ } => { split_arrow![parse_fgi_arrow <= $($arrow)+] };
    // failure
    { $($any:tt)* } => { CType::NoParse(stringify![$($any)*].to_string())};
}
/// this macro is a helper for fgi_ctype, not for external use
#[macro_export]
macro_rules! parse_fgi_arrow {
    // A -> E ...
    { ($($a:tt)+)($($e:tt)+)$($more:tt)* } => { CType::Arrow(
        fgi_vtype![$($a)+],
        Rc::new(parse_fgi_earrow![($($e)+)$($more)*]),
    )};
    // failure
    { $($any:tt)* } => { CType::NoParse(stringify![(-> $($any)*)].to_string())};
}

/// Computation effects
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum CEffect {
    Cons(CType,Effect),
    ForallType(Var,Kind,CEffectRec),
    ForallIdx(Var,Sort,Prop,CEffectRec),
    NoParse(String),
}
pub type CEffectRec = Rc<CEffect>;


/// Parser for Computations with effects
///
/// ```text
/// E ::=
///     fromast ast                 (inject ast nodes)
///     (E)                         (parens)
///     forallt (a,...):K.E         (extended type polymorphism)
///     foralli (a,...):g|P.E       (index polymorphism)
///     foralli (a,...):g.E         (index polymorphism -- true prop)
///     ε C                         (computation with effect)
/// ```
#[macro_export]
macro_rules! fgi_ceffect {
    //     fromast ast (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     (E)         (parens)
    { ($($e:tt)+) } => { fgi_ceffect![$($e)+] };
    //     forallt (a):K.E      (type polymorphism, base case multi vars)
    { forallt ($a:ident):$k:tt.$($e:tt)+ } => {
        fgi_ceffect![forallt $a:$k.$($e)+]
    };
    //     forallt a:K.E      (type polymorphism)
    { forallt $a:ident:$k:tt.$($e:tt)+ } => { CEffect::ForallType(
        stringify![$a].to_string(),
        fgi_kind![$k],
        Rc::new(fgi_ceffect![$($e)+]),
    )};
    //     forallt (a,...):K.E      (type polymorphism, multi vars)
    { forallt ($a:ident,$($vars:ident),+):$k:tt.$($e:tt)+ } => {
        CEffect::ForallType(
            stringify![$a].to_string(),
            fgi_kind![$k],
            Rc::new(fgi_ceffect![forallt ($($vars),+):$k.$($e)+]),
        )
    };
    //     foralli (a):g|P.E    (index polymorphism, base case multi vars)
    { foralli ($a:ident):$g:tt|$p:tt.$($e:tt)+ } => {
        fgi_ceffect![foralli $a:$g|$p.$($e)+]
    };
    //     foralli a:g|P.E    (index polymorphism)
    { foralli $a:ident:$g:tt|$p:tt.$($e:tt)+ } => { CEffect::ForallIdx(
        stringify![$a].to_string(),
        fgi_sort![$g],
        fgi_prop![$p],
        Rc::new(fgi_ceffect![$($e)+]),
    )};
    //     foralli (a,...):g|P.E    (index polymorphism, multi vars)
    { foralli ($a:ident,$($vars:ident),+):$g:tt|$p:tt.$($e:tt)+ } => {
        CEffect::ForallIdx(
            stringify![$a].to_string(),
            fgi_sort![$g],
            Prop::Tt,
            Rc::new(fgi_ceffect![foralli ($($vars),+):$g|$p.$($e)+]),
        )
    };
    //     foralli a:g.E    (index polymorphism, with trivial prop)
    { foralli $a:ident:$g:tt.$($e:tt)+ } => {
        fgi_ceffect![foralli $a:$g|tt.$($e)+]
    };
    //     foralli (a):g.E  (index polymorphism, multi var base case, tt prop)
    { foralli ($a:ident):$g:tt.$($e:tt)+ } => {
        fgi_ceffect![foralli $a:$g|tt.$($e)+]
    };
    //     foralli (a,...):g.E    (index polymorphism, multi vars, tt prop)
    { foralli ($a:ident,$($vars:ident),+):$g:tt.$($e:tt)+ } => {
        fgi_ceffect![foralli ($a,$($vars),+):$g|tt.$($e)+]
    };
    //     ε C -> ε C ... (computations with effects and arrows)
    { $($arr:tt)+ } => { split_arrow![parse_fgi_earrow <= $($arr)+] };
    // failure
    { $($any:tt)* } => { CEffect::NoParse(stringify![$($any)*].to_string())};
}

/// this macro is a helper for fgi_ceffect, not for external use
#[macro_export]
macro_rules! parse_fgi_earrow {
    // ε C
    { ($e:tt $($c:tt)+) } => { CEffect::Cons(
        fgi_ctype![$($c)+],
        fgi_effect![$e],
    )};
    // ε A -> ε C
    { ($e:tt $($a:tt)+)($($c:tt)+) $($more:tt)* } => { CEffect::Cons(
        parse_fgi_arrow![($($a)+)($($c)+) $($more)*],
        fgi_effect![$e],
    )};
    // failure
    { $($any:tt)* } => { CEffect::NoParse(stringify![(-> $($any)*)].to_string())};
}

/// Value terms
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Val {
    Var(Var),
    Unit,
    Pair(ValRec, ValRec),
    Inj1(ValRec),
    Inj2(ValRec),
    Roll(ValRec),
    Name(Name),
    NameFn(NameTm),
    Anno(ValRec,Type),
    Pack(Var, ValRec),
    
    // Anonymous thunks: "ordinary" CBPV thunks. They can be written
    // in the source program, and unlike named (store-allocated)
    // thunks, and closed, run-time thunks, these thunks exist in the
    // pre-evaluation AST (not the store); also, they don't yet have a
    // run-time environment.
    ThunkAnon(ExpRec),

    /// Primitive (Rust) `bool`, injected into `Val` type
    Bool(bool),
    /// Primitive (Rust) `usize`, injected into `Val` type
    Nat(usize),
    /// Primitive (Rust) `String`, injected into `Val` type
    Str(String),

    // Parse errors
    NoParse(String),
}
pub type ValRec = Rc<Val>;

/// Parser for values
///
/// ```text
/// v::=
///     fromast ast (inject ast nodes)
///     thunk e     (anonymous thunk)
///     v : A       (annotation)
///     (v1,v2,...) (unit,parens,tuples)
///     inj1 v      (first sum value)
///     inj2 v      (second sum value)
///     roll v      (roll an unrolled recursively-typed value)
///     pack (a1,...) v  (pack existential index term variables)
///     name n      (name value)
///     nmfn M      (name function as value)
///     true,false  (bool primitive)
///     @@str       (name primitive(symbol))
///     @1235       (name primitive(number))
///     str(string) (string primitive)
///     x           (variable)
///     1234        (nat primitive)
/// ```
#[macro_export]
macro_rules! fgi_val {
    //     fromast ast (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     v : A       (annotation)
    { $v:tt : $($a:tt)+} => { Val::Anno(
        Rc::new(fgi_val![$v]),
        fgi_vtype![$($a)+],
    )};
    //     thunk e
    { thunk $($e:tt)+ } => { Val::ThunkAnon(Rc::new(fgi_exp![$($e)+])) };
    //     (v1,v2,...) (unit,parens,tuples)
    { ($($tup:tt)*) } => { split_comma![parse_fgi_tuple <= $($tup)*] };
    //     inj1 v      (first sum value)
    { inj1 $($v:tt)+ } => { Val::Inj1(Rc::new(fgi_val![$($v)+])) };
    //     inj2 v      (second sum value)
    { inj2 $($v:tt)+ } => { Val::Inj2(Rc::new(fgi_val![$($v)+])) };
    //     roll v 
    { roll $($v:tt)+ } => { Val::Roll(Rc::new(fgi_val![$($v)+])) };
    //     pack (a1,...) v    (pack an existential index term variable)
    { pack ($a:ident,$($as:ident),+) $($v:tt)+ } => { Val::Pack(
        stringify![$a].to_string(),
        Rc::new(fgi_val![pack ($($as),+) $($v)+]),
    )};
    //     pack (a) v    (pack - base case)
    { pack ($a:ident) $($v:tt)+ } => { fgi_val![pack $a $($v)+] };
    //     pack a v    (pack - single case)
    { pack $a:ident $($v:tt)+ } => { Val::Pack(
        stringify![$a].to_string(),
        Rc::new(fgi_val![$($v)+]),
    )};
    //     name n      (name value)
    { name $($n:tt)+ } => { Val::Name(fgi_name![$($n)+]) };
    //     nmfn M      (name function as value)
    { nmfn $($m:tt)+ } => { Val::NameFn(fgi_nametm![$($m)+]) };
    //     true        (bool primitive)
    { true } => { Val::Bool(true) };
    //     false        (bool primitive)
    { false } => { Val::Bool(false) };
    //     @@str       (name primitive(symbol))
    { @@$($s:tt)+ } => { Val::Name(Name::Sym(stringify![$($s)+].to_string())) };
    //     @1235       (name primitive(number))
    { @$n:expr } => { Val::Name(Name::Num($n)) };
    //     str(string) (string primitive)
    { str($($s:tt)*) } => { Val::Str(stringify![$($s)*].to_string()) };
    //     x           (variable)
    { $x:ident } => { Val::Var(stringify![$x].to_string()) };
    //     1234        (nat primitive)
    { $n:expr } => { Val::Nat($n) };
    // failure
    { $($any:tt)* } => { Val::NoParse(stringify![$($any)*].to_string())};
}
/// this macro is a helper for fgi_ceffect, not for external use
#[macro_export]
macro_rules! parse_fgi_tuple {
    // unit
    { } => { Val::Unit };
    // parens, final tuple val
    { ($($v:tt)+) } => { fgi_val![$($v)+] };
    // tuple
    { ($($v:tt)+) $($more:tt)+ } => { Val::Pair(
        Rc::new(fgi_val![$($v)+]),
        Rc::new(parse_fgi_tuple![$($more)+]),
    )};
    // failure
    { $($any:tt)* } => { Val::NoParse(stringify![(, $($any)*)].to_string())};
}

// Host-language evaluation function, for use as a trapdoor for many
// different primitives in Fungi's standard library.
#[derive(Clone)]
pub struct HostEvalFn {
    pub arity:usize,
    pub eval:Rc<Fn(Vec<eval::ast_dynamic::RtVal>) -> eval::ast_dynamic::ExpTerm>
}
impl Hash for HostEvalFn {
    fn hash<H:Hasher>(&self, hasher: &mut H) {
        panic!("XXX")
    }
}
impl Debug for HostEvalFn {
    fn fmt(&self, f:&mut Formatter) -> fmt::Result {
        write!(f, "HostEvalFn")
    }
}
impl PartialEq for HostEvalFn {
    fn eq(&self, other:&Self) -> bool {
        panic!("XXX")        
    }
}
impl Eq for HostEvalFn { }

/// Expressions (aka, computation terms)
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum PrimApp {
    // Binary combination of two names; produces a name.
    NameBin(Val,Val),

    // Force a value-producing thunk into a ref cell that holds this
    // produced value. (This operation forces the thunk).
    //
    // In detail: A practical variation of force, for when the forced
    // computation produces a value, and in particular, a data
    // structure (e.g., not an arrow); this primitive returns that
    // produced value, along with a reference cell that holds it;
    // behind the scenes, this reference cell is really just a pointer
    // to the forced thunk's cached value.
    //
    // Note: the only sound way to coerce a thunk into a reference
    // cell is to _force_ that thunk, and determine what value it
    // produces --- otherwise, the ref cell is not an "eager" data
    // value that can be inspected without forcing arbitrary effects,
    // but rather, a suspended computation, like the thunk, with such
    // effects.  Hence the value-computation duality of CBPV.
    RefThunk(Val),
    
    // Natural number equality test; produces a boolean
    NatEq(Val,Val),
    // Natural number less-than test; produces a boolean
    NatLt(Val,Val),
    // Natural number less-than-or-equal test; produces a boolean
    NatLte(Val,Val),
    // Natural number addition; produces a natural number
    NatPlus(Val,Val),

}

/// Expressions (aka, computation terms)
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Exp {
    AnnoE(ExpRec,CEffect),
    AnnoC(ExpRec,CType),
    Force(Val),
    Thunk(Val,ExpRec),
    Unroll(Val,Var,ExpRec),
    // unpack (a)x = (v) e
    Unpack(Var,Var,Val,ExpRec),
    Fix(Var,ExpRec),
    Ret(Val),
    DefType(Var,Type,ExpRec),
    Let(Var,ExpRec,ExpRec),
    Lam(Var, ExpRec),
    // Host language (Rust) function. Use cautiously.
    //
    // Generally unsafe, since this term checks against all
    // computation types of the correct arity.  Fungi does not check
    // the host language function; it trusts the programmer's
    // annotation to check the remainder of the Fungi program.  This
    // term does not synthesize a type; it only checks against a type
    // annotation, which is generally required.
    HostFn(HostEvalFn),
    App(ExpRec, Val),
    Split(Val, Var, Var, ExpRec),
    Case(Val, Var, ExpRec, Var, ExpRec),
    IfThenElse(Val, ExpRec, ExpRec),
    Ref(Val,Val),
    Get(Val),
    Scope(Val,ExpRec),
    NameFnApp(Val,Val),
    PrimApp(PrimApp),
    Unimp,
    DebugLabel(Option<Name>,Option<String>,ExpRec),
    NoParse(String),
}
pub type ExpRec = Rc<Exp>;

/// Parser for expressions
///
/// ```text
/// e::=
///     fromast ast                     (inject ast nodes)
///     unsafe (arity) rustfn           (inject an evaluation function written in Rust)
///     e : C                           (type annotation, no effect)
///     e :> E                          (type annotation, with effect)
///     {e}                             (parens)
///     scope v e                       (memo scope)
///     ret v                           (lifted value)
///     #x.e                            (lambda)
///     fix x.e                         (recursive lambda)
///     unroll v x.e                    (unroll recursively-typed value v as x in e)
///     unroll match v { ... }          (unroll recursively-typed value and elim sum type)
///     unpack (a1,...) x = (v) e       (unpack existentials from type, bind x to v)
///     {e} {!ref} ...                  (application get-sugar)
///     {e} v1 ...                      (extened application)
///     type t = (A) e                  (user type shorthand, recursive type)
///     let x = {e1} e2                 (let-binding)
///     let x : A = {e1} e2             (annotated let-binding)
///     let rec x : A = {e1} e2         (annotated let-rec binding)
///     thk v e                         (create thunk)
///     ref v1 v2                       (create ref)
///     force v                         (force thunk)
///     refthunk v                      (coerce a value-producing thunk to a ref)
///     get v                           (read from ref)
///     let (x1,...) = {e1} e2          (let-split sugar)
///     let (x1,...) = v e              (extended split)
///     memo{e1}{e2}                    (memoize computation, sugar - compute name)
///     memo(v){e}                      (memoize computation by name, return ref)
///     match v {x1 => e1 ... }         (extended case analysis)
///     if { e } { e1 } else { e2 }     (if-then-else; bool elim)
///     if ( v ) { e1 } else { e2 }     (if-then-else; bool elim)
///     [v1] v2 ...                     (curried name function application)
///     v1, v2, ...                     (extended binary name construction)
///     v1 < v2                         (less-than)
///     unimplemented                   (marker for type checker)
///     label (some text) e             (debug string label)
///     label [n] e                     (debug name label)
///     label (some text)[n] e          (debug string and name label)
///     label [n](some text) e          (debug string and name label)
/// ```
#[macro_export]
macro_rules! fgi_exp {
    //     fromast ast                     (inject ast nodes)
    { fromast $ast:expr } => { $ast };
    //     unsafe (arity) rustfn           (inject an evaluation function written in Rust)
    { unsafe ($arity:expr) $rustfn:expr } => {
        Exp::HostFn(HostEvalFn{
            arity:$arity,
            eval:Rc::new($ast),
        })
    };
    //     e : C                           (type annotation, without effects)
    { $e:tt : $($c:tt)+ } => { Exp::AnnoC(
        Rc::new(fgi_exp![$e]),
        fgi_ctype![$($c)+],
    )};
    //     e :> E                          (type annotation, with effects)
    { $e:tt : $($c:tt)+ } => { Exp::AnnoE(
        Rc::new(fgi_exp![$e]),
        fgi_ceffect![$($c)+],
    )};
    //     {e}                             (parens)
    { {$($e:tt)+} } => { fgi_exp![$($e)+] };
    //     scope v e                       (memo scope)
    { scope $v:tt $($e:tt)+ } => { Exp::Scope(
        fgi_val![$v],
        Rc::new(fgi_exp![$($e)+]),
    )};
    //     ret v                           (lifted value)
    { ret $($v:tt)+ } => { Exp::Ret(fgi_val![$($v)+]) };
    //     #x.e                            (lambda)
    { #$x:ident.$($e:tt)+ } => { Exp::Lam(
        stringify![$x].to_string(),
        Rc::new(fgi_exp![$($e)+]),
    )};
    //     fix x.e                         (recursive lambda)
    { fix $x:ident.$($e:tt)+ } => { Exp::Fix(
        stringify![$x].to_string(),
        Rc::new(fgi_exp![$($e)+]),
    )};
    // Sugar:
    //    unroll match v { ... }  ==> unroll v y. match y { ... }
    //
    { unroll match $v:tt $($more:tt)+ } => {
        Exp::Unroll(fgi_val![$v],
                    "sugar_match_unroll".to_string(),
                    Rc::new(fgi_exp![
                        match sugar_match_unroll $($more)+
                    ]))
    };
    //     unroll v x.e
    { unroll $v:tt $x:ident.$($e:tt)+ } => {
        Exp::Unroll(
            fgi_val![$v],
            stringify![$x].to_string(),
            Rc::new(fgi_exp![$($e)+]))
    };
    //     unpack (a1,...) x = (v) e       (unpack existentials from type, bind x to v)
    { unpack ($idx:ident,$($idxs:ident),+) $var:ident = $val:tt $($exp:tt)+ } => {
        Exp::Unpack(
            stringify![$idx].to_string(),
            "sugar_unpack_multi".to_string(),
            fgi_val![$val],
            Rc::new(fgi_exp![unpack ($($idxs),+) $var = sugar_unpack_multi
                             $($exp)+]),
        )
    };
    //     unpack (a) x = (v) e            (unpack - single case)
    { unpack ($idx:ident) $var:ident = $val:tt $($exp:tt)+ } => {
        Exp::Unpack(
            stringify![$idx].to_string(),
            stringify![$var].to_string(),
            fgi_val![$val],
            Rc::new(fgi_exp![$($exp)+]),
        )
    };
    //     unpack (a1,...) x = {e1} e2     (unpack - expression)
    { unpack $idxs:tt $var:ident = {$($e1:tt)+} $($e2:tt)+ } => {
        fgi_exp![
            let sugar_unpack_exp = {$($e1)+}
            unpack $idxs $var = (sugar_unpack_exp)
            $($e2)+
        ]
    };
    //     {e} {!ref} ...                     (application get-sugar)
    { {$($e:tt)+} {!$ref:ident} $($more:tt)* } => {
        // we need to create a new variable name for each
        // forced ref in the application
        // this will force a ref each time it appears in the
        // argument list
        fgi_exp![{fromast Exp::Let(
            format!("{}{}",
                stringify![app_get_sugar_],
                stringify![$ref],
            ),
            Rc::new(Exp::Get(Val::Var(stringify![$ref].to_string()))),
            Rc::new(Exp::App(
                Rc::new(fgi_exp![$($e)+]),
                Val::Var(format!("{}{}",
                    stringify![app_get_sugar_],
                    stringify![$ref],
                )),
            )),
        )} $($more)*]
    };
    //     {e} v                             (single application)
    { {$($e:tt)+} $v:tt } => { Exp::App(
        Rc::new(fgi_exp![$($e)+]),
        fgi_val![$v],
    )};
    //     {e} v1 ...                        (extened application)
    { {$($e:tt)+} $v:tt $($more:tt)+ } => {
        fgi_exp![{fromast Exp::App(
            Rc::new(fgi_exp![$($e)+]),
            fgi_val![$v],
        )} $($more)+]
    };
    //     type t = (A) e                    (user type definition)
    { type $t:ident = $a:tt $($e:tt)+ }=>{Exp::DefType(
        stringify![$t].to_string(),
        fgi_vtype![$a],
        Rc::new(fgi_exp![$($e)+]),
    )};
    //     let x = {e1} e2                 (let-binding)
    { let $x:ident = $e1:tt $($e2:tt)+ } => { Exp::Let(
        stringify![$x].to_string(),
        Rc::new(fgi_exp![$e1]),
        Rc::new(fgi_exp![$($e2)+]),
    )};
    //     let x : A = {e1} e2             (annotated let-binding)
    { let $x:ident : $a:tt = $e1:tt $($e2:tt)+ } => { Exp::Let(
        stringify![$x].to_string(),
        Rc::new(Exp::AnnoC(
            Rc::new(fgi_exp![$e1]),
            fgi_ctype![F $a]
        )),
        Rc::new(fgi_exp![$($e2)+]),
    )};
    //     let rec x : A = {e1} e2         (annotated let-rec binding)
    //
    //     ===>> let x : A = {ret (thunkanon (fix x. e1))} e2
    //
    { let rec $x:ident : $a:tt = $e1:tt $($e2:tt)+ } => { Exp::Let(
        stringify![$x].to_string(),
        Rc::new(Exp::AnnoC(
            Rc::new(Exp::Ret(Val::ThunkAnon(
                Rc::new(Exp::Fix(stringify![$x].to_string(),
                                 Rc::new(fgi_exp![$e1])))))
            ),
            fgi_ctype![F $a]
        )),
        Rc::new(fgi_exp![$($e2)+]),
    )};
    //     thk v e                         (create thunk)
    { thk $v:tt $($e:tt)+ } => { Exp::Thunk(
        fgi_val![$v],
        Rc::new(fgi_exp![$($e)+]),
    )};
    //     ref v1 v2                       (create ref)
    { ref $v1:tt $($v2:tt)+ } => { Exp::Ref(
        fgi_val![$v1],
        fgi_val![$($v2)+],
    )};
    //     force v                         (force thunk)
    { force $($v:tt)+ } => { Exp::Force( fgi_val![$($v)+])};
    //     refthunk v                      (coerce thunk)
    { refthunk $($v:tt)+ } => { Exp::PrimApp( PrimApp::RefThunk(fgi_val![$($v)+])) };
    //     get v                           (read from ref)
    { get $($v:tt)+ } => { Exp::Get( fgi_val![$($v)+])};
    //     let (x1,...) = {e1} e2          (let-split sugar)
    { let ($($vars:tt)+) = {$($e1:tt)+} $($e2:tt)+ } => {
        fgi_exp![
            let let_split_sugar = {$($e1)+}
            let ($($vars)+) = let_split_sugar
            $($e2)+
        ]
    };
    //     let (x1,...) = v e              (extended split)
    { let ($($vars:tt)+) = $v:tt $($e:tt)+ } => {
        split_comma![parse_fgi_split ($v {$($e)+}) <= $($vars)+]
    };
    //     match v {x1 => e1 x2 => e2 }    (pair case analysis)
    { match $v:tt {$x1:ident=>$e1:tt $x2:ident=>$e2:tt} } => { Exp::Case(
        fgi_val![$v],
        stringify![$x1].to_string(),
        Rc::new(fgi_exp![$e1]),
        stringify![$x2].to_string(),
        Rc::new(fgi_exp![$e2]),
    )};
    //     match v {x1 => e1 ... }         (extended case analysis)
    { match $v:tt {$x1:ident=>$e1:tt $x2:ident=>$e2:tt $($more:tt)+} } => {
        Exp::Case(
            fgi_val![$v],
            stringify![$x1].to_string(),
            Rc::new(fgi_exp![$e1]),
            "sugar_match_snd".to_string(),
            Rc::new(fgi_exp![
                match sugar_match_snd {
                    $x2=>$e2 $($more)+
                }
            ]),
        )
    };
    //     memo{e1}{e2}                    (memoize computation, sugar - compute name)
    { memo{$($e1:tt)+}{$($e2:tt)+} } => {
        fgi_exp![
            let memo_name_sugar = {$($e1)+}
            memo(memo_name_sugar){$($e2)+}
        ]
    };
    //     memo(v){e}                      (memoize computation by name, return ref)
    { memo($($v:tt)+){$($e:tt)+} } => {
        fgi_exp![
            let memo_keyword_sugar = { thk ($($v)+) $($e)+ }
            refthunk memo_keyword_sugar
        ]
    };
    //     match v {x1 => e1 x2 => e2 }    (pair case analysis)
    { match $v:tt {$x1:ident=>$e1:tt $x2:ident=>$e2:tt} } => { Exp::Case(
        fgi_val![$v],
        stringify![$x1].to_string(),
        Rc::new(fgi_exp![$e1]),
        stringify![$x2].to_string(),
        Rc::new(fgi_exp![$e2]),
    )};
    //     if ( v ) { e1 } else { e2 }     (if-then-else; bool elim)
    { if ( $($v:tt)+ ) { $($e1:tt)+ } else { $($e2:tt)+ } } => {
        Exp::IfThenElse(
            fgi_val![$($v)+],
            Rc::new(fgi_exp![$($e1)+]),
            Rc::new(fgi_exp![$($e2)+])
        )
    };
    //     if { e } { e1 } else { e2 }     (if-then-else; bool elim)
    { if { $($e:tt)+ } { $($e1:tt)+ } else { $($e2:tt)+ } } => {
        Exp::Let("sugar_if_scrutinee".to_string(),
                 Rc::new(fgi_exp![$($e)+]),
                 Rc::new(Exp::IfThenElse(
                     Val::Var("sugar_if_scrutinee".to_string()),
                     Rc::new(fgi_exp![$($e1)+]),
                     Rc::new(fgi_exp![$($e2)+])
                 )))
    };
    //     [v1] v2                         (single name function application)
    { [$($v1:tt)+] $v2:tt } => { Exp::NameFnApp(
        fgi_val![$($v1)+],
        fgi_val![$v2],
    )};
    //     [v1] v2 ...                     (extended name function application)
    { [$($v1:tt)+] $v2:tt $($more:tt)+ } => {
        fgi_exp![
            let sugar_nmfn_exp = {[$($v1)+] $v2}
            [sugar_nmfn_exp] $($more)+
        ]
    };
    //     v1, v2                          (single binary name construction)
    { $v1:tt, $v2:tt } => {
        Exp::PrimApp(PrimApp::NameBin( fgi_val!($v1),
                                       fgi_val!($v2) ))
    };
    //     v1, v2, ...                     (extended binary name construction)
    { $v1:tt, $($more:tt)+ } => {
        fgi_exp![
            let sugar_name_pair = {fromast fgi_exp![$($more)+]}
            ret $v1, sugar_name_pair
        ]
    };
    //     v1 < v2                         (less-than)
    { $v1:tt < $v2:tt } => { Exp::PrimApp(PrimApp::NatLt(
        fgi_val![$v1],
        fgi_val![$v2],
    ))};
    //     v1 = v2                         
    { $v1:tt == $v2:tt } => { Exp::PrimApp(PrimApp::NatEq(
        fgi_val![$v1],
        fgi_val![$v2],
    ))};
    //     v1 <= v2                         
    { $v1:tt <= $v2:tt } => { Exp::PrimApp(PrimApp::NatLeq(
        fgi_val![$v1],
        fgi_val![$v2],
    ))};
    //     v1 + v2                         
    { $v1:tt + $v2:tt } => { Exp::PrimApp(PrimApp::NatPlus(
        fgi_val![$v1],
        fgi_val![$v2],
    ))};
    //     unimplemented                   (marker for type checker)
    { unimplemented } => { Exp::Unimp };
    //     label [n](some text) e                    (debug name label)
    { label [$($n:tt)+]($($s:tt)+) $($e:tt)+ } => { Exp::DebugLabel(
        Some(fgi_name![$($n)+]),
        Some(stringify![$($s)+].to_string()),
        Rc::new(fgi_exp![$($e)+]),
    )};
    //     label (some text)[n] e                    (debug name label)
    { label ($($s:tt)+)[$($n:tt)+] $($e:tt)+ } => { Exp::DebugLabel(
        Some(fgi_name![$($n)+]),
        Some(stringify![$($s)+].to_string()),
        Rc::new(fgi_exp![$($e)+]),
    )};
    //     label (some text) e             (debug string label)
    { label ($($s:tt)+) $($e:tt)+ } => { Exp::DebugLabel(
        None,
        Some(stringify![$($s)+].to_string()),
        Rc::new(fgi_exp![$($e)+]),
    )};
    //     label [n] e                    (debug name label)
    { label [$($n:tt)+] $($e:tt)+ } => { Exp::DebugLabel(
        Some(fgi_name![$($n)+]),
        None,
        Rc::new(fgi_exp![$($e)+]),
    )};
    // failure
    { $($any:tt)* } => { Exp::NoParse(stringify![$($any)*].to_string())};
}
/// this macro is a helper for fgi_exp, not for external use
#[macro_export]
macro_rules! parse_fgi_split {
    // v e (x1,x2)
    { $v:tt $e:tt ($x1:ident)($x2:ident) } => { Exp::Split(
        fgi_val![$v],
        stringify![$x1].to_string(),
        stringify![$x2].to_string(),
        Rc::new(fgi_exp![$e]),
    )};
    // v e (x1,x2,...)
    { $v:tt $e:tt ($x1:ident)($x2:ident) $($more:tt)+ } => {
        Exp::Split(
            fgi_val![$v],
            stringify![$x1].to_string(),
            "sugar_split_snd".to_string(),
            Rc::new(parse_fgi_split![sugar_split_snd $e ($x2) $($more)+]),
        )
    };
    // failure
    { $($any:tt)* } => { Exp::NoParse(stringify![(, $($any)*)].to_string())};
}


/// Each module consists of a declaration list body
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Module {
    pub body:  String,
    pub decls: Decls,
}

/// Declare the Fungi module for current host (Rust) module.
///
/// ```text
/// module ::= d
/// ```
///
#[macro_export]
macro_rules! fgi_mod {
    { $($decls:tt)+ } => {    
        pub fn fgi_module () -> Module {
            fgi_module![ $($decls)+ ]
        }
    };
}

/// Declare an inner, named Fungi module, using an inner host (Rust) module.
///
/// ```text
/// module ::= d
/// ```
///
#[macro_export]
macro_rules! fgi_inner_mod {
    { ( $name:ident ) $($decls:tt)+ } => {    
        mod $name {
            use std::rc::Rc;
            use ast::*;
            pub fn fgi_module () -> Module {
                fgi_module![ $($decls)+ ]
            }
        }
    };
}


/// Parser for modules, whose bodies consist of a declaration list.
///
/// ```text
/// module ::= d
/// ```
///
#[macro_export]
macro_rules! fgi_module {
    { $($decls:tt)+ } => {
        Module {
            body:  stringify![ $($decls)+].to_string(),
            decls: fgi_decls![ $($decls)+ ],
        }
    }
}

/// Declaration lists; the body of each module
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Decls {
    UseAll(UseAllModule,   DeclsRec),
    TypeAlias(String,Type, DeclsRec),
    Val(String,Type,Val,   DeclsRec),
    Fn(String,CEffect,Exp, DeclsRec),
    End,
    NoParse(String),
}
pub type DeclsRec = Rc<Decls>;

/// Declaration that uses (imports) all decls from another module
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct UseAllModule {
    pub path: String,
    pub module: Rc<Module>
}

/// Parser for declaration lists
///
/// ```text
/// d ::=
///     fromast ast                (inject ast nodes)
///     use ( hostpath ) :: * ; d  (all module items from path are put into local scope)
///     type t = ( A ) d           (in local scope, define a type alias `t` for value type `A`)
///     val x : ( A ) = ( v ) d    (in local scope, define a value v, of type A, bound to x)
///     fn f : ( E ) = { e } d     (in local scope, define a function f, of thunk type A, with recursive body e)
///     fn f : ( E ) { e } d       (alternate syntax: equal sign is optional)
///     ; d                        (alternate syntax: optional semi colons can go between decls)
/// ```
///
#[macro_export]
macro_rules! fgi_decls {
    { fromast $ast:expr } => {
        unimplemented!()
    };
    { use $path:ident :: * ; $($d:tt)* } => {
        // path is a Rust path (for now, just an identifier), from
        // which we project and run a public function called
        // `fgi_module`, that accepts no arguments and which produces
        // a Module.  We also save the given path, as a string.
        Decls::UseAll(
            UseAllModule{
                module:Rc::New( $path::fgi_module () ),
                path:stringify![$path].to_string(),
            },
            fgi_decls![ $($d)* ]
        )
    };
    { use ( $path:ident ) :: * ; $($d:tt)* } => {
        Decls::UseAll(
            UseAllModule{
                module:Rc::new( $path::fgi_module () ),
                path:stringify![$path].to_string(),
            },
            Rc::new(fgi_decls![ $($d)* ])
        )
    };
    { type $t:ident = ( $($a:tt)+ ) $($d:tt)* } => {
        Decls::TypeAlias( stringify![$t].to_string(),
                          fgi_vtype![ $($a)+ ],
                          Rc::new( fgi_decls![ $($d)* ] ) )
    };
    { val $x:ident : ( $($a:tt)+ ) = ( $($v:tt)+ ) $($d:tt)* } => {
        Decls::Val( stringify![$x].to_string(),
                    fgi_vtype![ $($a)+ ],
                    fgi_val![ $($v)+ ],
                    Rc::new( fgi_decls![ $($d)* ] ) )
    };
    { fn $f:ident : ( $($ceffect:tt)+ )   { $($e:tt)+ } $($d:tt)* } => {
        // parse with implied `=` sign
        fgi_decls![ $f : ( $($ceffect)+ ) = { $($e)+ } $($d)* ]
    };
    { fn $f:ident : ( $($ceffect:tt)+ ) = { $($e:tt)+ } $($d:tt)* } => {
        Decls::Fn( stringify![$f].to_string(),
                   fgi_ceffect![ $($ceffect)+ ],
                   fgi_exp![ $($e)+ ],                   
                   Rc::new( fgi_decls![ $($d)* ] ) )
    };
    { ; $($d:tt)* } => {
        // end of list; no more declarations
        fgi_decls![ $($d)* ]
    };

    { } => {
        // end of list; no more declarations
        Decls::End
    };
    // failure
    { $($any:tt)* } => { Decls::NoParse(stringify![ $($any)* ].to_string())};
}



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
#[macro_export]
/// run a macro on a list of lists after splitting the input
macro_rules! split_semi {
    // no defaults
    {$fun:ident <= $($item:tt)*} => {
        split_semi![$fun () () () <= $($item)*]
    };
    // give initial params to the function
    {$fun:ident ($($first:tt)*) <= $($item:tt)*} => {
        split_semi![$fun ($($first)*) () () <= $($item)*]
    };
    // give inital params and initial inner items in every group
    {$fun:ident ($($first:tt)*) ($($every:tt)*) <= $($item:tt)*} => {
        split_semi![$fun ($($first)*) ($($every)*) ($($every)*) <= $($item)*]
    };
    // on non-final seperator, stash the accumulator and restart it
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)*) <= ; $($item:tt)+} => {
        split_semi![$fun ($($first)* ($($current)*)) ($($every)*) ($($every)*) <= $($item)*]
    };
    // ignore final seperator, run the function
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)+) <= ; } => {
        $fun![$($first)* ($($current)*)]
    };
    // on next item, add it to the accumulator
    {$fun:ident ($($first:tt)*) ($($every:tt)*) ($($current:tt)*) <= $next:tt $($item:tt)*} => {
        split_semi![$fun ($($first)*) ($($every)*) ($($current)* $next)  <= $($item)*]
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
