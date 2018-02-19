/*! Bidirectional type system. */

use ast::*;
use std::fmt;
use std::rc::Rc;

/// Typing context
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Ctx {
    Empty,
    /// Define a type term to be carried in the type context
    Def(CtxRec,Var,Term),
    /// Define a value variable's type
    Var(CtxRec,Var,Type),
    /// Define a name/index variable's sort
    IVar(CtxRec,Var,Sort),
    /// Define a type variable's kind
    TVar(CtxRec,Var,Kind),
    /// Assume an index term equivalence, at a common sort
    Equiv(CtxRec,IdxTm,IdxTm,Sort),
    /// Assume an index term apartness, at a common sort
    Apart(CtxRec,IdxTm,IdxTm,Sort),
    /// Assume a proposition is true
    PropTrue(CtxRec,Prop),
}
pub type CtxRec = Rc<Ctx>;

/// Type terms; each can be defined by a module declaration,
/// and carried (by identifier name) in the typing context, and used
/// (by identifier name) to construct terms used in typing
/// derivations.
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Term {
    NmTm(NameTm),
    IdxTm(IdxTm),
    Type(Type),
}

impl Ctx {
    /// define a term
    pub fn def(&self,v:Var,t:Term) -> Ctx {
        Ctx::Def(Rc::new(self.clone()),v,t)
    }
    /// bind a var and type
    pub fn var(&self,v:Var,t:Type) -> Ctx {
        Ctx::Var(Rc::new(self.clone()),v,t)
    }
    /// bind a index var and sort
    pub fn ivar(&self,v:Var,s:Sort) -> Ctx {
        Ctx::IVar(Rc::new(self.clone()),v,s)
    }
    /// bind a type var and kind
    pub fn tvar(&self,v:Var,k:Kind) -> Ctx {
        Ctx::TVar(Rc::new(self.clone()),v,k)
    }
    /// assume an index equivalence
    pub fn equiv(&self,i1:IdxTm,i2:IdxTm,s:Sort) -> Ctx {
        Ctx::Equiv(Rc::new(self.clone()),i1,i2,s)
    }
    /// assume an index apartness
    pub fn apart(&self,i1:IdxTm,i2:IdxTm,s:Sort) -> Ctx {
        Ctx::Apart(Rc::new(self.clone()),i1,i2,s)
    }
    /// assume a proposition is true
    pub fn prop(&self,p:Prop) -> Ctx {
        Ctx::PropTrue(Rc::new(self.clone()),p)
    }
    // append another context to the given one
    pub fn append(&self,other:&Ctx) -> Ctx {
        match *self {
            Ctx::Empty => other.clone(),
            Ctx::Def(ref c, ref x, ref t)  => Ctx::Def(c.append_rec(other), x.clone(), t.clone()),
            Ctx::Var(ref c, ref x, ref a)  => Ctx::Var(c.append_rec(other), x.clone(), a.clone()),
            Ctx::IVar(ref c, ref x, ref g) => Ctx::IVar(c.append_rec(other), x.clone(), g.clone()),
            Ctx::TVar(ref c, ref x, ref k) => Ctx::TVar(c.append_rec(other), x.clone(), k.clone()),
            Ctx::PropTrue(ref c, ref prop) => Ctx::PropTrue(c.append_rec(other), prop.clone()),
            Ctx::Equiv(ref c, ref i, ref j, ref g) => Ctx::Equiv(c.append_rec(other), i.clone(), j.clone(), g.clone()),
            Ctx::Apart(ref c, ref i, ref j, ref g) => Ctx::Apart(c.append_rec(other), i.clone(), j.clone(), g.clone()),
        }
    }
    pub fn append_rec(&self,other:&Ctx) -> Rc<Ctx> {
        Rc::new(self.append(other))
    }
}

impl Ctx {
    pub fn rest(&self) -> Option<CtxRec> {
        match *self {
            Ctx::Empty => None,
            Ctx::Def(ref c,_,_) |
            Ctx::Var(ref c, _, _) |
            Ctx::IVar(ref c,_,_) |
            Ctx::TVar(ref c,_,_) |
            Ctx::Equiv(ref c,_,_,_) |
            Ctx::Apart(ref c,_,_,_) |
            Ctx::PropTrue(ref c,_) => { Some(c.clone()) },
        }
    }
    pub fn lookup_var(&self, x:&Var) -> Option<Type> {
        match *self {
            Ctx::Empty => None,
            Ctx::Var(ref c,ref y,ref a) => {
                if x == y { Some(a.clone()) } else { c.lookup_var(x) }
            },
            ref c => c.rest().unwrap().lookup_var(x)
        }
    }
    pub fn lookup_ivar(&self, x:&Var) -> Option<Sort> {
        match *self {
            Ctx::Empty => None,
            Ctx::IVar(ref c,ref y,ref g) => {
                if x == y { Some(g.clone()) } else { c.lookup_ivar(x) }
            },
            ref c => c.rest().unwrap().lookup_ivar(x)
        }
    }
    pub fn lookup_tvar(&self, x:&Var) -> Option<Kind> {
        match *self {
            Ctx::Empty => None,
            Ctx::TVar(ref c,ref y,ref k) => {
                if x == y { Some(k.clone()) } else { c.lookup_tvar(x) }
            },
            ref c => c.rest().unwrap().lookup_tvar(x)
        }
    }
    pub fn lookup_type_def(&self, x:&Var) -> Option<Type> {
        match *self {
            Ctx::Empty => None,
            Ctx::Def(ref c,ref y, Term::Type(ref a)) => {
                if x == y { Some(a.clone()) } else { c.lookup_type_def(x) }
            },
            ref c => c.rest().unwrap().lookup_type_def(x)
        }        
    }    
}

pub trait HasClas {
    type Clas;
    fn tm_fam() -> String;
}

/// Typing derivation: A context (`ctx`), a direction (`dir`), a classifier (type, sort, etc) and a rule (`rule`).
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Der<Rule:HasClas> {
    pub ctx:Ctx,
    pub dir:Dir,
    pub rule:Rc<Rule>,
    pub clas:Result<Rule::Clas,TypeError>,
    pub vis:DerVis,
}
impl<Rule:HasClas> Der<Rule> {
    pub fn is_err(&self) -> bool { self.clas.is_err() }
    pub fn is_ok(&self) -> bool { self.clas.is_ok() }
}
/// Information for visualizing derivation trees in HFI
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct DerVis {
    /// Term family name, for HFI
    pub tmfam:String,
}


/// Name term sorting rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum NmTmRule {
    Var(Var),
    Name(Name),
    Bin(NmTmDer, NmTmDer),
    Lam(Var,Sort,NmTmDer),
    App(NmTmDer, NmTmDer),
    NoParse(String),
}
pub type NmTmDer = Der<NmTmRule>;
impl HasClas for NmTmRule {
    type Clas = Sort;
    fn tm_fam() -> String { "NmTm".to_string() }
}

/// Index term sorting rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum IdxTmRule {
    Var(Var),
    Sing(NmTmDer),
    Empty,
    Disj(IdxTmDer, IdxTmDer),
    Union(IdxTmDer, IdxTmDer),
    Unit,
    Pair(IdxTmDer, IdxTmDer),
    Proj1(IdxTmDer),
    Proj2(IdxTmDer),
    Lam(Var, Sort, IdxTmDer),
    App(IdxTmDer, IdxTmDer),
    Map(NmTmDer, IdxTmDer),
    FlatMap(IdxTmDer, IdxTmDer),
    Star(IdxTmDer, IdxTmDer),
    NoParse(String),
}
pub type IdxTmDer = Der<IdxTmRule>;
impl HasClas for IdxTmRule {
    type Clas = Sort;
    fn tm_fam () -> String { "IdxTm".to_string() }
}

/// Value typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ValRule {
    Var(Var),
    Unit,
    Pair(ValDer, ValDer),
    Inj1(ValDer),
    Inj2(ValDer),
    Roll(ValDer),
    Pack(Var,ValDer),
    Name(Name),
    NameFn(NmTmDer),
    Anno(ValDer,Type),
    ThunkAnon(Der<ExpRule>),
    Bool(bool),
    Nat(usize),
    Str(String),
    NoParse(String),
}
pub type ValDer = Der<ValRule>;
impl HasClas for ValRule {
    type Clas = Type;
    fn tm_fam () -> String { "Val".to_string() }
}


/// Qualifiers for module item names
///
/// Two named objects in a module can reuse the same name if they have
/// different qualifiers (e.g., name term vs index term vs type vs value).
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Qual {
    NmTm,
    IdxTm,
    Type,
    Val
}

/// Module item derivation
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct ItemDer {
    pub doc:Option<String>,
    pub qual:Qual,
    pub var:String,
    pub der:DeclDer,
}
/// Module item typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ItemRule {
    Bind(ItemDer),
    NoParse(String),
}
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
/// Module typing derivation
pub struct ModuleDer {
    /// untyped AST of the module
    pub ast: Rc<Module>,
    /// typing sub-derivations for each module item: each `ModuleVar` is unique
    pub tds: Vec<ItemRule>,
    /// the context exported by this module to modules that use it
    pub ctx_out: Ctx,
}
/// Module import typing derivation
pub struct UseAllModuleDer {
    /// untyped AST of the imported module
    pub ast: UseAllModule,
    /// typing derivation for the imported module
    pub td: ModuleDer,
}
/// Module declaration typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum DeclRule {
    UseAll(UseAllModule),
    NmTm (String, NmTmDer),
    IdxTm(String, IdxTmDer),
    // TODO: add kinds
    Type (String, Type), 
    Val  (String, ValDer),
    Fn   (String, ValDer),
}
/// Classifier for declared object in a module
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum DeclClas {
    /// Classifier `g` for name terms `N` and index terms `i`
    Sort(Sort),
    /// Classifier `K` for types `A`
    Kind(Kind),
    /// Classifier `A` for values `v`
    Type(Type),
    /// Classifier `E` for function bodies `e` (implied thunk type is `Thk[0] E`)
    CEffect(CEffect),
}
/// Module declaration typing derivation
pub type DeclDer = Der<DeclRule>;
impl HasClas for DeclRule {
    type Clas = DeclClas;
    fn tm_fam () -> String { "Decl".to_string() }
}

/// Expression typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum ExpRule {
    AnnoC(ExpDer,CType),
    AnnoE(ExpDer,CEffect),
    Force(ValDer),
    Thunk(ValDer,ExpDer),
    Unroll(ValDer,Var,ExpDer),
    Unpack(Var,Var,ValDer,ExpDer),
    Fix(Var,ExpDer),
    Ret(ValDer),
    DefType(Var,Type,ExpDer),
    Let(Var,ExpDer,ExpDer),
    Lam(Var, ExpDer),
    HostFn(HostEvalFn),
    App(ExpDer, ValDer),
    Split(ValDer, Var, Var, ExpDer),
    Case(ValDer, Var, ExpDer, Var, ExpDer),
    IfThenElse(ValDer, ExpDer, ExpDer),
    Ref(ValDer,ValDer),
    Get(ValDer),
    Scope(ValDer,ExpDer),
    NameFnApp(ValDer,ValDer),
    PrimApp(PrimAppRule),
    Unimp,
    DebugLabel(Option<Name>, Option<String>,ExpDer),
    NoParse(String),
}
pub type ExpDer = Der<ExpRule>;
impl HasClas for ExpRule {
    type Clas = CEffect;
    fn tm_fam () -> String { "Exp".to_string() }
}

/// Primitive application typing rule
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum PrimAppRule {
    NatEq(ValDer,ValDer),
    NatLt(ValDer,ValDer),
    NatLte(ValDer,ValDer),
    NatPlus(ValDer,ValDer),
    NameBin(ValDer,ValDer),
    RefThunk(ValDer),
}

/// Bidirectional direction: _Synthesis_ vs _Checking_
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum Dir { Synth, Check }
impl Dir {
    fn short(&self) -> &str {
        match *self {
            Dir::Synth => "synth",
            Dir::Check => "check",
        }
    }
}

/// Typing error
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum TypeError {
    VarNotInScope(String),
    NoParse(String),
    AnnoMism,
    NoSynthRule,
    NoCheckRule,
    InvalidPtr,
    ParamMism(usize),
    ParamNoSynth(usize),
    ParamNoCheck(usize),
    ExistVarMism,
    ProjNotProd,
    AppNotArrow,
    ValNotArrow,
    GetNotRef,
    ExpNotCons,
    BadCheck,
    DSLiteral,
    EmptyDT,
    Unimplemented,
    // More errors
    CheckFailType(Type),
    CheckFailCEffect(CEffect),
    SynthFailVal(Val),
    UnexpectedCEffect(CEffect),
    UnexpectedType(Type),
}
impl fmt::Display for TypeError {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        let s = match *self {
            TypeError::VarNotInScope(ref s) => format!("variable {} not in scope",s),
            TypeError::NoParse(ref s) => format!("term did not parse: `{}`",s),
            TypeError::AnnoMism => format!("annotation mismatch"),
            TypeError::NoSynthRule => format!("no synth rule found, try an annotation"),
            TypeError::NoCheckRule => format!("no check rule found"),
            TypeError::ExistVarMism => format!("identifiers of packed/unpacked existensial vars must match"),
            TypeError::InvalidPtr => format!("invalid pointer"),
            // 0 based parameter numbers
            TypeError::ParamMism(num) => format!("parameter {} type incorrect",num),
            TypeError::ParamNoSynth(num) => format!("parameter {} unknown type",num),
            TypeError::ParamNoCheck(num) => format!("parameter {} type mismatch ",num),
            TypeError::ProjNotProd => format!("projection of non-product type"),
            TypeError::ValNotArrow => format!("this value requires an arrow type"),
            TypeError::AppNotArrow => format!("application of non-arrow type"),
            TypeError::GetNotRef => format!("get from a non-ref val"),
            TypeError::ExpNotCons => format!("annotated a expression that was not type-and-effect"),
            TypeError::BadCheck => format!("checked type inappropriate for value"),
            TypeError::DSLiteral => format!("data structure literals not allowed"),
            TypeError::EmptyDT => format!("ambiguous empty data type"),
            TypeError::Unimplemented => format!("Internal Error: type-checking unimplemented"),
            // 
            TypeError::CheckFailType(ref t) => format!("check fail for type {:?}",t),
            TypeError::CheckFailCEffect(ref ce) => format!("check fail for ceffect {:?}",ce),
            TypeError::SynthFailVal(ref v) => format!("failed to synthesize type for value {:?}",v),
            //TypeError::TypeMismatch(ref t1, ref t2) => format!("failed to equate types {:?} (given) and {:?} (expected)", t1, t2),
            TypeError::UnexpectedCEffect(ref ce) => format!("unexpected effect type: {:?}", ce),
            TypeError::UnexpectedType(ref t) => format!("unexpected type: {:?}", t),
        };
        write!(f,"{}",s)
    }
}

fn failure<R:HasClas+debug::DerRule>
    (dir:Dir, last_label:Option<&str>,
     ctx:&Ctx, n:R, err:TypeError) -> Der<R>
{
    if let Some(lbl) = last_label {print!("After {}, ", lbl)}
    println!("Failed to {} {} {}, error: {}", dir.short(), n.short(), R::term_desc(), err);
    Der{
        ctx: ctx.clone(),
        rule: Rc::new(n),
        dir: dir,
        clas: Err(err),
        vis:DerVis{
            tmfam:R::tm_fam(),
        }
    }
}

fn success<R:HasClas+debug::DerRule>
    (dir:Dir, _last_label:Option<&str>,
     ctx:&Ctx, rule:R, clas:R::Clas) -> Der<R>
{
    Der{
        ctx: ctx.clone(),
        rule: Rc::new(rule),
        dir: dir,
        clas: Ok(clas),
        vis:DerVis{
            tmfam:R::tm_fam(),
        }
    }
}


/// Normalize types (expand definitions and reduce applications).
///
/// To normalize types, we generally need to **expand definitions** of
/// user-defined types, and **apply them** to type or index arguments.
///
/// ### Example:
///
/// Suppose the user defines `NmOp := foralli X:NmSet. 1 + Nm[X]` in
/// the context.  Then, `NmOp [{@1}]` normalizes to `1 + Nm[{@1}]`, by
/// using the body of the definition of `NmOp`, and reducing the
/// type-index application.
///
/// ### Reducible forms (not head normal form)
///
/// The following type forms are **reducible**:
///
///   1. `user(_)` / `Ident(_)`   -- user-defined identifiers (each reduces to its definition)
///   2. `(foralli a:g. A) [i]`   -- type-index application
///   3. `(forallt a:K. A) B`     -- type-type application
///
/// ### Normal forms (irreducible forms)
///
/// The following forms are "normal" (irreducible); they each have
/// intro/elim forms in the core language's program syntax:
///
///  1. Base types, sums, products
///  3. `Ref`, `Thk`, `Nm`, `(Nm->Nm)[_]`,
///  4. `exists`
///  5. `forallt`, `foralli`
///  6. `rec`
///  7. type variables, as introduced by `forallt` and `rec` (note: not the same as user-defined type names, which each have a known definition)
///  8. type applications in head normal form.
/// 
pub fn normal_type(ctx:&Ctx, typ:&Type) -> Type {
    match typ {
        // normal forms:
        &Type::Unit         |
        &Type::Var(_)       |
        &Type::Sum(_, _)    |
        &Type::Prod(_, _)   |
        &Type::Thk(_, _)    |
        &Type::Ref(_, _)    |
        &Type::Rec(_, _)    |
        &Type::Nm(_)        |
        &Type::NmFn(_)      |
        &Type::TypeFn(_,_,_)|
        &Type::IdxFn(_,_,_) |
        &Type::NoParse(_)   |
        &Type::Exists(_,_,_,_)
            =>
            typ.clone(),

        &Type::Ident(ref ident) => { match ident.as_str() {
            // Built-in primitives are normal; they lack a definition in the context:
            "Nat" | "Bool" | "String"
                => { typ.clone() }
            
            // all other identifiers are for defined types; look up the definition
            _ => { match ctx.lookup_type_def(ident) {
                Some(a) => normal_type(ctx, &a),
                _ => {
                    println!("undefined type: {} in\n{:?}", ident, ctx);
                    // Give up:
                    typ.clone()
                }
            }}
        }}
        &Type::TypeApp(ref a, ref b) => {
            let a = normal_type(ctx, a);
            let a = match a {
                Type::Rec(_,_) => unroll_type(&a),
                _ => a,
            };
            let b = normal_type(ctx, b);
            match a {
                Type::TypeFn(ref x, ref _k, ref body) => {
                    let body = subst_type_type(b,x,body);
                    normal_type(ctx, &body)
                },
                a => {
                    println!("sort error: expected TypeFn, not {:?}", a);
                    typ.clone()
                }
            }
        }
        &Type::IdxApp(ref a, ref i) => {
            let a = normal_type(ctx, a);
            let a = match a {
                Type::Rec(_,_) => unroll_type(&a),
                _ => a,
            };
            match a {
                Type::IdxFn(ref x, ref _g, ref body) => {
                    let body = subst_idxtm_type(i.clone(),x,body);
                    normal_type(ctx, &body)
                },
                a => {
                    println!("sort error: expected TypeFn, not {:?}", a);
                    typ.clone()
                }
            }
        }
    }
}

pub fn subst_type_type(a:Type, x:&String, b:&Type) -> Type {
    panic!("{:?} {:?} {:?}", a, x, b);
}

pub fn subst_idxtm_type(a:IdxTm, x:&String, b:&Type) -> Type {
    panic!("{:?} {:?} {:?}", a, x, b);
}

/*

Not head normal:
(#a. (#b. b) 3) 4
-->
(#a. 3) 4
-->
3 4
-/->

Not in normal form: (#b.b) 3) --> 3
(#x. ((#b.b) 3))

Is head normal (with lambda as outside thing)
(#x. ((#b.b) 3))

Head normal (with application as outside thing)
x 1 2 3
^
| variable here

*/

/// Unroll a `rec` type, exposing its recursive body's type structure.
///
/// ### Example 1:  
///
/// `unroll_type(rec a. 1 + a)`  
///  = `1 + (rec a. 1 + (rec a. 1 + a))`
///
/// ### Example 2:
///
/// `unroll_type(rec a. (+ 1 + a + (x a x a)))`  
///  = `(+ 1`  
///      `+ (rec a. 1 + a + (x a x a))`  
///      `+ (x (rec a. 1 + a + (x a x a)) x (rec a. 1 + a + (x a x a)))`  
///     `)`  
///
///
pub fn unroll_type(typ:&Type) -> Type {
    // TODO***
    // Needed to implement case in the max example; the `Seq [X][Y] Nat` arg type needs to be "reduced" and then unrolled.
    //unimplemented!("{:?}", typ)
    typ.clone()
}

/// synthesize sort for index term
pub fn synth_idxtm(last_label:Option<&str>, ctx:&Ctx, idxtm:&IdxTm) -> IdxTmDer {
    let fail = |td:IdxTmRule, err :TypeError| { failure(Dir::Synth, last_label, ctx, td, err)  };
    let succ = |td:IdxTmRule, sort:Sort     | { success(Dir::Synth, last_label, ctx, td, sort) };
    match idxtm {
        &IdxTm::Var(ref x) => {
            let td = IdxTmRule::Var(x.clone());
            match ctx.lookup_ivar(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(sort) => succ(td, sort)
            }   
        }
        &IdxTm::Sing(ref nt) => {
            let td0 = synth_nmtm(last_label,ctx,nt);
            let ty0 = td0.clas.clone();
            let td = IdxTmRule::Sing(td0);
            match ty0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(ref t) if *t == Sort::Nm => succ(td, Sort::NmSet),
                Ok(_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Empty => {
            succ(IdxTmRule::Empty, Sort::NmSet)
        },
        &IdxTm::Disj(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctx,idx0);
            let td1 = synth_idxtm(last_label,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::Disj(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmSet),Ok(Sort::NmSet)) => succ(td, Sort::NmSet),
                (Ok(Sort::NmSet),_) => fail(td, TypeError::ParamMism(1)),
                (_,_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Union(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctx,idx0);
            let td1 = synth_idxtm(last_label,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::Union(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmSet),Ok(Sort::NmSet)) => succ(td, Sort::NmSet),
                (Ok(Sort::NmSet),_) => fail(td, TypeError::ParamMism(1)),
                (_,_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Unit => {
            succ(IdxTmRule::Unit, Sort::Unit)
        },
        &IdxTm::Pair(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctx,idx0);
            let td1 = synth_idxtm(last_label,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::Pair(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(t0),Ok(t1)) => succ(td, Sort::Prod(
                    Rc::new(t0), Rc::new(t1),
                ))
            }
        },
        &IdxTm::Proj1(ref idx) => {
            let td0 = synth_idxtm(last_label,ctx,idx);
            let typ0 = td0.clas.clone();
            let td = IdxTmRule::Proj1(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Sort::Prod(t0,_)) => succ(td, (*t0).clone()),
                _ => fail(td, TypeError::ProjNotProd),
            }
        },
        &IdxTm::Proj2(ref idx) => {
            let td0 = synth_idxtm(last_label,ctx,idx);
            let typ0 = td0.clas.clone();
            let td = IdxTmRule::Proj2(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Sort::Prod(_,t1)) => succ(td, (*t1).clone()),
                _ => fail(td, TypeError::ProjNotProd),
            }
        },
        &IdxTm::Lam(ref x, ref x_sort, ref idx) => {
            let ctx_ext = ctx.ivar(x.clone(), x_sort.clone());
            let td0 = synth_idxtm(last_label,&ctx_ext,idx);
            let typ0 = td0.clas.clone();
            let td = IdxTmRule::Lam(x.clone(), x_sort.clone(), td0);
            if let &Sort::NoParse(ref bad) = x_sort {
                return fail(td, TypeError::NoParse(bad.clone()))
            }
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(2)),
                Ok(s) =>  succ(td, Sort::IdxArrow(
                    Rc::new(x_sort.clone()),
                    Rc::new(s),
                )),
            }
        },
        &IdxTm::App(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctx,idx0);
            let td1 = synth_idxtm(last_label,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::App(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::IdxArrow(ref t0,ref t1)),Ok(ref t2)) if **t0 == *t2 => succ(td, (**t1).clone()),
                (Ok(Sort::IdxArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                _ => fail(td, TypeError::AppNotArrow),
            }
        },
        &IdxTm::Map(ref nt, ref idx) => {
            let td0 = synth_nmtm(last_label,ctx,nt);
            let td1 = synth_idxtm(last_label,ctx,idx);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::Map(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmArrow(n0,n1)),Ok(Sort::NmSet)) => {
                    if (*n0 == Sort::Nm) & (*n1 == Sort::Nm) { succ(td, Sort::NmSet) }
                    else { fail(td, TypeError::ParamMism(0)) }
                },
                (Ok(Sort::NmArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                _ => fail(td, TypeError::AppNotArrow),
            }
        },
        &IdxTm::FlatMap(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctx,idx0);
            let td1 = synth_idxtm(last_label,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::FlatMap(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::IdxArrow(n0,n1)),Ok(Sort::NmSet)) => {
                    if (*n0 == Sort::Nm) & (*n1 == Sort::NmSet) { succ(td, Sort::NmSet) }
                    else { fail(td, TypeError::ParamMism(0)) }
                },
                (Ok(Sort::IdxArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                (Ok(_),_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::Star(ref idx0, ref idx1) => {
            let td0 = synth_idxtm(last_label,ctx,idx0);
            let td1 = synth_idxtm(last_label,ctx,idx1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = IdxTmRule::Star(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::IdxArrow(n0,n1)),Ok(Sort::NmSet)) => {
                    if (*n0 == Sort::Nm) & (*n1 == Sort::NmSet) { succ(td,Sort::NmSet) }
                    else { fail(td, TypeError::ParamMism(0)) }
                },
                (Ok(Sort::IdxArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                (Ok(_),_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &IdxTm::NoParse(ref s) => {
            fail(IdxTmRule::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },
    }
}

/// check sort against index term
pub fn check_idxtm(last_label:Option<&str>, ctx:&Ctx, idxtm:&IdxTm, sort:&Sort) -> IdxTmDer {
    // let fail = |td:IdxTmRule, err :TypeError| { failure(Dir::Check, last_label, ctx, td, err)  };
    // let succ = |td:IdxTmRule, sort:Sort     | { success(Dir::Check, last_label, ctx, td, sort) };
    match idxtm {
        // We're exclusively using synthesis for index terms at the moment
        tm => {
            let mut td = synth_idxtm(last_label,ctx,tm);
            let ty = td.clas.clone();
            if let Ok(ty) = ty {
                // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
                if ty == *sort { td }
                else {
                    td.clas = Err(TypeError::AnnoMism);
                    td
                }
            } else { td }
        },
    }  
}

/// synthesize sort for name term
pub fn synth_nmtm(last_label:Option<&str>, ctx:&Ctx, nmtm:&NameTm) -> NmTmDer {
    let fail = |td:NmTmRule, err :TypeError| { failure(Dir::Synth, last_label, ctx, td, err)  };
    let succ = |td:NmTmRule, sort:Sort     | { success(Dir::Synth, last_label, ctx, td, sort) };
    match nmtm {
        &NameTm::Var(ref x) => {
            let td = NmTmRule::Var(x.clone());
            match ctx.lookup_ivar(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(sort) => succ(td, sort)
            }
        },
        &NameTm::Name(ref n) => {
            let td = NmTmRule::Name(n.clone());
            if let &Name::NoParse(ref bad) = n {
                return fail(td, TypeError::NoParse(bad.clone()))
            }
            succ(td, Sort::Nm)
        },
        &NameTm::Bin(ref nt0, ref nt1) => {
            let td0 = synth_nmtm(last_label, ctx, nt0);
            let td1 = synth_nmtm(last_label, ctx, nt1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = NmTmRule::Bin(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::Nm),Ok(Sort::Nm)) => succ(td, Sort::Nm),
                (Ok(Sort::Nm),_) => fail(td, TypeError::ParamMism(1)),
                (_,_) => fail(td, TypeError::ParamMism(0)),
            }
        },
        &NameTm::Lam(ref x, ref s, ref nt) => {
            let ctx_ext = ctx.ivar(x.clone(), s.clone());
            let td0 = synth_nmtm(last_label,&ctx_ext,nt);
            let typ0 = td0.clas.clone();
            let td = NmTmRule::Lam(x.clone(), s.clone(), td0);
            if let &Sort::NoParse(ref bad) = s {
                return fail(td, TypeError::NoParse(bad.clone()))
            }
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(2)),
                Ok(rty) =>  succ(td, Sort::NmArrow(
                    Rc::new(s.clone()),
                    Rc::new(rty),
                )),
            }
        },
        &NameTm::App(ref nt0, ref nt1) => {
            let td0 = synth_nmtm(last_label,ctx,nt0);
            let td1 = synth_nmtm(last_label,ctx,nt1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = NmTmRule::App(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(Sort::NmArrow(ref t0,ref t1)),Ok(ref t2)) if **t0 == *t2 => succ(td, (**t1).clone()),
                (Ok(Sort::NmArrow(_,_)),_) => fail(td, TypeError::ParamMism(1)),
                _ => fail(td, TypeError::AppNotArrow),
            }
        },
        &NameTm::NoParse(ref s) => {
            fail(NmTmRule::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },
    }  
}

/// check sort against name term
pub fn check_nmtm(last_label:Option<&str>, ctx:&Ctx, nmtm:&NameTm, sort:&Sort) -> NmTmDer {
    // let fail = |td:IdxTmRule, err :TypeError| { failure(Dir::Check, last_label, ctx, td, err)  };
    // let succ = |td:IdxTmRule, sort:Sort     | { success(Dir::Check, last_label, ctx, td, sort) };
    match nmtm {
        // We're exclusively using synthesis for name terms at the moment
        tm => {
            let mut td = synth_nmtm(last_label,ctx,tm);
            let ty = td.clas.clone();
            if let Ok(ty) = ty {
                // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
                if ty == *sort { td }
                else {
                    td.clas = Err(TypeError::AnnoMism);
                    td
                }
            } else { td }
        },
    }  
}

/// synthesize sort for value term
pub fn synth_val(last_label:Option<&str>, ctx:&Ctx, val:&Val) -> ValDer {
    let fail = |td:ValRule, err :TypeError| { failure(Dir::Synth, last_label, ctx, td, err)  };
    let succ = |td:ValRule, typ :Type     | { success(Dir::Synth, last_label, ctx, td, typ) };
    match val {
        &Val::Var(ref x) => {
            let td = ValRule::Var(x.clone());
            match ctx.lookup_var(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(ty) => succ(td, ty)
            }
        },
        &Val::Unit => {
            succ(ValRule::Unit, Type::Unit)
        },
        &Val::Pair(ref v0, ref v1) => {
            let td0 = synth_val(last_label, ctx, v0);
            let td1 = synth_val(last_label, ctx, v1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = ValRule::Pair(td0,td1);
            match (typ0,typ1) {
                (Err(_),_) => fail(td, TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td, TypeError::ParamNoSynth(1)),
                (Ok(ty0),Ok(ty1)) => succ(td, Type::Prod(
                    Rc::new(ty0), Rc::new(ty1),
                )),
            }
        },
        &Val::Inj1(ref v) => {
            let td0 = synth_val(last_label, ctx, v);
            let td = ValRule::Inj1(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Val::Inj2(ref v) => {
            let td0 = synth_val(last_label, ctx, v);
            let td = ValRule::Inj2(td0);
            fail(td, TypeError::NoSynthRule)
        },
        &Val::Roll(ref v) => {
            let td0 = synth_val(last_label, ctx, v);
            // let typ0 = td0.clas.clone();
            let td = ValRule::Roll(td0);
            // TODO*: Rule for Roll
            fail(td, TypeError::Unimplemented)
        },
        &Val::Pack(ref a, ref v) => {
            let td1 = synth_val(last_label, ctx, v);
            let td = ValRule::Pack(a.clone(), td1);
            fail(td, TypeError::NoSynthRule)
        }
        &Val::Name(ref n) => {
            let td = ValRule::Name(n.clone());
            match n {
                &Name::NoParse(ref s) => fail(td, TypeError::NoParse(s.clone())),
                _ => succ(td, Type::Nm(IdxTm::Sing(NameTm::Name(n.clone())))),
            }
        },
        &Val::NameFn(ref nmtm) => {
            let td0 = synth_nmtm(last_label, ctx, nmtm);
            let typ0 = td0.clas.clone();
            let td = ValRule::NameFn(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Sort::NmArrow(n0,n1)) => {
                    if (*n0 == Sort::Nm) & (*n1 == Sort::Nm) {
                        succ(td, Type::NmFn(nmtm.clone()))
                    } else { fail(td, TypeError::ParamMism(0)) }
                },
                _ => fail(td, TypeError::ValNotArrow),
            }
        },
        &Val::Anno(ref v,ref t) => {
            let td0 = check_val(last_label, ctx, v, t);
            let typ0 = td0.clas.clone();
            let td = ValRule::Anno(td0, t.clone());
            match typ0 {
                Err(err) => fail(td, err.clone()),
                Ok(typ) => succ(td, typ.clone()),
            }
        },
        &Val::ThunkAnon(ref e) => {
            let td0 = synth_exp(last_label, ctx, e);
            let typ0 = td0.clas.clone();
            let td = ValRule::ThunkAnon(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(ty) => succ(td, Type::Thk(IdxTm::Empty, Rc::new(ty))),
            }
        },
        &Val::Bool(b) => {
            succ(ValRule::Bool(b), type_bool())
        },
        &Val::Nat(n) => {
            succ(ValRule::Nat(n), type_nat())
        },
        &Val::Str(ref s) => {
            succ(ValRule::Str(s.clone()), type_string())
        },
        &Val::NoParse(ref s) => {
            fail(ValRule::NoParse(s.clone()),TypeError::NoParse(s.clone()))
        },
    }
}

/// check sort against value term
pub fn check_val(last_label:Option<&str>, ctx:&Ctx, val:&Val, typ:&Type) -> ValDer {
    let fail = |td:ValRule, err :TypeError| { failure(Dir::Check, last_label, ctx, td, err)  };
    let succ = |td:ValRule, typ :Type     | { success(Dir::Check, last_label, ctx, td, typ) };
    match val {
        &Val::Var(ref x) => {
            let td = ValRule::Var(x.clone());
            match ctx.lookup_var(x) {
                None => fail(td, TypeError::VarNotInScope(x.clone())),
                Some(ty) => {
                    // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
                    if ty == *typ { succ(td, ty) }
                    else { fail(td, TypeError::AnnoMism) }
                }
            }
        },
        &Val::Unit => {
            let td = ValRule::Unit;
            if Type::Unit == *typ { succ(td, typ.clone()) }
            else { fail(td, TypeError::AnnoMism) }
        },
        &Val::Pair(ref v0, ref v1) => {
            if let Type::Prod(ref t0, ref t1) = *typ {
                let td0 = check_val(last_label, ctx, v0, t0);
                let td1 = check_val(last_label, ctx, v1, t1);
                let (typ0,typ1) = (td0.clas.clone(), td1.clas.clone());
                let td = ValRule::Pair(td0,td1);
                match (typ0,typ1) {
                    (Err(_),_) => fail(td, TypeError::ParamNoCheck(0)),
                    (_,Err(_)) => fail(td, TypeError::ParamNoCheck(1)),
                    (Ok(_),Ok(_)) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Pair(
                synth_val(last_label, ctx, v0),
                synth_val(last_label, ctx, v1),
            ), TypeError::AnnoMism) }
        },
        &Val::Inj1(ref v) => {
            if let Type::Sum(ref t1, _) = *typ {
                let td0 = check_val(last_label, ctx, v, t1);
                let typ0 = td0.clas.clone();
                let td = ValRule::Inj1(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Ok(_) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Inj1(
                synth_val(last_label,ctx, v)
            ), TypeError::AnnoMism) }
        },
        &Val::Inj2(ref v) => {
            if let Type::Sum(_, ref t2) = *typ {
                let td0 = check_val(last_label, ctx, v, t2);
                let typ0 = td0.clas.clone();
                let td = ValRule::Inj2(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Ok(_) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Inj2(
                synth_val(last_label,ctx, v)
            ), TypeError::AnnoMism) }
        },
        &Val::Roll(ref v) => {
            // TODO: Rule for Roll
            let temp_td = synth_val(last_label, ctx, v);
            fail(ValRule::Roll(temp_td), TypeError::Unimplemented)
        },
        &Val::Name(ref n) => {
            let td = ValRule::Name(n.clone());
            if let Type::Nm(ref _idx) = *typ {
                match n { 
                    &Name::NoParse(ref s) => fail(td, TypeError::NoParse(s.clone())),
                    // TODO: check that n is a member of idx
                    _ => succ(td, typ.clone())
                }
            } else { fail(td, TypeError::AnnoMism) }
        },
        &Val::NameFn(ref nmtm) => {
            if let Type::NmFn(ref nt) = *typ {
                let td0 = check_nmtm(last_label, ctx, nt, &Sort::NmArrow(
                    Rc::new(Sort::Nm), Rc::new(Sort::Nm),
                ));
                let typ0 = td0.clas.clone();
                let td = ValRule::NameFn(td0);
                match typ0 {
                    Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    // TODO: check equivalence of nmtm and nt
                    Ok(_) => succ(td, typ.clone())
                }
            } else { fail(ValRule::NameFn(
                synth_nmtm(last_label, ctx, nmtm)
            ), TypeError::AnnoMism) }
        },
        &Val::Anno(ref v,ref t) => {
            // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
            if *t == *typ {
                let td0 = check_val(last_label, ctx, v, t);
                let typ0 = td0.clas.clone();
                let td = ValRule::Anno(td0, t.clone());
                match typ0 {
                    Err(err) => fail(td, err.clone()),
                    Ok(typ) => succ(td, typ.clone()),
                }
            } else { fail(ValRule::Anno(
                synth_val(last_label, ctx, v), t.clone()
            ), TypeError::AnnoMism) }
        },
        //
        // Gamma, a:g         ||- P true
        // Gamma, a:g, P true |- v <= A
        // -------------------------------------------- :: existsi
        // Gamma |- pack(a,v) <= (exists a:g|P. A)
        //
        &Val::Pack(ref a1, ref v) => {
            if let Type::Exists(a2,g,p,aa) = typ.clone() {
                if *a1 == a2 {
                    let new_ctx1 = ctx.ivar(a1.clone(),(*g).clone());
                    // TODO: check that p is true
                    let new_ctx2 = new_ctx1.prop(p);
                    let td1 = check_val(last_label, &new_ctx2, v, &aa);
                    let typ1 = td1.clas.clone();
                    let td = ValRule::Pack(a1.clone(), td1);
                    match typ1 {
                        Err(_) => fail(td, TypeError::ParamNoCheck(1)),
                        Ok(_) => succ(td, typ.clone()),
                    }
                } else { fail(ValRule::Pack(
                    a1.clone(), synth_val(last_label, ctx, v)
                ), TypeError::ExistVarMism) }
            } else { fail(ValRule::Pack(
                a1.clone(), synth_val(last_label, ctx, v)
            ), TypeError::AnnoMism) }
        },
        &Val::ThunkAnon(ref e) => {
            if let Type::Thk(ref _idx, ref ce) = *typ {
                let td0 = check_exp(last_label, ctx, &*e, &*ce);
                let typ0 = td0.clas.clone();
                let td = ValRule::ThunkAnon(td0);
                // TODO: use this once effects are implemented
                // if IdxTm::Empty != *idx {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ0 {
                    //Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                    Err(_) => fail(td, TypeError::CheckFailCEffect((**ce).clone())),
                    Ok(_) => succ(td, typ.clone())
                }
            } else { fail(ValRule::ThunkAnon(
                synth_exp(last_label, ctx, e)
            ), TypeError::AnnoMism) }
        },
        &Val::Bool(b) => {
            let td = ValRule::Bool(b);
            if type_bool() == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::Nat(n) => {
            let td = ValRule::Nat(n);
            if type_nat() == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::Str(ref s) => {
            let td = ValRule::Str(s.clone());
            if type_string() == *typ { succ(td, typ.clone())} 
            else { fail(td, TypeError::ParamMism(0)) }
        },
        &Val::NoParse(ref s) => {
            fail(ValRule::NoParse(s.clone()), TypeError::NoParse(s.clone()))
        },
        // v => {
        //     let mut td = synth_val(last_label,ctx,v);
        //     let ty = td.clas.clone();
        //     if let Ok(ty) = ty {
        //         if ty == *typ { td }
        //         else {
        //             td.clas = Err(TypeError::AnnoMism);
        //             td
        //         }
        //     } else { td }
        // },
    }
}

/// Synthesize a typing derivation for a module, given the module AST.
pub fn synth_module(last_label:Option<&str>, m:&Rc<Module>) -> ModuleDer {
    let mut decls = &m.decls;
    let mut tds : Vec<ItemRule> = vec![];
    let mut doc : Option<String> = None;
    let mut ctx = Ctx::Empty;
    fn der_of(ctx:Ctx, rule:DeclRule,
              res:Result<DeclClas,TypeError>) -> DeclDer
    {
        Der{
            ctx:ctx,
            dir:Dir::Synth,
            rule:Rc::new(rule),
            clas:res,
            vis:DerVis{
                tmfam:"Module".to_string(),
            }
        }
    };
    loop {
        match decls {
            &Decls::End => break,
            &Decls::Doc(ref s, ref d) =>
            {
                doc   = Some(s.clone());
                decls = d;
            }            
            &Decls::NoParse(ref s) => {
                tds.push(ItemRule::NoParse(s.clone()));
                break;
            },
            &Decls::UseAll(ref uam, ref d) => {
                let der = synth_module(last_label, &uam.module);
                tds.append(&mut der.tds.clone());
                ctx.append(&der.ctx_out);
                doc = None;
                decls = d;
            }
            &Decls::NmTm(ref x, ref m, ref d) => {
                let der = synth_nmtm(last_label, &ctx, m);
                let sort = der.clas.clone();
                let der = ItemDer{
                    doc:doc.clone(),
                    qual:Qual::NmTm,
                    var:x.clone(),
                    der:der_of(ctx.clone(),
                               DeclRule::NmTm(x.clone(), der),
                               sort.map(|s|DeclClas::Sort(s)))
                };
                doc = None;
                tds.push(ItemRule::Bind(der));
                ctx = ctx.def(x.clone(), Term::NmTm(m.clone()));
                decls = d;
            }
            &Decls::IdxTm(ref x, ref i, ref d) => {
                let der = synth_idxtm(last_label, &ctx, i);
                let sort = der.clas.clone();
                let der = ItemDer{
                    doc:doc.clone(),
                    qual:Qual::IdxTm,
                    var:x.clone(),
                    der:der_of(ctx.clone(),
                               DeclRule::IdxTm(x.clone(), der),
                               sort.map(|s|DeclClas::Sort(s)))
                };
                doc = None;
                tds.push(ItemRule::Bind(der));
                ctx = ctx.def(x.clone(), Term::IdxTm(i.clone()));
                decls = d;
            }
            &Decls::Type(ref x, ref a, ref d) => {
                println!("define type {} {:?}",x, a);
                // TODO: synth kinding for type
                let der = ItemDer{
                    doc:doc.clone(),
                    qual:Qual::Type,
                    var:x.clone(),
                    der:der_of(ctx.clone(),
                               DeclRule::Type(x.clone(), a.clone()),
                               Ok(DeclClas::Kind(Kind::NoParse("TODO-XXX-bitype.rs".to_string()))))
                };
                doc = None;
                tds.push(ItemRule::Bind(der));
                ctx = ctx.def(x.clone(), Term::Type(a.clone()));
                decls = d;
            }
            &Decls::Val(ref x, ref oa, ref v, ref d) => {
                let der = match oa {
                    &None        => synth_val(last_label, &ctx, v   ),
                    &Some(ref a) => check_val(last_label, &ctx, v, a),
                };
                ctx = match der.clas.clone() {
                    Err(_) => match oa {
                        &None        => ctx,
                        &Some(ref a) => ctx.var(x.clone(), a.clone())
                    },
                    Ok(a) => ctx.var(x.clone(), a),
                };
                let der_typ = der.clas.clone();
                let der = ItemDer{
                    doc:doc.clone(),
                    qual:Qual::Val,
                    var:x.clone(),
                    der:der_of(ctx.clone(),
                               DeclRule::Val(x.clone(), der),
                               der_typ.map(|a| DeclClas::Type(a)))
                };
                doc = None;
                tds.push(ItemRule::Bind(der));
                decls = d;
            }
            &Decls::Fn(ref f, ref a, ref e, ref d) => {
                let v : Val = fgi_val![ thunk fix ^f. ^e.clone() ];
                let a2 = a.clone();
                let der = check_val(last_label, &ctx, &v, a);
                let der_typ = der.clas.clone();
                let der = ItemDer{
                    doc:doc.clone(),
                    qual:Qual::Val,
                    var:f.clone(),
                    der:der_of(ctx.clone(),
                               DeclRule::Fn(f.clone(), der),
                               der_typ.map(|_| DeclClas::Type(a2)))
                };
                ctx = ctx.var(f.clone(), a.clone());
                tds.push(ItemRule::Bind(der));
                doc = None;
                decls = d;
            }
        }      
    };
    ModuleDer{
        ast: m.clone(),
        tds: tds,
        ctx_out: ctx,
    }
}

/// Synthesize a type and effect for a program expression
pub fn synth_exp(last_label:Option<&str>, ctx:&Ctx, exp:&Exp) -> ExpDer {
    let fail = |td:ExpRule, err :TypeError| { failure(Dir::Synth, last_label, ctx, td, err) };
    let succ = |td:ExpRule, typ :CEffect  | { success(Dir::Synth, last_label, ctx, td, typ) };
    match exp {
        &Exp::UseAll(ref m, ref exp) => {
            let der = synth_module(last_label, &m.module);
            ctx.append(&der.ctx_out);
            synth_exp(last_label, &ctx, exp)
        }
        &Exp::AnnoC(ref e,ref ctyp) => {
            // TODO: this is a hackthat only works while we're ignoring effects,
            // we need check_exp to handle an optional effect
            let noeffect = Effect::WR(IdxTm::Empty,IdxTm::Empty);
            let td0 = check_exp(last_label, ctx, e, &CEffect::Cons(ctyp.clone(),noeffect));
            let typ0 = td0.clas.clone();
            let td = ExpRule::AnnoC(td0, ctyp.clone());
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoCheck(0)),
                Ok(CEffect::Cons(ct,eff)) => {
                    // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
                    if *ctyp == ct { succ(td, CEffect::Cons(ct,eff)) }
                    else { fail(td, TypeError::AnnoMism) }
                },
                _ => fail(td, TypeError::ExpNotCons)
            }
        },
        &Exp::AnnoE(ref e,ref et) => {
            let td0 = check_exp(last_label, ctx, e, et);
            let typ0 = td0.clas.clone();
            let td = ExpRule::AnnoE(td0, et.clone());
            match typ0 {
                Ok(ty) => succ(td, ty),
                Err(_err) => {                    
                    fail(td, TypeError::CheckFailCEffect((et.clone())))
                }
            }
        },
        &Exp::Force(ref v) => {
            let td0 = synth_val(last_label, ctx, v);
            let typ0 = td0.clas.clone();
            let td = ExpRule::Force(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(Type::Thk(ref _idx,ref ce)) => {
                    // TODO: Compose effects
                    succ(td, (**ce).clone())
                }
                Ok(t) => fail(td, TypeError::UnexpectedType(t.clone())),
            }
        },
        &Exp::DefType(ref x,ref t, ref e) => {
            let ctx = &ctx.def(x.clone(), Term::Type(t.clone()));
            let td2 = synth_exp(last_label, ctx, e);
            // TODO: user-type kinding??
            let typ2 = td2.clas.clone();
            let td = ExpRule::DefType(x.clone(), t.clone(), td2);
            match typ2 {
                Err(_) => fail(td, TypeError::ParamNoSynth(2)),
                Ok(ty) => succ(td, ty.clone()),
            }
        },
        &Exp::App(ref e, ref v) => {
            let td0 = synth_exp(last_label, ctx, e);
            let typ0 = td0.clas.clone();
            match typ0 {
                Err(_) => {
                    let td1 = synth_val(last_label, ctx, v);
                    let td = ExpRule::App(td0,td1);
                    fail(td, TypeError::SynthFailVal(v.clone()))
                },
                Ok(CEffect::Cons(CType::Arrow(ref ty,ref ce), ref _ef)) => {
                    let td1 = check_val(last_label, ctx, v, ty);
                    let ty1 = td1.clas.clone();
                    let td = ExpRule::App(td0,td1);
                    match ty1 {
                        Err(_) => fail(td, TypeError::ParamMism(1)),
                        Ok(_) => {
                            // TODO: compose effects
                            succ(td, (**ce).clone())
                        }
                    }
                },
                Ok(ce) => {
                    let td1 = synth_val(last_label, ctx, v);
                    let td = ExpRule::App(td0,td1);
                    fail(td, TypeError::UnexpectedCEffect(ce.clone()))
                }
            }
        },
        &Exp::Get(ref v) => {
            let td0 = synth_val(last_label, ctx, v);
            let typ0 = td0.clas.clone();
            let td = ExpRule::Get(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::SynthFailVal(v.clone())),
                Ok(Type::Ref(ref idx,ref ty)) => succ(td, CEffect::Cons(
                    CType::Lift((**ty).clone()),
                    Effect::WR(IdxTm::Empty, idx.clone())
                )),
                Ok(_) => fail(td, TypeError::GetNotRef)
            }
        },
        &Exp::Ret(ref v) => {
            let td0 = synth_val(last_label, ctx, v);
            let typ0 = td0.clas.clone();
            let td = ExpRule::Ret(td0);
            match typ0 {
                Err(_) => fail(td, TypeError::ParamNoSynth(0)),
                Ok(ty) => succ(td, CEffect::Cons(
                    CType::Lift(ty),
                    Effect::WR(IdxTm::Empty, IdxTm::Empty)
                )),
            }
        },
        &Exp::Let(ref x, ref e1, ref e2) => {
            let td1 = synth_exp(last_label, ctx, e1);
            match td1.clas.clone() {
                Err(_) => fail(ExpRule::Let(x.clone(),td1,
                    synth_exp(last_label, ctx, e2)
                ), TypeError::ParamNoSynth(1)),
                Ok(CEffect::Cons(CType::Lift(ty1),_eff1)) => {
                    let new_ctx = ctx.var(x.clone(), ty1);
                    let td2 = synth_exp(last_label, &new_ctx, e2);
                    let typ2 = td2.clas.clone();
                    let td = ExpRule::Let(x.clone(),td1,td2);
                    match typ2 {
                        Err(_) => fail(td, TypeError::ParamNoSynth(2)),
                        Ok(CEffect::Cons(ty2,eff2)) => {
                            // TODO: combine effects
                            succ(td, CEffect::Cons(ty2, eff2))
                        },
                        _ => fail(td, TypeError::ParamMism(2)),
                    }
                },
                _ => fail(ExpRule::Let(x.clone(),td1,
                    synth_exp(last_label, ctx, e2)
                ), TypeError::ParamMism(1)),
            }
        },
        &Exp::PrimApp(PrimApp::NameBin(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctx, v0);
            let td1 = synth_val(last_label, ctx, v1);
            let (typ0,typ1) = (td0.clas.clone(),td1.clas.clone());
            let td = ExpRule::PrimApp(PrimAppRule::NameBin(td0,td1));
            match (typ0,typ1) {
                (Err(_),_) => fail(td,TypeError::ParamNoSynth(0)),
                (_,Err(_)) => fail(td,TypeError::ParamNoSynth(1)),
                (Ok(Type::Nm(_)),Ok(Type::Nm(_))) => {
                    if let (&Val::Name(ref nm0),&Val::Name(ref nm1)) = (v0,v1) {
                        succ(td, CEffect::Cons(
                            CType::Lift(Type::Nm(
                                IdxTm::Sing(NameTm::Name(Name::Bin(
                                    Rc::new(nm0.clone()),
                                    Rc::new(nm1.clone()),
                                )))
                            )),
                            Effect::WR(IdxTm::Empty, IdxTm::Empty))
                        )
                    } else { unreachable!("NameBin: Type::Nm not Val::Name") }
                },
                (Ok(Type::Nm(_)),_) => fail(td,TypeError::ParamMism(1)),
                _ => fail(td, TypeError::ParamMism(0))
            }
        },
        &Exp::PrimApp(PrimApp::RefThunk(ref v)) => {
            let td0 = synth_val(last_label, ctx, v);
            let td = ExpRule::PrimApp(PrimAppRule::RefThunk(td0));
            // TODO**: implement
            // XXX -- for example
            fail(td, TypeError::Unimplemented)
        },        
        &Exp::PrimApp(PrimApp::NatLt(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctx, v0);
            let td1 = synth_val(last_label, ctx, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatLt(td0,td1));
            // TODO**: implement
            // XXX -- for max example:
            fail(td, TypeError::Unimplemented)
        },
        &Exp::Unimp => {
            let td = ExpRule::Unimp;
            fail(td, TypeError::NoSynthRule)
        },
        &Exp::DebugLabel(ref n, ref s,ref e) => {
            let td2 = match s {
                &None => synth_exp(last_label, ctx, e),
                &Some(ref lbl) => synth_exp(Some(lbl), ctx, e),
            };
            let typ2 = td2.clas.clone();
            let td = ExpRule::DebugLabel(n.clone(),s.clone(),td2);
            match typ2 {
                // Copy/propagate the error; do not replace it with a new one.
                Err(err) => fail(td, err),
                Ok(ty) => succ(td, ty),
            }
        },
        &Exp::NoParse(ref s) => {
            fail(ExpRule::NoParse(s.clone()), TypeError::NoParse(s.clone()))
        },
        &Exp::HostFn(ref hef) => {
            fail(ExpRule::HostFn(hef.clone()),
                 TypeError::NoSynthRule)
        },
        //
        // -------- low priority:
        //
        
        &Exp::NameFnApp(ref v0,ref v1) => {
            let td0 = synth_val(last_label, ctx, v0);
            let td1 = synth_val(last_label, ctx, v1);
            let td = ExpRule::NameFnApp(td0,td1);
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatEq(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctx, v0);
            let td1 = synth_val(last_label, ctx, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatEq(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatLte(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctx, v0);
            let td1 = synth_val(last_label, ctx, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatLte(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },
        &Exp::PrimApp(PrimApp::NatPlus(ref v0,ref v1)) => {
            let td0 = synth_val(last_label, ctx, v0);
            let td1 = synth_val(last_label, ctx, v1);
            let td = ExpRule::PrimApp(PrimAppRule::NatPlus(td0,td1));
            // TODO: implement
            fail(td, TypeError::Unimplemented)
        },

        //
        // -------- More cases (lowest priority)
        //

        &Exp::Scope(ref v,ref e) => {            
            let td0 = synth_val(last_label, ctx, v);
            let td1 = synth_exp(last_label, ctx, e);
            let td = ExpRule::Scope(td0,td1);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },
        &Exp::Split(ref v, ref x1, ref x2, ref e) => {
            let td0 = synth_val(last_label, ctx, v);
            let td3 = synth_exp(last_label, ctx, e);
            let td = ExpRule::Split(td0,x1.clone(),x2.clone(),td3);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },
        &Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2) => {
            let td0 = synth_val(last_label, ctx, v);
            let td2 = synth_exp(last_label, ctx, e1);
            let td4 = synth_exp(last_label, ctx, e2);
            let td = ExpRule::Case(td0,x1.clone(),td2,x2.clone(),td4);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },
        &Exp::IfThenElse(ref v, ref e1, ref e2) => {
            let td0 = synth_val(last_label, ctx, v);
            let td1 = synth_exp(last_label, ctx, e1);
            let td2 = synth_exp(last_label, ctx, e2);
            let td = ExpRule::IfThenElse(td0,td1,td2);
            // TODO: implement
            fail(td, TypeError::Unimplemented) // Ok, for now.
        },
        &Exp::Ref(ref v1,ref v2) => {
            let td0 = synth_val(last_label, ctx, v1);
            let td1 = synth_val(last_label, ctx, v2);
            let td = ExpRule::Ref(td0,td1);
            fail(td, TypeError::NoSynthRule) // Ok, for now.
        },

        // ==  
        // == -- No synth rules for these forms
        // ==
        &Exp::Thunk(ref v,ref e) => {
            let td0 = synth_val(last_label, ctx, v);
            let td1 = synth_exp(last_label, ctx, e);
            let td = ExpRule::Thunk(td0,td1);
            fail(td, TypeError::NoSynthRule) // Ok
        },
        &Exp::Fix(ref x,ref e) => {
            let td1 = synth_exp(last_label, ctx, e);
            let td = ExpRule::Fix(x.clone(), td1);
            fail(td, TypeError::NoSynthRule) // Ok
        },
        &Exp::Lam(ref x, ref e) => {
            let td1 = synth_exp(last_label, ctx, e);
            let td = ExpRule::Lam(x.clone(), td1);
            fail(td, TypeError::NoSynthRule) // Ok
        },        
        &Exp::Unroll(ref v,ref x,ref e) => {
            let td0 = synth_val(last_label, ctx, v);
            let td2 = synth_exp(last_label, ctx, e);
            let td = ExpRule::Unroll(td0, x.clone(), td2);
            fail(td, TypeError::Unimplemented) // Ok
        },
        &Exp::Unpack(ref i, ref x, ref v, ref e) => {
            let td2 = synth_val(last_label, ctx, v);
            let td3 = synth_exp(last_label, ctx, e);
            let td = ExpRule::Unpack(i.clone(),x.clone(),td2,td3);
            fail(td, TypeError::NoSynthRule)
        }
    }
}

/// Check a type and effect against a program expression
pub fn check_exp(last_label:Option<&str>, ctx:&Ctx, exp:&Exp, ceffect:&CEffect) -> ExpDer {
    let fail = |td:ExpRule, err :TypeError| { failure(Dir::Check, last_label, ctx, td, err) };
    let succ = |td:ExpRule, typ :CEffect  | { success(Dir::Check, last_label, ctx, td, typ) };
    match exp {
        &Exp::Fix(ref x,ref e) => {            
            let new_ctx = ctx.var(x.clone(), Type::Thk(IdxTm::Empty, Rc::new(ceffect.clone())));
            let td = check_exp(last_label, &new_ctx, e, ceffect);
            let td_typ = td.clas.clone();
            match td_typ {
                Err(_) => fail(ExpRule::Fix(x.clone(),td), TypeError::CheckFailCEffect((ceffect.clone()))),
                Ok(_)  => succ(ExpRule::Fix(x.clone(),td), ceffect.clone())
            }
        },
        &Exp::Lam(ref x, ref e) => {
            // Strip off "forall" quantifiers in the ceffect type, moving their assumptions into the context.
            fn strip_foralls (ctx:&Ctx, ceffect:&CEffect) -> (Ctx, CEffect) {
                match ceffect {
                    &CEffect::ForallType(ref _a, ref _kind, ref ceffect) => {
                        // TODO**: extend context with _x, etc.
                        strip_foralls(ctx, ceffect)
                    },
                    &CEffect::ForallIdx(ref _a, ref _sort, ref _prop, ref ceffect) => {
                        // TODO**: extend context with _x, etc.
                        strip_foralls(ctx, ceffect)
                    },
                    &CEffect::Cons(_, _) => { (ctx.clone(), ceffect.clone()) }
                    &CEffect::NoParse(_) => { (ctx.clone(), ceffect.clone()) }
                }
            }
            let (ctx, ceffect) = strip_foralls(ctx, ceffect);            
            if let CEffect::Cons(CType::Arrow(ref at,ref et),ref _ef) = ceffect {
                let new_ctx = ctx.var(x.clone(),at.clone());
                let td1 = check_exp(last_label, &new_ctx, e, et);
                let typ1 = td1.clas.clone();
                let td = ExpRule::Lam(x.clone(), td1);
                // TODO: use this once effects are properly implemented
                // if *ef != Effect::WR(IdxTm::Empty,IdxTm::Empty) {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ1 {
                    Err(_) => fail(td, TypeError::CheckFailCEffect((ceffect.clone()))),
                    Ok(_) => succ(td, ceffect.clone()),
                }
            } else { fail(ExpRule::Lam(
                x.clone(), synth_exp(last_label, &ctx, e)
            ), TypeError::AnnoMism) }
        },
        &Exp::Unroll(ref v,ref x,ref e) => {
            let v_td = synth_val(last_label, ctx, v);
            match v_td.clas.clone() {
                Err(_) => {
                    let td0 = check_exp(last_label, ctx, e, ceffect);
                    fail(ExpRule::Unroll(v_td, x.clone(), td0),
                         TypeError::SynthFailVal(v.clone()))
                }
                Ok(v_ty) => {
                    // TODO** -- Call `reduce_type`,
                    // and then `unroll_type` before extending
                    // context with `v_ty`.
                    let new_ctx = ctx.var(x.clone(), v_ty);
                    let td0 = check_exp(last_label, &new_ctx, e, ceffect);
                    let td0_typ = td0.clas.clone();
                    let td = ExpRule::Unroll(v_td, x.clone(), td0);
                    match td0_typ {
                        Err(_) => fail(td, TypeError::CheckFailCEffect((ceffect.clone()))),
                        Ok(_)  => succ(td, ceffect.clone())
                    }
                }
            }
        },
        ///////////////////////////////////////////////////////
        //
        // Gamma |- v => (exists a:g|P. A)
        // Gamma, b:g, [b/a]P true, x:[b/a]A |- e <= E
        // -------------------------------------------- :: unpack2
        // Gamma |- unpack(v,x.b.e) <= E                                   
        //
        // more general version of rule that permits index vars `a`
        // and `b` to differ; requires substituting an index term for
        // an index variable (index term 'b', a variable, for variable
        // 'a') in propositions, in indices and in types.
        //
        /////////////////////////////////////////////////////////
        //
        // Gamma |- v => (exists a:g|P. A)
        // Gamma, a:g, P true, x:A |- e <= E
        // ---------------------------------- :: unpack
        // Gamma |- unpack(v,x.a.e) <= E
        //
        &Exp::Unpack(ref a1, ref x, ref v, ref e) => {
            let td2 = synth_val(last_label, ctx, v);
            match td2.clas.clone() {
                Ok(Type::Exists(ref a2, ref g, ref p, ref aa)) => {
                    if *a1 == *a2 {
                        let new_ctx = ctx
                            .ivar(a1.clone(),(**g).clone())
                            .prop(p.clone())
                            .var(x.clone(),(**aa).clone())
                        ;
                        let td3 = check_exp(last_label, &new_ctx, e, &ceffect);
                        let typ3 = td3.clas.clone();
                        let td = ExpRule::Unpack(a1.clone(),x.clone(),td2,td3);
                        match typ3 {
                            Err(_) => fail(td, TypeError::ParamNoCheck(3)),
                            Ok(_) => succ(td, ceffect.clone())
                        }

                    } else {
                        // TODO: See more general version of rule, above.
                        let td3 = synth_exp(last_label, ctx, e);
                        let td = ExpRule::Unpack(a1.clone(),x.clone(),td2,td3);
                        fail(td, TypeError::ExistVarMism)
                    }
                },
                rt => {
                    let td3 = synth_exp(last_label, ctx, e);
                    let td = ExpRule::Unpack(a1.clone(),x.clone(),td2,td3);
                    if let Err(_) = rt { fail(td, TypeError::ParamNoSynth(2)) }
                    else { fail(td, TypeError::ParamMism(2)) }
                }
            }
        },
        &Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2) => {
            let v_td = synth_val(last_label, ctx, v);
            let v_ty = v_td.clone().clas.map(|a| normal_type(ctx, &a));
            match v_ty {
                Ok(Type::Sum(ty1, ty2)) => {
                    let new_ctx1 = ctx.var(x1.clone(), (*ty1).clone());
                    let new_ctx2 = ctx.var(x2.clone(), (*ty2).clone());
                    let td1 = check_exp(last_label, &new_ctx1, e1, ceffect);
                    let td1_typ = td1.clas.clone();
                    let td2 = check_exp(last_label, &new_ctx2, e2, ceffect);
                    let td2_typ = td2.clas.clone();
                    let td = ExpRule::Case(v_td, x1.clone(), td1, x2.clone(), td2);
                    match (td1_typ, td2_typ) {
                        (Ok(_),Ok(_)) => succ(td, ceffect.clone()),
                        (_    ,_    ) => fail(td, TypeError::CheckFailCEffect((ceffect.clone()))),
                    }
                }
                Ok(t) => {
                    let td1 = check_exp(last_label, ctx, e1, ceffect);
                    let td2 = check_exp(last_label, ctx, e2, ceffect);
                    fail(ExpRule::Case(v_td, x1.clone(), td1, x2.clone(), td2),
                         TypeError::UnexpectedType(t))
                }
                _ => {
                    let td1 = check_exp(last_label, ctx, e1, ceffect);
                    let td2 = check_exp(last_label, ctx, e2, ceffect);
                    fail(ExpRule::Case(v_td, x1.clone(), td1, x2.clone(), td2),
                         TypeError::SynthFailVal(v.clone()))
                }
            }
        },
        &Exp::Let(ref x,ref e1, ref e2) => {
            if let CEffect::Cons(ref ctyp,ref _eff) = *ceffect {
                let td1 = synth_exp(last_label, ctx, e1);
                let typ1 = td1.clas.clone();
                match typ1 {
                    Err(_) => { fail(ExpRule::Let(
                        x.clone(), td1,
                        synth_exp(last_label, ctx, e2)
                    ), TypeError::ParamNoSynth(1)) },
                    Ok(CEffect::Cons(CType::Lift(ref ct1),ref _eff1)) => {
                        let new_ctx = ctx.var(x.clone(),ct1.clone());
                        // TODO: compute this effect
                        let eff2 = Effect::WR(IdxTm::Empty,IdxTm::Empty);
                        let typ2 = CEffect::Cons(ctyp.clone(), eff2);
                        let td2 = check_exp(last_label, &new_ctx, e2, &typ2);
                        let typ2res = td2.clas.clone();
                        let td = ExpRule::Let(x.clone(), td1,td2);
                        match typ2res {
                            Err(_) => fail(td, TypeError::ParamNoCheck(2)),
                            Ok(_) => succ(td, ceffect.clone()),
                        }
                    },
                    _ => fail(ExpRule::Let(
                        x.clone(), td1,
                        synth_exp(last_label,ctx,e2)
                    ), TypeError::ParamMism(1)),
                }
            } else { fail(ExpRule::Let(x.clone(),
                synth_exp(last_label, ctx, e1),
                synth_exp(last_label, ctx, e1),
            ), TypeError::AnnoMism) }
        },
        &Exp::Ret(ref v) => {
            if let CEffect::Cons(CType::Lift(ref t),ref _ef) = *ceffect {
                let td0 = check_val(last_label, ctx, v, t);
                let typ0 = td0.clas.clone();
                let td = ExpRule::Ret(td0);
                // TODO: use this once effects are properly implemented
                // if *ef != Effect::WR(IdxTm::Empty,IdxTm::Empty) {
                //     return fail(td, TypeError::InvalidPtr)
                // }
                match typ0 {
                    Err(_) => fail(td, TypeError::CheckFailType((t.clone()))),
                    Ok(_) => succ(td, ceffect.clone())
                }
            } else { fail(ExpRule::Ret(
                synth_val(last_label,ctx,v)
            ), TypeError::AnnoMism) }
        },
        
        // XXX: TODO next:
        //   &Exp::Split(ref v, ref x1, ref x2, ref e) => {},
        //   &Exp::IfThenElse(ref v, ExpRec, ExpRec) => {},
        //
        // TODO later:
        //   &Exp::Scope(ref v,ref e) => {},
        //
        //
        // Later and/or use synth rule:
        //   &Exp::App(ref e, ref v) => {},
        //   &Exp::Force(ref v) => {},
        //   &Exp::Get(ref v) => {},
        //   &Exp::DefType(ref x,Type,ref e) => {},
        //   &Exp::AnnoC(ref e,ref ct) => {},
        //   &Exp::AnnoE(ref e,ref et) => {},      
        //   &Exp::Thunk(ref v,ref e) => {},
        //   &Exp::Ref(ref v1,ref v2) => {},
        //   &Exp::PrimApp(PrimApp) => {},
        //   &Exp::NameFnApp(ref v1,ref v2) => {},
        //
        &Exp::HostFn(ref hef) => {
            succ(ExpRule::HostFn(hef.clone()), ceffect.clone())
        }        
        &Exp::Unimp => {
            succ(ExpRule::Unimp, ceffect.clone())
        },
        &Exp::DebugLabel(ref _n, ref s, ref e) => {
            match s {
                &None => check_exp(last_label, ctx, e, ceffect),
                &Some(ref lbl) => check_exp(Some(lbl), ctx, e, ceffect),
            }
            
        },
        &Exp::NoParse(ref s) => {
            fail(ExpRule::NoParse(s.clone()), TypeError::NoParse(s.clone()))
        },
        e => {
            let mut td = synth_exp(last_label,ctx,e);
            let ty = td.clas.clone();
            if let Ok(ty) = ty {
                // TODO: Type equality may be more complex than this test (e.g. alpha equivalent types should be equal)
                if ty == *ceffect { td }
                else {
                    td.clas = Err(TypeError::AnnoMism);
                    td
                }
            } else { td }
        },
    }
}



/// Stringification for debugging derivation rules
mod debug {
    use super::*;
    // rule instance in a derivation tree
    pub trait DerRule {
        /// short term family description
        fn term_desc() -> &'static str { "unknown term family" }
        /// short name for rule
        fn short(&self) -> &str { "unknown rule" }
    }

    impl DerRule for NmTmRule {
        fn term_desc() -> &'static str { "name-term" }
        fn short(&self) -> &str {
            match *self {
                NmTmRule::Var(_) => "Var",
                NmTmRule::Name(_) => "Name",
                NmTmRule::Bin(_, _) => "Bin",
                NmTmRule::Lam(_,_,_) => "Lam",
                NmTmRule::App(_, _) => "App",
                NmTmRule::NoParse(_) => "NoParse",
            }
        }
    }

    impl DerRule for IdxTmRule {
        fn term_desc() -> &'static str { "index-term" }
        fn short(&self) -> &str {
            match *self {
                IdxTmRule::Var(_) => "Var",
                IdxTmRule::Sing(_) => "Sing",
                IdxTmRule::Empty => "Empty",
                IdxTmRule::Disj(_, _) => "Disj",
                IdxTmRule::Union(_, _) => "Union",
                IdxTmRule::Unit => "Unit",
                IdxTmRule::Pair(_, _) => "Pair",
                IdxTmRule::Proj1(_) => "Proj1",
                IdxTmRule::Proj2(_) => "Proj2",
                IdxTmRule::Lam(_, _, _) => "Lam",
                IdxTmRule::App(_, _) => "App",
                IdxTmRule::Map(_, _) => "Map",
                IdxTmRule::FlatMap(_, _) => "FlatMap",
                IdxTmRule::Star(_, _) => "Star",
                IdxTmRule::NoParse(_) => "NoParse",
            }
        }
    }

    impl DerRule for ValRule {
        fn term_desc() -> &'static str { "value" }
        fn short(&self) -> &str {
            match *self {
                ValRule::Var(_) => "Var",
                ValRule::Unit => "Unit",
                ValRule::Pair(_, _) => "Pair",
                ValRule::Inj1(_) => "Inj1",
                ValRule::Inj2(_) => "Inj2",
                ValRule::Roll(_) => "Roll",
                ValRule::Pack(_,_) => "Pack",
                ValRule::Name(_) => "Name",
                ValRule::NameFn(_) => "NameFn",
                ValRule::Anno(_,_) => "Anno",
                ValRule::ThunkAnon(_) => "ThunkAnon",
                ValRule::Bool(_) => "Bool",
                ValRule::Nat(_) => "Nat",
                ValRule::Str(_) => "Str",
                ValRule::NoParse(_) => "NoParse",
            }
        }
    }

    impl DerRule for ExpRule {
        fn term_desc() -> &'static str { "expression" }
        fn short(&self) -> &str {
            match *self {
                ExpRule::AnnoC(_,_) => "AnnoC",
                ExpRule::AnnoE(_,_) => "AnnoE",
                ExpRule::Force(_) => "Force",
                ExpRule::Thunk(_,_) => "Thunk",
                ExpRule::Unroll(_,_,_) => "Unroll",
                ExpRule::Unpack(_,_,_,_) => "Unpack",
                ExpRule::Fix(_,_) => "Fix",
                ExpRule::Ret(_) => "Ret",
                ExpRule::DefType(_,_,_) => "DefType",
                ExpRule::Let(_,_,_) => "Let",
                ExpRule::Lam(_, _) => "Lam",
                ExpRule::HostFn(_) => "HostFn",
                ExpRule::App(_, _) => "App",
                ExpRule::Split(_, _, _, _) => "Split",
                ExpRule::Case(_, _, _, _, _) => "Case",
                ExpRule::IfThenElse(_, _, _) => "IfThenElse",
                ExpRule::Ref(_,_) => "Ref",
                ExpRule::Get(_) => "Get",
                ExpRule::Scope(_,_) => "Scope",
                ExpRule::NameFnApp(_,_) => "NameFnApp",
                ExpRule::PrimApp(ref p) => p.short(),
                ExpRule::Unimp => "Unimp",
                ExpRule::DebugLabel(_,_,_) => "DebugLabel",
                ExpRule::NoParse(_) => "NoParse",
            }
        }
    }
    impl DerRule for PrimAppRule {
        fn term_desc() -> &'static str { "primitive expression" }
        fn short(&self) -> &str {
            match *self {
                PrimAppRule::NatEq(_,_) => "NatEq",
                PrimAppRule::NatLt(_,_) => "NatLt",
                PrimAppRule::NatLte(_,_) => "NatLte",
                PrimAppRule::NatPlus(_,_) => "NatPlus",
                PrimAppRule::NameBin(_,_) => "NameBin",
                PrimAppRule::RefThunk(_) => "RefThunk",
            }
        }
    }
}
//use self::debug::*;
