/*! Decision procedures for Fungi type and effect system. */

use ast::*;
use bitype::{Ctx,HasClas,TypeError};
use normal;
//use std::fmt;
use std::rc::Rc;

/// Pair of related variables
pub type Var2 = (Var, Var);

/// Relational typing context: Relates pairs of variables, terms, etc
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum RelCtx {
    /// Basecase 1: empty context
    Empty,
    /// Basecase 2: Non-relational typing context
    Ctx(Ctx),
    /// Assume a name variable equivalence, at a common sort
    NVarEquiv(RelCtxRec,Var,Var,Sort),
    /// Assume a name variable apartness, at a common sort
    NVarApart(RelCtxRec,Var,Var,Sort),
    /// Assume an index variable equivalence, at a common sort
    IVarEquiv(RelCtxRec,Var,Var,Sort),
    /// Assume an index variable apartness, at a common sort
    IVarApart(RelCtxRec,Var,Var,Sort),
    /// Assume a proposition is true
    PropTrue(RelCtxRec,Prop),
    /// Type variables are related: TODO: Kinds?
    TVarRelated(RelCtxRec,Var,Var)
}
pub type RelCtxRec = Rc<RelCtx>;

impl RelCtx {
    pub fn prop_true(&self, p:Prop) -> Self {
        RelCtx::PropTrue(Rc::new(self.clone()), p)
    }    
    pub fn add_tvars(&self, a:Var, b:Var) -> Self {
        RelCtx::TVarRelated(Rc::new(self.clone()),a,b)
    }
    pub fn add_ivars(&self, a:Var, b:Var, g:Sort) -> Self {
        // TODO(?): Related ivars same as "equivalent" ivars?
        RelCtx::IVarEquiv(Rc::new(self.clone()), a, b, g)
    }
    pub fn ivar(&self, a:Var, b:Var, g:Sort) -> Self { self.add_ivars(a,b,g) }

    pub fn nt_eq(&self,n1:&Var,n2:&Var,g:&Sort) -> Self {
        RelCtx::NVarEquiv(Rc::new(self.clone()),n1.clone(),n2.clone(),g.clone())
    }
    pub fn rest(&self) -> Option<RelCtxRec> {
        match self {
            &RelCtx::Empty => None,
            &RelCtx::Ctx(ref _c) => None,
            &RelCtx::NVarEquiv(ref c,_,_,_) |
            &RelCtx::NVarApart(ref c,_,_,_) |
            &RelCtx::IVarEquiv(ref c,_,_,_) |
            &RelCtx::IVarApart(ref c,_,_,_) |
            &RelCtx::TVarRelated(ref c,_,_) |
            &RelCtx::PropTrue(ref c,_) => { Some(c.clone()) }
        }
    }
    pub fn lookup_tvars(&self, x1:&Var, x2:&Var) -> bool {
        match self {
            &RelCtx::TVarRelated(ref c, ref v1, ref v2) => {
                if (x1 == v1) && (x2 == v2) { true }
                else { c.lookup_tvars(x1,x2) }
            }
            c => c.rest().map_or(false,|c|c.lookup_tvars(x1,x2))
        }
    }
    pub fn lookup_nvareq(&self, x1:&Var, x2:&Var, g:&Sort) -> bool {
        match self {
            &RelCtx::NVarEquiv(ref c, ref v1, ref v2, ref s) => {
                // TODO: sort compatibility?
                if (x1 == v1) && (x2 == v2) && (g == s) { true }
                else { c.lookup_nvareq(x1,x2,g) }
            }
            c => c.rest().map_or(false,|c|c.lookup_nvareq(x1,x2,g))
        }
    }
    // pub fn lookup_nvareq_sort(&self, x1:&Var, x2:&Var) -> Option<Sort> {
    //     match self {
    //         &RelCtx::NVarEquiv(ref c, ref v1, ref v2, ref s) => {
    //             if (x1 == v1) && (x2 == v2) { Some(s.clone()) }
    //             else { c.lookup_nvareq_sort(x1,x2) }
    //         }
    //         c => c.rest().and_then(|c|c.lookup_nvareq_sort(x1,x2))
    //     }
    // }
    pub fn lookup_ivareq(&self, x1:&Var, x2:&Var, g:&Sort) -> bool {
        match self {
            &RelCtx::NVarEquiv(ref c, ref v1, ref v2, ref s) => {
                // TODO: sort compatibility?
                if (x1 == v1) && (x2 == v2) && (g == s) { true }
                else { c.lookup_ivareq(x1,x2,g) }
            }
            c => c.rest().map_or(false,|c|c.lookup_ivareq(x1,x2,g))
        }
    }
}

/// Convert the context into the corresponding relational context
pub fn relctx_of_ctx(c: &Ctx) -> RelCtx {
    RelCtx::Ctx(c.clone())
}

/// Each relation has two sides, which we refer to as `L` and `R`
pub enum HandSide { L, R }

/// Convert the context into the corresponding relational context
pub fn ctxs_of_relctx(c: RelCtx) -> (Ctx,Ctx) {
    match c {
        RelCtx::Empty => {
            (Ctx::Empty, Ctx::Empty)
        }
        RelCtx::Ctx(ctx) => {
            (ctx.clone(), ctx)
        }
        RelCtx::NVarEquiv(ctx,x,y,g) |
        RelCtx::NVarApart(ctx,x,y,g) |
        RelCtx::IVarApart(ctx,x,y,g) |
        RelCtx::IVarEquiv(ctx,x,y,g) => {
            let (ctx1,ctx2) = ctxs_of_relctx_rec(ctx);
            (ctx1.ivar(x,g.clone()),ctx2.ivar(y,g))
        }
        RelCtx::PropTrue(ctx,p) => {
            // TODO: Should we have two props?
            // Or should we continue to mirror the prop on both LH and RH sides?
            let (ctx1,ctx2) = ctxs_of_relctx_rec(ctx);
            (ctx1.prop(p.clone()), ctx2.prop(p))
        }
        RelCtx::TVarRelated(ctx,x,y) => {
            let (ctx1,ctx2) = ctxs_of_relctx_rec(ctx);
            (ctx1.tvar(x,Kind::Type),ctx2.tvar(y,Kind::Type))
        }
    }
}

/// Convert the context into the corresponding relational context
pub fn ctxs_of_relctx_rec(c: Rc<RelCtx>) -> (Rc<Ctx>, Rc<Ctx>) {
    let (c1,c2) = ctxs_of_relctx((*c).clone());
    (Rc::new(c1), Rc::new(c2))
}

/// Decision-related error
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub enum DecError {
    /// Type/sort/kind error during the decision procedure
    TypeError(TypeError),
    InSubDec,
    LamNotArrow,
    AppNotArrow,
    PairNotProd,
}

/// Derivation for a decision procedure, expressed as deductive inference rules
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Dec<Rule:HasClas> {
    pub ctx:RelCtx,
    pub rule:Rc<Rule>,
    pub clas:Rule::Clas,
    pub res:Result<bool,DecError>
}


/// Decide equivalence of two terms (types, indices, name terms)
pub mod equiv {
    use ast::*;
    use bitype::{HasClas};
    use bitype::{NmTmDer,IdxTmDer};
    use bitype::NmTmRule as BiNmTm;
    use bitype::IdxTmRule as BiIdxTm;
    //use std::fmt;
    use std::rc::Rc;
    use super::*;

    /// Name term equivalence rules
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum NmTmRule {
        Refl(NmTmDer),
        Var(Var2),
        Bin(NmTmDec, NmTmDec),
        Lam(Var2,Sort,NmTmDec),
        App(NmTmDec, NmTmDec),
        NoParse(String),
    }
    pub type NmTmDec  = Dec<NmTmRule>;
    impl HasClas for NmTmRule {
        type Clas = Sort;
        fn tm_fam() -> String { "NmTm".to_string() }
    }
    
    /// Index term equivalence rules
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum IdxTmRule {
        Var(Var2),
        Refl(IdxTmDer),
        Sing(NmTmDec),
        Empty,
        Apart(IdxTmDec, IdxTmDec),
        Union(IdxTmDec, IdxTmDec),
        Unit,
        Pair(IdxTmDec, IdxTmDec),
        Proj1(IdxTmDec),
        Proj2(IdxTmDec),
        Lam(Var2, Sort, IdxTmDec),
        App(IdxTmDec, IdxTmDec),
        Map(NmTmDec, IdxTmDec),
        FlatMap(IdxTmDec, IdxTmDec),
        Star(IdxTmDec, IdxTmDec),
        NoParse(String),
    }
    pub type IdxTmDec  = Dec<IdxTmRule>;
    impl HasClas for IdxTmRule {
        type Clas = Sort;
        fn tm_fam () -> String { "IdxTm".to_string() }
    }

    /// Value type equivalence rules
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum TypeRule {
        Refl(Type),
        Var(Var2),
        Sum(TypeDec, TypeDec),
        Prod(TypeDec, TypeDec),
        Ref(IdxTm, TypeDec),
        Thk(IdxTm, CEffectDec),
        IdxApp(TypeDec, IdxTmDec),
        TypeApp(TypeDec, TypeDec),
        Nm(IdxTm),
        NmFn(NameTm),
        TypeFn(Var2, Kind, TypeDec),
        IdxFn(Var2, Sort, TypeDec),
        Rec(Var2, TypeDec),
        Exists(Var2, SortRec, Prop, TypeDec),
        NoParse(String),
    }
    pub type TypeDec  = Dec<TypeRule>;
    impl HasClas for TypeRule {
        type Clas = Kind;
        fn tm_fam() -> String { "Type".to_string() }
    }    

    /// Computation type equivalence rules
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum CEffectRule {
        /// Every term is equal to itself
        Refl(CEffect),
    }
    pub type CEffectDec  = Dec<CEffectRule>;
    impl HasClas for CEffectRule {
        type Clas = Kind;
        fn tm_fam() -> String { "CEffect".to_string() }
    }    


    /// Decide if two name terms are equivalent under the given context
    pub fn decide_nmtm_equiv(ctx: &RelCtx, n:&NmTmDer, m:&NmTmDer, g:&Sort) -> NmTmDec {
        let succ = |r| {
            Dec{
                ctx:ctx.clone(),
                rule:Rc::new(r),
                clas:g.clone(),
                res:Ok(true),
            }
        };
        let fail = |r| {
            Dec{
                ctx:ctx.clone(),
                rule:Rc::new(r),
                clas:g.clone(),
                res:Ok(false),
            }
        };
        let err = |r,e| {
            Dec{
                ctx:ctx.clone(),
                rule:Rc::new(r),
                clas:g.clone(),
                res:Err(e),
            }
        };
        match (&*m.rule,&*n.rule) {
            (mr,nr) if nr == mr => { succ(NmTmRule::Refl(n.clone())) }
            // TODO: all struct cases
            (&BiNmTm::Var(ref v1),&BiNmTm::Var(ref v2)) => {
                if ctx.lookup_nvareq(v1,v2,g) {
                    succ(NmTmRule::Var((v1.clone(),v2.clone())))
                } else {
                    fail(NmTmRule::Var((v1.clone(),v2.clone())))
                }
            }
            (&BiNmTm::Bin(ref m1,ref m2),&BiNmTm::Bin(ref n1,ref n2)) => {
                // Assume sort Nm (they're bins)
                let left = decide_nmtm_equiv(ctx,m1,n1,g);
                let right = decide_nmtm_equiv(ctx,m2,n2,g);
                let (r1,r2) = (left.res.clone(),right.res.clone());
                let der = NmTmRule::Bin(left,right);
                match (r1,r2) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (&BiNmTm::Lam(ref a,ref asort,ref m),&BiNmTm::Lam(ref b,_,ref n)) => {
                // Assume lam vars have same sort
                if let &Sort::NmArrow(ref g1,ref g2) = g {
                    let bodys = decide_nmtm_equiv(&ctx.nt_eq(a,b,g1),m,n,g2);
                    let res = bodys.res.clone();
                    let der = NmTmRule::Lam((a.clone(),b.clone()),asort.clone(),bodys);
                    match res {
                        Ok(true) => succ(der),
                        Ok(false) => fail(der),
                        Err(_) => err(der, DecError::InSubDec)
                    }
                } else {err(
                    NmTmRule::Lam((a.clone(),b.clone()),asort.clone(),
                        decide_nmtm_equiv(ctx,m,n,g)
                    ), DecError::LamNotArrow
                )}
            }
            (&BiNmTm::App(ref m1,ref m2),&BiNmTm::App(ref n1,ref n2)) => {
                // find sort of m1 and n1, assume matching arrows
                let g1 = match (&m1.clas,&n1.clas) {
                    (&Ok(ref g),&Ok(_)) => g,
                    _ => {
                        // error out, using bad types for the recursive decisions
                        let der1 = decide_nmtm_equiv(ctx,m1,n1,g);
                        let der2 = decide_nmtm_equiv(ctx,m2,n2,g);
                        return err(NmTmRule::App(der1, der2),DecError::AppNotArrow)
                    }
                };
                // find sort of m2 and n2, assume matching types
                let g2 = match (&m2.clas,&n2.clas) {
                    (&Ok(ref g),&Ok(_)) => g,
                    _ => {
                        // fail, using bad types for the recursive decisions
                        let der1 = decide_nmtm_equiv(ctx,m1,n1,g1);
                        let der2 = decide_nmtm_equiv(ctx,m2,n2,g);
                        return err(NmTmRule::App(der1, der2),DecError::InSubDec)
                    }
                };
                // assume appropriate types
                let app = decide_nmtm_equiv(ctx,m1,n1,g1);
                let par = decide_nmtm_equiv(ctx,m2,n2,g2);
                let (r1,r2) = (app.res.clone(),par.res.clone());
                let der = NmTmRule::Bin(app,par);
                match (r1,r2) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (_mr, _nr) => {
                // TODO: Non-structural cases
                unimplemented!("decide_nmtm_equiv non-struct")
            }
        }
    }

    /// Decide if two index terms are equivalent under the given context
    pub fn decide_idxtm_equiv(ctx: &RelCtx, i:&IdxTmDer, j:&IdxTmDer, g:&Sort) -> IdxTmDec {
        let succ = |r| {
            Dec{
                ctx:ctx.clone(),
                rule:Rc::new(r),
                clas:g.clone(),
                res:Ok(true),
            }
        };
        let fail = |r| {
            Dec{
                ctx:ctx.clone(),
                rule:Rc::new(r),
                clas:g.clone(),
                res:Ok(false),
            }
        };
        let err = |r,e| {
            Dec{
                ctx:ctx.clone(),
                rule:Rc::new(r),
                clas:g.clone(),
                res:Err(e),
            }
        };
        match (&*i.rule,&*j.rule) {
            (_ir, _jr) if i == j => { succ(IdxTmRule::Refl(i.clone())) }
            // TODO: all struct cases
            (&BiIdxTm::Var(ref v1),&BiIdxTm::Var(ref v2)) => {
                if ctx.lookup_ivareq(v1,v2,g) {
                    succ(IdxTmRule::Var((v1.clone(),v2.clone())))
                } else {
                    fail(IdxTmRule::Var((v1.clone(),v2.clone())))
                }
            }
            (&BiIdxTm::Pair(ref i1,ref i2),&BiIdxTm::Pair(ref j1,ref j2)) => {
                if let &Sort::Prod(ref g1,ref g2) = g {
                    let left = decide_idxtm_equiv(ctx,i1,j1,g1);
                    let right = decide_idxtm_equiv(ctx,i2,j2,g2);
                    let (r1,r2) = (left.res.clone(),right.res.clone());
                    let der = IdxTmRule::Pair(left,right);
                    match (r1,r2) {
                        (Ok(true),Ok(true)) => succ(der),
                        (Ok(_),Ok(_)) => fail(der),
                        (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                    }
                } else {
                    err(IdxTmRule::Pair(
                        decide_idxtm_equiv(ctx,i1,j1,g),
                        decide_idxtm_equiv(ctx,i2,j2,g),
                    ), DecError::PairNotProd)
                }
            }
            (&BiIdxTm::Lam(ref a,ref asort,ref i),&BiIdxTm::Lam(ref b,_,ref j)) => {
                // Assume lam vars have same sort
                if let &Sort::IdxArrow(ref g1,ref g2) = g {
                    let bodys = decide_idxtm_equiv(&ctx.nt_eq(a,b,g1),i,j,g2);
                    let res = bodys.res.clone();
                    let der = IdxTmRule::Lam((a.clone(),b.clone()),asort.clone(),bodys);
                    match res {
                        Ok(true) => succ(der),
                        Ok(false) => fail(der),
                        Err(_) => err(der, DecError::InSubDec)
                    }
                } else { err(
                    IdxTmRule::Lam((a.clone(),b.clone()),asort.clone(),
                        decide_idxtm_equiv(ctx,i,j,g)
                    ), DecError::LamNotArrow
                )}
            }
            (&BiIdxTm::Empty,&BiIdxTm::Empty) => {
                // Assume sort NmSet
                succ(IdxTmRule::Empty)
            }
            (&BiIdxTm::Sing(ref m),&BiIdxTm::Sing(ref n)) => {
                // Assume sort NmSet
                let nder = decide_nmtm_equiv(ctx,m,n,&Sort::Nm);
                let res = nder.res.clone();
                let der = IdxTmRule::Sing(nder);
                match res {
                    Ok(true) => succ(der),
                    Ok(false) => fail(der),
                    Err(_) => err(der, DecError::InSubDec)
                }
            }
            (&BiIdxTm::Apart(ref x1,ref y1),&BiIdxTm::Apart(ref x2,ref y2)) => {
                // Assume sort NmSet
                let left = decide_idxtm_equiv(ctx,x1,x2,&Sort::NmSet);
                let right = decide_idxtm_equiv(ctx,y1,y2,&Sort::NmSet);
                let (l,r) = (left.res.clone(),right.res.clone());
                let der = IdxTmRule::Apart(left,right);
                match (l,r) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (&BiIdxTm::Map(ref m,ref x),&BiIdxTm::Map(ref n,ref y)) => {
                // Assume sort NmSet
                let nmarrow = Sort::NmArrow(Rc::new(Sort::Nm),Rc::new(Sort::Nm));
                let left = decide_nmtm_equiv(ctx,m,n,&nmarrow);
                let right = decide_idxtm_equiv(ctx,x,y,&Sort::NmSet);
                let (l,r) = (left.res.clone(),right.res.clone());
                let der = IdxTmRule::Map(left,right);
                match (l,r) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (_ir, _jr) => {
                // TODO: Non-structural cases
                unimplemented!()
            }
        }
    }

    /// Decide if two type terms are equivalent under the given context
    pub fn decide_type_equiv(ctx: &RelCtx, a:&Type, b:&Type, k:&Kind) -> TypeDec {
        if a == b {
            return Dec{
                ctx:ctx.clone(),
                rule:Rc::new(TypeRule::Refl(a.clone())),
                clas:k.clone(),
                res:Ok(true),
            }
        }
        else {        
            // TODO: the types are not identical, but could still be
            // equivalent.  TODO: Use structural/deductive equiv
            // rules.

            // NOTE #2: This is a low priority over name and index
            // term _apartness_ checks, which are likely to be the
            // most important in many common examples.
            unimplemented!()
        }
    }
}

/// Decide subset relationships over name sets, index terms and types
pub mod subset {
    use ast::*;
    use bitype::{Ctx};
    //use std::fmt;
    use bitype::{IdxTmDer};
    use std::rc::Rc;
    use super::*;

    // XXX
    /// Index term equivalence rules
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum IdxTmRule {
        Var(Var2),
        Refl(IdxTmDer),
        Sing(equiv::NmTmDec),
        Empty,
        Apart(IdxTmDec, IdxTmDec),
        Union(IdxTmDec, IdxTmDec),
        Unit,
        Pair(IdxTmDec, IdxTmDec),
        Proj1(IdxTmDec),
        Proj2(IdxTmDec),
        Lam(Var2, Sort, IdxTmDec),
        App(IdxTmDec, IdxTmDec),
        Map(equiv::NmTmDec, IdxTmDec),
        FlatMap(IdxTmDec, IdxTmDec),
        Star(IdxTmDec, IdxTmDec),
        NoParse(String),
    }
    pub type IdxTmDec  = Dec<IdxTmRule>;
    impl HasClas for IdxTmRule {
        type Clas = Sort;
        fn tm_fam () -> String { "IdxTm".to_string() }
    }

   


    // -------------------------------------------------------------
    
    //TODO: Return a Vec<_>; try each possible decomposition.
    fn find_defs_for_idxtm_var(ctx:&Ctx, x:&Var) -> Option<IdxTm> {
        match ctx {
            &Ctx::Empty => None,
            &Ctx::PropTrue(_, Prop::Equiv(IdxTm::Var(ref x_), ref i,_)) if x == x_ => Some(i.clone()),
            &Ctx::PropTrue(_, Prop::Equiv(ref i, IdxTm::Var(ref x_),_)) if x == x_ => Some(i.clone()),
            _ => find_defs_for_idxtm_var(&*(ctx.rest().unwrap()), x)
        }
    }

    /// Decide if a proposition is true under the given context
    pub fn decide_prop(_ctx: &RelCtx, p:Prop) -> bool {
        unimplemented!("{:?}", p)
    }
    
    /// Decide name set subset relation.
    ///
    /// Return true iff name set `a` is a subset of, or equal to, name set `b`
    pub fn decide_idxtm_subset(ctx: &RelCtx, a:IdxTm, b:IdxTm) -> bool {
        if a == b {
            println!("decide_idxtm_subset:\n  {:?}\n  {:?}\nTRUE(1)!", a, b);           
            return true
        } else {
            // 1a. normalize term `a` under left projection of ctx.
            // 2a. normalize term `b` under right projection of ctx.
            let (ctx1, ctx2) = ctxs_of_relctx((*ctx).clone());
            let a = normal::normal_idxtm(&ctx1, a);
            let b = normal::normal_idxtm(&ctx2, b);

            println!("decide_idxtm_subset:\n  {:?}\n  {:?}\n", a, b);

            if a == b {
                println!("decide_idxtm_subset:\n  {:?}\n  {:?}\nTRUE(2)!", a, b);
                return true
            } else { match b {
                IdxTm::Var(x) => {
                    // If it is possible to subdivide term `b` using
                    // equivalences, then do so. TODO: Return a
                    // Vec<_>; try each possible decomposition.
                    let xdef : Option<IdxTm> = find_defs_for_idxtm_var(&ctx2, &x);
                    match xdef {
                        // Not enough info.
                        None => false,
                        // Use def to try to reason further; TODO:
                        // backtrack if we fail and try next def.
                        Some(xdef) => decide_idxtm_subset(ctx, a, xdef)
                    }
                },
                IdxTm::NmSet(b_ns) => {
                    match a {                        
                        IdxTm::Var(_) => {
                            // Look for the variable in the name set `b_ns`
                            let a_ns_tm = normal::NmSetTm::Subset(a);
                            for b_ns_tm in b_ns.terms.iter() {
                                if b_ns_tm == &a_ns_tm {
                                    println!("decide_idxtm_subset:\n  {:?}\n  {:?}\nTRUE(3)!",
                                             b_ns_tm, a_ns_tm);
                                    return true
                                }
                                else { continue }
                            }
                            return false
                        },
                        IdxTm::NmSet(_a_ns) => {
                            // If the terms normalize, then by
                            // canonical forms, both should each be
                            // NmSets.  For each term in `a`'s
                            // decomposition, attempt to find a
                            // matching (equivalent) term in `b`'s
                            // decomposition.  Each match in `b` may
                            // be used at most once.
                            unimplemented!()
                        }
                        a => panic!("{:?}", a)
                    }
                },
                b => panic!("==================\n {:?}\n ===============\n {:?}", ctx, b)
            }}
        }                                
    }

    /// Decide type subset relation
    pub fn decide_type_subset_rec(ctx: &RelCtx, a:Rc<Type>, b:Rc<Type>) -> bool {
        decide_type_subset(ctx, (*a).clone(), (*b).clone())
    }
    
    /// Decide type subset relation
    pub fn decide_type_subset(ctx: &RelCtx, a:Type, b:Type) -> bool {
        let (ctx1, ctx2) = ctxs_of_relctx((*ctx).clone());
        if a == b { true } else {
            match (a,b) {
                (Type::Var(x), Type::Var(y)) => {
                    ctx.lookup_tvars(&x, &y)
                }
                (Type::Unit, Type::Unit) => true,
                (Type::Sum(a1, a2), Type::Sum(b1, b2)) => {
                    decide_type_subset_rec(ctx, a1, b1) &&
                        decide_type_subset_rec(ctx, a2, b2)
                }
                (Type::Prod(a1,a2), Type::Prod(b1, b2)) => {
                    decide_type_subset_rec(ctx, a1, b1) &&
                        decide_type_subset_rec(ctx, a2, b2)
                }
                (Type::Ref(i, a), Type::Ref(j, b)) => {                    
                    decide_idxtm_subset(ctx, i, j) &&
                        decide_type_subset_rec(ctx, a, b)
                }
                (Type::Thk(i, ce1), Type::Thk(j, ce2)) => {
                    decide_idxtm_subset(ctx, i, j) &&
                        decide_ceffect_subset_rec(ctx, ce1, ce2)
                }
                (Type::IdxApp(a, i), Type::IdxApp(b, j)) => {
                    decide_type_subset_rec(ctx, a, b) &&
                        decide_idxtm_subset(ctx, i, j)
                }
                (Type::TypeApp(a1, b1), Type::TypeApp(a2, b2)) => {
                    decide_type_subset_rec(ctx, a1, a2) &&
                        decide_type_subset_rec(ctx, b1, b2)
                }
                (Type::Nm(i), Type::Nm(j)) => {
                    decide_idxtm_subset(ctx, i, j)
                }
                (Type::NmFn(m), Type::NmFn(n)) => {
                    let n = normal::normal_nmtm(&ctx1, n);
                    let m = normal::normal_nmtm(&ctx2, m);
                    let _nmarrow = fgi_sort![ Nm -> Nm ];
                    // XXX/TODO
                    //super::equiv::decide_nmtm_equiv(ctx, &m, &n, &nmarrow).res
                    //== Ok(true)
                    m == n
                }
                (Type::TypeFn(x1, _k1, a1), Type::TypeFn(x2, _k2, a2)) => {
                    decide_type_subset_rec(
                        &ctx.add_tvars(x1,x2),
                        a1, a2
                    )
                }
                (Type::IdxFn(x1, g1, a1), Type::IdxFn(x2, g2, a2)) => {
                    assert_eq!(g1, g2);
                    decide_type_subset_rec(
                        &ctx.add_ivars(x1,x2,g1),
                        a1, a2
                    )
                }
                // Exists for index-level variables; they are classified by sorts
                (Type::Exists(x1, g1, p1, a1), Type::Exists(x2, g2, p2, a2)) => {
                    // extend ctx with x1 ~~ x2.  Prove: p1 ==> p2 by
                    // extending context with p1, to prove p2. Show
                    // that a1 <= a2.
                    if g1 == g2 {
                        decide_prop(&ctx.prop_true(p1), p2)
                            &&
                            decide_type_subset_rec(&ctx.add_ivars(x1, x2, (*g1).clone()),
                                                   a1, a2)
                    } else {
                        false
                            
                    }
                }
                (Type::Rec(x1, a1), Type::Rec(x2, a2)) => {
                    decide_type_subset_rec(
                        &ctx.add_tvars(x1, x2),
                        a1, a2)
                }                
                (_,_) => false,
            }
        }        
    }

    /// Decide computation type subset relation
    pub fn decide_ctype_subset(ctx: &RelCtx, ct1:CType, ct2:CType) -> bool {
        match (ct1, ct2) {
            (CType::Lift(a), CType::Lift(b)) => {
                decide_type_subset(ctx, a, b)
            }
            (CType::Arrow(a,ce1), CType::Arrow(b,ce2)) => {
                // Arrow's first type parameter is contra-variant
                decide_type_subset(ctx, b, a) &&
                    decide_ceffect_subset_rec(ctx, ce1, ce2)
            }
            _ => false
        }
    }

    /// Decide computation effect subset relation    
    pub fn decide_ceffect_subset(ctx: &RelCtx, ce1:CEffect, ce2:CEffect) -> bool {
        match (ce1, ce2) {
            (CEffect::Cons(ct1, eff1), CEffect::Cons(ct2, eff2)) => {
                decide_ctype_subset(ctx, ct1, ct2) &&
                    decide_effect_subset(ctx, eff1, eff2)
            }
            (CEffect::ForallType(_x1,_k1,_ce1), CEffect::ForallType(_x2,_k2,_ce2)) => {
                // TODO
                unimplemented!()
            }
            (CEffect::ForallIdx(_x1,_g1,_p1,_ce1), CEffect::ForallIdx(_x2,_g2,_p2,_ce2)) => {
                // TODO
                unimplemented!()
            }
            _ => false
        }
    }
    
    /// Decide computation effect subset relation
    pub fn decide_ceffect_subset_rec(ctx: &RelCtx, ce1:Rc<CEffect>, ce2:Rc<CEffect>) -> bool {
        decide_ceffect_subset(ctx, (*ce1).clone(), (*ce2).clone())
    }
    
    /// Decide effect subset relation
    pub fn decide_effect_subset(ctx: &RelCtx, eff1:Effect, eff2:Effect) -> bool {
        match (eff1, eff2) {
            (Effect::WR(w1,r1),Effect::WR(w2,r2)) => {
                decide_idxtm_subset(ctx, w1, w2) &&
                    decide_idxtm_subset(ctx, r1, r2)
            },
            _ => false
        }        
    }

}


/// Decide apartness of two terms (indices, name terms)
pub mod apart {
    //use ast::*;
    use bitype::{HasClas};
    use bitype::{NmTmDer,IdxTmDer};
    //use bitype::NmTmRule as BiNmTm;
    //use bitype::IdxTmRule as BiIdxTm;
    //use std::fmt;
    //use std::rc::Rc;
    use super::*;

    /// Name term apartness rules
    ///
    /// Fig. 24 of https://arxiv.org/abs/1610.00097v5
    ///
    /// Note: Removed D-Proj1 and D-Proj2, which are stale and should
    /// not be there in the rules.
    ///
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum NmTmRule {
        Var(Var2),
        Sym(NmTmDec),
        Trans(equiv::NmTmDec, NmTmDec, NmTmDec),
        Bin1(NmTmDec),
        Bin2(NmTmDec),
        BinEq1(equiv::NmTmDec),
        BinEq2(equiv::NmTmDec),
        Lam(Var2,Sort,NmTmDec),
        App(NmTmDec, NmTmDec),
        Beta(NmTmDer, NmTmDer, NmTmDec),
        NoParse(String),
    }
    pub type NmTmDec  = Dec<NmTmRule>;
    impl HasClas for NmTmRule {
        type Clas = Sort;
        fn tm_fam() -> String { "NmTm".to_string() }
    }
    
    /// One side of an index term apartness
    ///
    /// Fig. 29 of https://arxiv.org/abs/1610.00097v5
    ///
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum IdxTmRule {
        Var(Var2),
        Sym(IdxTmDec),
        Proj1(IdxTmDec),
        Proj2(IdxTmDec),
        Lam(Var2, Sort, IdxTmDec),
        App(IdxTmDec, equiv::IdxTmDec),
        Beta(IdxTmDec, IdxTmDer, IdxTmDer),
        Empty(NmTmDec),
        Single(IdxTmDec),
        Apart(IdxTmDec, IdxTmDec),
        Map(NmTmDec, IdxTmDec),
        FlatMap(IdxTmDec, IdxTmDec),
        Star(IdxTmDec, equiv::IdxTmDec),
        NoParse(String),
    }
    pub type IdxTmDec  = Dec<IdxTmRule>;
    impl HasClas for IdxTmRule {
        type Clas = Sort;
        fn tm_fam () -> String { "IdxTm".to_string() }
    }

    /// Decide if two name terms are apart under the given context
    pub fn decide_nmtm_apart(_ctx: &RelCtx, _n:&NmTmDer, _m:&NmTmDer, _g:&Sort) -> NmTmDec {
        // TODO: Use structural/deductive apartness rules.  Also, do
        // normalization of the name term (aka, beta reduction).
        unimplemented!()
    }

    /// Decide if two index terms are apart under the given context
    pub fn decide_idxtm_apart(_ctx: &RelCtx, _i:&IdxTmDer, _j:&IdxTmDer, _g:&Sort) -> IdxTmDec {
        // TODO: Use structural/deductive apartness rules. Also, do
        // normalization of the index term (aka, beta reduction).
        // Need to be careful not to expand Kleene star indefintely,
        // though. :)
        unimplemented!()
    }

}
