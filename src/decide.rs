/*! Decision procedures for Fungi type and effect system. */

use ast::*;
use bitype::{Ext,Ctx,HasClas,TypeError};
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
    pub fn lookup_type_def(&self, x:&Var) -> Option<Type> {
        self.lookup_bitype_ctx().lookup_type_def(x)
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
            &RelCtx::IVarEquiv(ref c, ref v1, ref v2, ref s) => {
                // TODO: sort compatibility?
                if (x1 == v1) && (x2 == v2) && (g == s) { true }
                else { c.lookup_ivareq(x1,x2,g) }
            }
            c => c.rest().map_or(false,|c|c.lookup_ivareq(x1,x2,g))
        }
    }
    pub fn lookup_nvarapart(&self, x1:&Var, x2:&Var, g:&Sort) -> bool {
        match self {
            &RelCtx::NVarApart(ref c, ref v1, ref v2, ref s) => {
                // TODO: sort compatibility?
                if (x1 == v1) && (x2 == v2) && (g == s) { true }
                else { c.lookup_nvarapart(x1,x2,g) }
            }
            c => c.rest().map_or(false,|c|c.lookup_nvarapart(x1,x2,g))
        }
    }
    pub fn lookup_bitype_ctx(&self) -> Ctx {
        match self {
            &RelCtx::Ctx(ref c) => c.clone(),
            c => c.rest().map_or(Ctx::Empty,|c|c.lookup_bitype_ctx())
        }
    }    
    pub fn lookup_ivarapart(&self, x1:&Var, x2:&Var, g:&Sort) -> bool {
        match self {
            &RelCtx::IVarApart(ref c, ref v1, ref v2, ref s) => {
                // TODO: sort compatibility?
                if (x1 == v1) && (x2 == v2) && (g == s) { true }
                else { c.lookup_ivarapart(x1,x2,g) }
            }
            c => c.rest().map_or(false,|c|c.lookup_ivarapart(x1,x2,g))
        }
    }
}

/// Convert the relational context into the corresponding non-relational context
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
    /// search-based decision procedure fails to find proof of a subset relation
    SubsetSearchFailure(String),
    /// Unknown case of congruence (could be a mismatch)
    UnknownCongruence(IdxTm, IdxTm),
}

/// Derivation for a decision procedure, expressed as deductive inference rules
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct Dec<Rule:HasClas> {
    pub ctx:RelCtx,
    pub rule:Rc<Rule>,
    pub clas:Rule::Clas,
    pub res:Result<bool,DecError>,
}

/// Decide effect relationships
pub mod effect {
    use ast::*;
    use normal;
    use normal::{NmSet,NmSetCons};
    use bitype;
    use bitype::{Ext,Ctx};
    use super::equiv;
    use std::rc::Rc;
    
    /// Computation role, either _Archivist_ or _Editor_.
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum Role {
        Archivist,
        Editor,
    }
    /// Effect-related decision errors
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum Error {
        /// Cannot subtract the second index term from the first
        CannotSubtractFromIdxTm(IdxTm, IdxTm),        
        /// Cannot subtract structure from a variable with unknown structure
        CannotSubtractFromVar(Var, IdxTm),
        /// Cannot subtract a name set term from a name set
        CannotSubtractNmSetTmFromNmSet(normal::NmSet, normal::NmSetTm),
        /// The Archivist cannot subtract the second effect from the first
        CannotSubtract(Effect, Effect),
        /// The Archivist cannot sequence the two effects
        CannotSequence(Effect, Effect),
        /// The Archivist cannot prove that the current effect typing context permits a given read set
        CannotDecideReadSubset(Rc<super::DecError>),
        /// TODO
        TODO
    }

    /// Decide whether a given effect is empty
    pub fn decide_effect_empty(ctx:&Ctx, eff:Effect) -> bool {
        match eff {
            Effect::NoParse(_) => false,
            Effect::WR(IdxTm::Empty, IdxTm::Empty) => true,
            Effect::WR(i, j) => {
                let rctx = super::relctx_of_ctx(ctx);
                let ed = bitype::synth_idxtm(&Ext::empty(), ctx, &IdxTm::Empty);
                let id = bitype::synth_idxtm(&Ext::empty(), ctx, &i);
                let jd = bitype::synth_idxtm(&Ext::empty(), ctx, &j);
                let id = equiv::decide_idxtm_equiv(&rctx, &id, &ed, &Sort::NmSet);
                let jd = equiv::decide_idxtm_equiv(&rctx, &jd, &ed, &Sort::NmSet);
                match (id.res, jd.res) {
                    (Result::Ok(true), Result::Ok(true)) => true,
                    _ => false
                }
            }
        }
    }

    /// Tactic to find an index term `j` such that `NmSet(ns1) == NmSet(ns2) % j`
    pub fn decide_nmset_subtraction(_ctx:&Ctx, ns1:NmSet, ns2:NmSet) -> Result<IdxTm, Error> {
        //println!("decide_nmset_subtraction:\n From:\n\t{:?}\n Subtract:\n\t{:?}", &ns1, &ns2);
        //
        // Step 1: Verify: Before computing subtraction, check
        // that each term in ns1 is really in the set ns1.
        //
        for t2 in ns2.terms.iter() {
            let mut t2_found = false;
            for t1 in ns1.terms.iter() {
                if t1 == t2 { t2_found = true; break }
                else { continue }
            };
            if t2_found { } else {
                println!("^decide_nmset_subtraction: Failure\nFrom:\n\t{:?}\nCannot subtract:\n\t{:?}", &ns1, &t2);
                return Result::Err( Error::CannotSubtractNmSetTmFromNmSet( ns1.clone(), t2.clone() ) )
            }
        };
        //
        // Step 2: Calculate: OK -- All the terms in ns2 are
        // also in ns1.  So, compute the subtraction:
        //
        let mut terms = vec![];
        for t1 in ns1.terms.iter() {
            let mut t1_found = false;
            for t2 in ns2.terms.iter() {
                if t1 == t2 { t1_found = true; break }
                else { continue }                        
            }
            if t1_found { } else {
                terms.push(t1.clone())
            }
        };
        let i_minus_j = IdxTm::NmSet(NmSet{
            cons:Some(NmSetCons::Apart),
            terms:terms,
        });
        //println!("^decide_idxtm_subtraction:\n Success:\n\t{:?}", i_minus_j);
        Result::Ok(i_minus_j)
    }
    
    /// Tactic to find an index term `j2` such that `i = j % j2`
    ///
    /// TODO: "Verify" the results using our decision procedures; return those derivations with the term that we find
    pub fn decide_idxtm_subtraction(ctx:&Ctx, i:IdxTm, j:IdxTm) -> Result<IdxTm, Error> {
        //println!("decide_idxtm_subtraction:\n From:\n\t{:?}\n Subtract:\n\t{:?}", &i, &j);
        let ni = normal::normal_idxtm(ctx, i);
        let nj = normal::normal_idxtm(ctx, j);
        //println!("^decide_idxtm_subtraction:\n From:\n\t{:?}\n Subtract:\n\t{:?}", &ni, &nj);
        match (ni, nj) {
            (IdxTm::Var(x), j) => {
                let xdef = bitype::find_defs_for_idxtm_var(&ctx, &x);
                match xdef {
                    None => {
                        //println!("^decide_idxtm_subtraction: Failure:\n From variable (with no known decomposition):\n\t{:?}\n Cannot subtract index term:\n\t{:?}", &x, &j);
                        Result::Err( Error::CannotSubtractFromVar(x, j) )
                    }
                    Some(xdef) => {
                        //println!("^decide_idxtm_subtraction: Using {:?} == {:?} ...", x, xdef);
                        decide_idxtm_subtraction(ctx, xdef, j)
                    }
                }
            }
            (IdxTm::NmSet(ns1), IdxTm::NmSet(ns2)) => {
                decide_nmset_subtraction(ctx, ns1, ns2)
            }
            (IdxTm::NmSet(ns1), j) => {
                let ns2 = normal::NmSet{cons:None,terms:vec![normal::NmSetTm::Subset(j)]};
                decide_nmset_subtraction(ctx, ns1, ns2)
            }
            (i, j) => {
                println!("^decide_idxtm_subtraction: Failure:\n From index term:\n\t{:?}\n We do not know how to subtract index term:\n\t{:?}", &i, &j);
                Result::Err( Error::CannotSubtractFromIdxTm(i, j) )
            }
        }        
    }
    
    /// Tactic to find the result effect `eff3` such that `eff1 = eff2 then eff3`
    ///
    /// TODO: "Verify" the results using our decision procedures; return those derivations with the term that we find    
    pub fn decide_effect_subtraction(ctx:&Ctx, r:Role, eff1:Effect, eff2:Effect) -> Result<Effect, Error> {
        assert_eq!(r, Role::Archivist);
        if decide_effect_empty(ctx, eff2.clone()) {
            Result::Ok(eff1.clone())
        }
        else {
            //println!("decide_effect_subtraction:\n From:\n\t{:?}\n Subtract:\n\t{:?}", &eff1, &eff2);
            match (eff1.clone(), eff2.clone()) {
                (Effect::WR(wr1, rd1), Effect::WR(wr2, rd2)) => {
                    let wr3 = decide_idxtm_subtraction(ctx, wr1, wr2);
                    use super::subset;
                    let rdsub = subset::decide_idxtm_subset(
                        &super::relctx_of_ctx(ctx),
                        // rd2: Candidate to be the smaller set
                        &rd2,
                        // rd1: Candidate to be the larger set
                        &rd1.clone()
                    );
                    match (wr3, rdsub.res) {
                        (Ok(wr3), Ok(_)) => {
                            let eff3 = Effect::WR(wr3, rd1);
                            //println!("^decide_effect_subtraction:\n Success:\n\t{:?}", &eff3);
                            Ok(eff3)
                        },
                        (Err(err),_) => Result::Err(err),
                        // TODO-someday: gather all errors together
                        (_,Err(err)) => {
                            if false {
                                println!("======================================================= BEGIN");
                                println!("decide_effect_subtraction: Cannot decide read subset:");
                                println!(" Error: {:?}\n", err);
                                println!(" Superset (candidate):\n\t{:?}", &rd1);
                                println!(" Subset (candidate):\n\t{:?}", &rd2);
                                println!("\n\
                                          (If you believe this subset relationship holds, \
                                          Fungi may need additional reasoning in its `decide` \
                                          and/or `normal` modules...)");
                                println!("------------------------------------------------------- END");
                            }
                            Result::Err(Error::CannotDecideReadSubset(Rc::new(err)))
                        },
                    }
                }
                _ => {
                    //println!("^decide_effect_subtraction: Cannot subtract:\n From:\n\t{:?}\n Cannot subtract:\n\t{:?}", &eff1, &eff2);
                    Result::Err( Error::CannotSubtract(eff1, eff2) )
                }
            }
        }
    }

    /// Construct a name set (`i (cons) j`) from name set pair (`i`,`j`) and constructor `cons`.
    pub fn decide_idxtm_cons(_nctx:&Ctx, cons:NmSetCons, i:IdxTm, j:IdxTm) -> Result<IdxTm, Error> {
        match (i,j) {
            (IdxTm::Empty, j) => Ok(j),
            (i, IdxTm::Empty) => Ok(i),
            (i, j) => {
                match cons {
                    NmSetCons::Apart => {
                        // TODO/XXX: Verify that these name sets are apart, where needed.
                        Ok(IdxTm::Apart(Rc::new(i), Rc::new(j)))
                    }
                    NmSetCons::Union => {
                        Ok(IdxTm::Union(Rc::new(i), Rc::new(j)))
                    }
                }
            }
        }
    }

    /// The result effect, if it exists, is `ceffect3` such that `eff1 then ceffect2 = ceffect3`
    pub fn decide_effect_ceffect_sequencing(ctx:&Ctx, r:Role, eff1:Effect, ce2:CEffect) -> Result<CEffect, Error> {
        match ce2 {
            CEffect::Cons(ctype2, eff2) => {
                match decide_effect_sequencing(ctx, r, eff1, eff2) {
                    Err(e) => Err(e),
                    Ok(eff3) => Ok(CEffect::Cons(ctype2, eff3))
                }
            },
            CEffect::ForallType(x,xk,ce) => {
                match decide_effect_ceffect_sequencing(ctx, r, eff1, (*ce).clone()) {
                    Err(e) => Err(e),
                    Ok(ce) => Ok(CEffect::ForallType(x,xk,Rc::new(ce)))
                }
            },
            CEffect::ForallIdx(x,xg,p,ce) => {
                match decide_effect_ceffect_sequencing(ctx, r, eff1, (*ce).clone()) {
                    Err(e) => Err(e),
                    Ok(ce) => Ok(CEffect::ForallIdx(x,xg,p,Rc::new(ce)))
                }
            }
            CEffect::NoParse(s) => Ok(CEffect::NoParse(s)),
        }
    }
    
    /// The result effect, if it exists, is `eff3` such that `eff1 then eff2 = eff3`
    pub fn decide_effect_sequencing(ctx:&Ctx, r:Role, eff1:Effect, eff2:Effect) -> Result<Effect, Error> {
        assert_eq!(r, Role::Archivist);
        if decide_effect_empty(ctx, eff1.clone()) {
            Result::Ok(eff2.clone())
        } else if decide_effect_empty(ctx, eff2.clone()) {
            Result::Ok(eff1.clone())            
        } else { match (eff1.clone(), eff2.clone()) {
            (Effect::WR(wr1, rd1), Effect::WR(wr2, rd2)) => {
                let wr3 = decide_idxtm_cons(ctx, NmSetCons::Apart, wr1, wr2);
                let rd3 = decide_idxtm_cons(ctx, NmSetCons::Union, rd1, rd2);
                match (wr3, rd3) {
                    (Ok(wr3), Ok(rd3)) => {
                        Result::Ok( Effect::WR(wr3, rd3) )                            
                    },
                    _ => {
                        //println!("^decide_effect_sequencing: Cannot sequence:\n Effect 1:\n\t{:?}\n Effect 2:\n\t{:?}", &eff1, &eff2);
                        Result::Err( Error::CannotSequence(eff1, eff2) )
                    }
                }
            }
            _ => {
                //println!("^decide_effect_sequencing: Cannot sequence:\n Effect 1:\n\t{:?}\n Effect 2:\n\t{:?}", &eff1, &eff2);
                Result::Err( Error::CannotSequence(eff1, eff2) )
            }
        }}
    }
}


/// Decide equivalence of two terms (types, indices, name terms)
pub mod equiv {
    //use ast::*;
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
        FailDistinctNames(Name,Name),
        FailNoRule,
    }
    pub type NmTmDec  = Dec<NmTmRule>;    
    impl HasClas for NmTmRule {
        type Term = NameTm;
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
        FlatMapStar(IdxTmDec, IdxTmDec),
        NoParse(String),
        Fail,
    }
    pub type IdxTmDec  = Dec<IdxTmRule>;
    impl HasClas for IdxTmRule {
        type Term = IdxTm;
        type Clas = Sort;
        fn tm_fam () -> String { "IdxTm".to_string() }
    }

    /// Value type equivalence rules
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum TypeRule {
        Refl(Type),
        SubsetNorm(Type,Type),
        Fail,
    }
    pub type TypeDec  = Dec<TypeRule>;
    impl HasClas for TypeRule {
        type Term = Type;
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
        type Term = CEffect;
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
            (&BiNmTm::Name(ref n1),&BiNmTm::Name(ref n2)) => {
                if n1 == n2 {
                    succ(NmTmRule::Refl(m.clone()))
                } else {
                    fail(NmTmRule::FailDistinctNames(n1.clone(), n2.clone()))
                }
            }
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
                    let bodies = decide_nmtm_equiv(&ctx.nt_eq(a,b,g1),m,n,g2);
                    let res = bodies.res.clone();
                    let der = NmTmRule::Lam((a.clone(),b.clone()),asort.clone(),bodies);
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
                let der = NmTmRule::App(app,par);
                match (r1,r2) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (a, b) => {
                println!("Note: Fungi called: decide_nmtm_equiv on non-struct:\n\
                          \t{:?}\n\
                          Versus\n\
                          \t{:?}", a, b);
                fail(NmTmRule::FailNoRule)
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
                    let bodies = decide_idxtm_equiv(&ctx.nt_eq(a,b,g1),i,j,g2);
                    let res = bodies.res.clone();
                    let der = IdxTmRule::Lam((a.clone(),b.clone()),asort.clone(),bodies);
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
            (&BiIdxTm::App(ref i1, ref i2),&BiIdxTm::App(ref j1, ref j2)) => {
                // find sort of i1 and j1, assume matching arrows
                let g1 = match (&i1.clas,&j1.clas) {
                    (&Ok(ref g),&Ok(_)) => g,
                    _ => {
                        // error out, using bad types for the recursive decisions
                        let der1 = decide_idxtm_equiv(ctx,i1,j1,g);
                        let der2 = decide_idxtm_equiv(ctx,i2,j2,g);
                        return err(IdxTmRule::App(der1, der2),DecError::AppNotArrow)
                    }
                };
                // find sort of i2 and j2, assume matching types
                let g2 = match (&i2.clas,&j2.clas) {
                    (&Ok(ref g),&Ok(_)) => g,
                    _ => {
                        // fail, using bad types for the recursive decisions
                        let der1 = decide_idxtm_equiv(ctx,i1,j1,g1);
                        let der2 = decide_idxtm_equiv(ctx,i2,j2,g);
                        return err(IdxTmRule::App(der1, der2),DecError::InSubDec)
                    }
                };
                // assume appropriate types
                let app = decide_idxtm_equiv(ctx,i1,j1,g1);
                let par = decide_idxtm_equiv(ctx,i2,j2,g2);
                let (r1,r2) = (app.res.clone(),par.res.clone());
                let der = IdxTmRule::App(app,par);
                match (r1,r2) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
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
            (&BiIdxTm::FlatMap(ref m,ref x),&BiIdxTm::FlatMap(ref n,ref y)) => {
                // Assume sort NmSet
                let idxarrow = Sort::IdxArrow(Rc::new(Sort::Nm),Rc::new(Sort::NmSet));
                let left = decide_idxtm_equiv(ctx,m,n,&idxarrow);
                let right = decide_idxtm_equiv(ctx,x,y,&Sort::NmSet);
                let (l,r) = (left.res.clone(),right.res.clone());
                let der = IdxTmRule::FlatMap(left,right);
                match (l,r) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (&BiIdxTm::FlatMapStar(ref m,ref x),&BiIdxTm::FlatMapStar(ref n,ref y)) => {
                // Assume sort NmSet
                let idxarrow = Sort::IdxArrow(Rc::new(Sort::Nm),Rc::new(Sort::NmSet));
                let left = decide_idxtm_equiv(ctx,m,n,&idxarrow);
                let right = decide_idxtm_equiv(ctx,x,y,&Sort::NmSet);
                let (l,r) = (left.res.clone(),right.res.clone());
                let der = IdxTmRule::FlatMapStar(left,right);
                match (l,r) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (_ir, _jr) => {
                if false {
                    println!("=============================================================================== BEGIN");
                    println!("decide_idxtm_equiv: Cannot decide this case:\n Left:\n\t{:?}\n Right:\n\t{:?}", i.term, j.term);
                    println!("This case is not implemented; but, it _may_ indicate a type error.");
                    println!("------------------------------------------------------------------------------- END");
                }
                err(IdxTmRule::Fail, DecError::UnknownCongruence((*i.term).clone(), (*j.term).clone()))
            }
        }
    }

    /// Decide if two type terms are equivalent under the given context
    pub fn decide_type_equiv(ctx: &RelCtx, a:&Type, b:&Type, k:&Kind) -> TypeDec {
        // Subcase: "On the nose" equal:
        if a == b {
            return Dec{
                ctx:ctx.clone(),
                rule:Rc::new(TypeRule::Refl(a.clone())),
                clas:k.clone(),
                res:Ok(true),
            }
        }
        else {
            // Subcase: Otherwise, they aren't "on the nose equal",
            // but perhaps we can normalize them, use alpha-reasoning,
            // or use the context somehow to identify them; So, here
            // we reuse the subset reasoning logic, in each direction:
            if subset::decide_type_subset_norm(ctx, a.clone(), b.clone()) &&
                subset::decide_type_subset_norm(ctx, b.clone(), a.clone())
            {
                return Dec{
                    ctx:ctx.clone(),
                    rule:Rc::new(TypeRule::SubsetNorm(a.clone(), b.clone())),
                    clas:k.clone(),
                    res:Ok(true),
                }
            }
            else {
                return Dec{
                    ctx:ctx.clone(),
                    rule:Rc::new(TypeRule::Fail),
                    clas:k.clone(),
                    res:Ok(false),
                }
            }
        }
    }
}

/// Decide subset relationships over name sets, index terms and types
pub mod subset {
    //use ast::*;
    use bitype;
    use bitype::{Ctx};
    //use std::fmt;
    use bitype::{IdxTmDer};
    use std::rc::Rc;
    use super::*;
    use super::equiv::{decide_nmtm_equiv};
    use bitype::IdxTmRule as BiIdxTm;
    use normal::NmSetTm;

    /// Index term equivalence rules
    #[derive(Clone,Debug,Eq,PartialEq,Hash)]
    pub enum IdxTmRule {
        Var(Var2),
        Refl(IdxTmDer),
        Sing(equiv::NmTmDec),
        Empty,
        Apart(IdxTmDec, IdxTmDec),
        Union(IdxTmDec, IdxTmDec),
        Bin(IdxTmDec, IdxTmDec),
        Unit,
        Pair(IdxTmDec, IdxTmDec),
        Proj1(IdxTmDec),
        Proj2(IdxTmDec),
        Lam(Var2, Sort, IdxTmDec),
        App(IdxTmDec, IdxTmDec),
        Map(equiv::NmTmDec, IdxTmDec),
        FlatMap(IdxTmDec, IdxTmDec),
        FlatMapStar(IdxTmDec, IdxTmDec),
        // - - - - - - - - - - - - - - - - -
        SubsetRefl(normal::NmSetTm),
        Subset(normal::NmSet, normal::NmSet),
        NoParse(String),
        Fail,
    }
    pub type IdxTmDec  = Dec<IdxTmRule>;
    impl HasClas for IdxTmRule {
        type Term = IdxTm;
        type Clas = Sort;
        fn tm_fam () -> String { "IdxTm".to_string() }
    }
    
    /// Decide if a proposition is true under the given context
    pub fn decide_prop(_ctx: &RelCtx, p:Prop) -> bool {
        match p {
            Prop::Tt => true,
            _ => { println!("{:?}", p); false }
        }
    }

    // -------------------------------------------------------------
    /// Decide name set subset relation.
    ///
    /// Return true iff name set `i` is a subset of, or equal to, name
    /// set `j`.  Uses `decide_idxtm_congr` as a subroutine.
    //
    pub fn decide_nmsettm_subset(ctx: &RelCtx, tm1:&NmSetTm, tm2:&NmSetTm) -> bool {
        //println!("??????? search ?????????? ------------ BEGIN");
        let res = match (tm1, tm2) {
            (&NmSetTm::Single(ref x), &NmSetTm::Single(ref y)) => {
                // TODO -- use equiv module
                x == y
            },
            (&NmSetTm::Single(ref x), &NmSetTm::Subset(ref y)) => {
                decide_idxtm_subset_simple(ctx, &IdxTm::Sing(x.clone()), y)
            },
            (&NmSetTm::Subset(ref x), &NmSetTm::Single(ref y)) => {
                decide_idxtm_subset_simple(ctx, x, &IdxTm::Sing(y.clone()))
            },
            (&NmSetTm::Subset(ref x), &NmSetTm::Subset(ref y)) => {
                decide_idxtm_subset_simple(ctx, x, y)
            }
        };
        //println!("??????? search ?????????? ----------- END");
        res
    }
    
    // -------------------------------------------------------------
    /// Decide name set subset relation.
    ///
    /// Return true iff name set `i` is a subset of, or equal to, name
    /// set `j`.  Uses `decide_idxtm_congr` as a subroutine.
    pub fn decide_idxtm_subset(ctx: &RelCtx, i:&IdxTm, j:&IdxTm) -> IdxTmDec
    {
        // Normalize `i` and `j` as `a` and `b`, respectively
        let (ctx1, ctx2) = ctxs_of_relctx((*ctx).clone());

        let a     = normal::normal_idxtm(&ctx1, i.clone());
        let a_bit = bitype::synth_idxtm(&Ext::empty(), &ctx1, &a);

        let b     = normal::normal_idxtm(&ctx2, j.clone());
        let b_bit = bitype::synth_idxtm(&Ext::empty(), &ctx2, &b);

        // Basecase: "On the nose" equality.
        //
        // TODO: Use equiv module instead, to relate alpha-equiv terms.
        if a == b {
            return Dec{
                ctx:ctx.clone(),
                rule:Rc::new(IdxTmRule::Refl(b_bit)),
                clas:Sort::NmSet,
                res:Ok(true)
            }
        } else { match b.clone() {
            // Else: The terms are not equal, but perhaps they are:
            //
            // 1.  Related as propositions of the form `(x = x1%x2)
            //     true` in the _unary context_, where each of `x1` and
            //     `x2` is related to `x` by the equation.
            //
            // 2.  Related by assumed equivalences of the form `x1 == x2 :
            //     NmSet` in the _relational context_.
            //
            // 3.  Related by the "larger" set being a caonical form name set
            //     (`normal::NmSet`), with the smaller set as one of
            //     its subterms.
            //
            // 4.  Each sets in caonical form, as name sets
            //     (`normal::NmSet`), with the smaller set as a subset of
            //     the larger set.
            //
            // 5.  Related in some other way (?)
            //
            //
            // TODO-Someday: Create IdxTmDec rules for the different cases above.
            //
            IdxTm::Var(x) => {
                // Subcase 1: subdivide term for `x` using
                // propositions.  For each, try to find a subset
                // relationship.  TODO: Return a Vec<_>; try each
                // possible decomposition.
                fn simple_solver(ctx:&RelCtx,ctx2:&Ctx,a:IdxTm,x:&String) -> IdxTmDec {
                    let xdef : Option<IdxTm> = bitype::find_defs_for_idxtm_var(&ctx2, &x);
                    match xdef {
                        // Not enough info.
                        None => {
                            //println!("No defs for {}, looking for subset:\t\n{:?}", x, &a);
                            //panic!("TODO: {:?}", ctx)
                            return Dec{
                                ctx:ctx.clone(),
                                rule:Rc::new(IdxTmRule::Fail),
                                clas:Sort::NmSet,
                                res:Err(DecError::SubsetSearchFailure(format!("Subcase-1")))
                            }
                        }
                        // Use def to try to reason further; TODO:
                        // backtrack if we fail and try next def.
                        Some(xdef) => {
                            decide_idxtm_subset(ctx, &a, &xdef)
                        }
                    }
                };
                if let IdxTm::Var(y) = a.clone() {
                    if ctx.lookup_ivareq(&y, &x, &Sort::NmSet) {
                        // Subcase 2: Both terms are variables, and
                        // they are related in the relational `ctx`.
                        return Dec{
                            ctx:ctx.clone(),
                            rule:Rc::new(IdxTmRule::Var((x, y))),
                            clas:Sort::NmSet,
                            res:Ok(true),
                        }
                    } else { simple_solver(&ctx,&ctx2,a,&x) }
                } else { simple_solver(&ctx,&ctx2,a,&x) }
            },
            // Subcase 3:  The "larger" set is a caonical form name
            // set (`normal::NmSet`), with the smaller set as a
            // subterm.
            IdxTm::NmSet(b_ns) => {
                match a {                        
                    IdxTm::Var(_) => {
                        // Look for the variable in the name set `b_ns`
                        let a_ns_tm = normal::NmSetTm::Subset(a);
                        for b_ns_tm in b_ns.terms.iter() {
                            if b_ns_tm == &a_ns_tm {
                                //println!("decide_idxtm_subset:\n  {:?}\n  {:?}\nTRUE(3)!",
                                //b_ns_tm, a_ns_tm);
                                return Dec{
                                    ctx:ctx.clone(),
                                    rule:Rc::new(IdxTmRule::SubsetRefl(a_ns_tm)),
                                    clas:Sort::NmSet,
                                    res:Ok(true)
                                }
                            }
                            else { continue }
                        }
                        return Dec{
                            ctx:ctx.clone(),
                            rule:Rc::new(IdxTmRule::Fail),
                            clas:Sort::NmSet,
                            res:Err(DecError::SubsetSearchFailure(format!("Subcase-3")))
                        }
                    },
                    IdxTm::NmSet(a_ns) => {                        
                        // Subcase 4: Check subset relationship, at
                        // the "term" level: If the terms normalize,
                        // then by canonical forms, both should each
                        // be NmSets.
                        //
                        // For each term in `a`'s decomposition,
                        // attempt to find a matching (equivalent)
                        // term in `b`'s decomposition.  Each match in
                        // `b` may be used at most once.
                        for tm1 in a_ns.terms.iter() {
                            let mut found_tm1 = false;
                            for tm2 in b_ns.terms.iter() {
                                // XXX -- Too strong: Use subset check here:
                                if tm1 == tm2 ||
                                    decide_nmsettm_subset(ctx, tm1, tm2)
                                {
                                    found_tm1 = true;
                                }
                            }
                            if found_tm1 { continue } else {
                                if true {
                                    println!("Subcase-4: Term not found in superset candidate:\n\
                                              \t`{:?}`\n\
                                          Not found among:\n\
                                          \t`{:?}`", tm1, b_ns.terms);
                                }
                                return Dec{
                                    ctx:ctx.clone(),
                                    rule:Rc::new(IdxTmRule::Fail),
                                    clas:Sort::NmSet,
                                    res:Err(DecError::SubsetSearchFailure(
                                        format!("Subcase-4: Term not found in superset candidate:\n\
                                                 \t`{:?}`\n\n\
                                                 Not found among:\n\
                                                 \t`{:?}`", tm1, b_ns.terms)))
                                }
                            }
                        };
                        return Dec{
                            ctx:ctx.clone(),
                            rule:Rc::new(IdxTmRule::Subset(a_ns, b_ns)),
                            clas:Sort::NmSet,
                            res:Ok(true)
                        }
                    }
                    // Subcase 5: "Other: Say 'No'"
                    a => {
                        if false {
                            println!("======================================================= BEGIN");
                            println!("decide_idxtm_subset: Cannot decide subset:");
                            println!(" Superset (candidate):\n\t{:?}", &b);
                            println!(" Subset (candidate):\n\t{:?}", &a);
                            println!("\n\
                                      (If you believe this subset relationship holds, \
                                      Fungi may need additional reasoning in its `decide` \
                                      and/or `normal` modules...)");
                            println!("------------------------------------------------------- END");
                        };
                        return Dec{
                            ctx:ctx.clone(),
                            rule:Rc::new(IdxTmRule::Fail),
                            clas:Sort::NmSet,
                            res:Err(DecError::SubsetSearchFailure(format!("Subcase-5")))
                        }}                    
                }
            },
            _ => decide_idxtm_subset_congr (
                ctx,
                &a_bit, &b_bit,
                &Sort::NmSet
            )
        }}
    }

    /// Decide type subset relation
    pub fn decide_type_subset_rec(ctx: &RelCtx, a:Rc<Type>, b:Rc<Type>) -> bool {
        decide_type_subset(ctx, (*a).clone(), (*b).clone())
    }
    
    /// Decide if two index terms are congruent under the given context
    fn decide_idxtm_subset_congr(ctx: &RelCtx, i:&IdxTmDer, j:&IdxTmDer, g:&Sort) -> IdxTmDec {
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
            (_ir, _jr) if i == j => {
                succ(IdxTmRule::Refl(i.clone()))
            }
            (&BiIdxTm::Empty, _) => {
                // Empty is a subset of everything else
                succ(IdxTmRule::Empty)
            }
            (&BiIdxTm::Var(ref v1),&BiIdxTm::Var(ref v2)) => {
                if ctx.lookup_ivareq(v1,v2,g) {
                    succ(IdxTmRule::Var((v1.clone(),v2.clone())))
                } else {
                    fail(IdxTmRule::Var((v1.clone(),v2.clone())))
                }
            }
            (&BiIdxTm::Pair(ref i1,ref i2),&BiIdxTm::Pair(ref j1,ref j2)) => {
                if let &Sort::Prod(ref g1,ref g2) = g {
                    let left = decide_idxtm_subset_congr(ctx,i1,j1,g1);
                    let right = decide_idxtm_subset_congr(ctx,i2,j2,g2);
                    let (r1,r2) = (left.res.clone(),right.res.clone());
                    let der = IdxTmRule::Pair(left,right);
                    match (r1,r2) {
                        (Ok(true),Ok(true)) => succ(der),
                        (Ok(_),Ok(_)) => fail(der),
                        (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                    }
                } else {
                    err(IdxTmRule::Pair(
                        decide_idxtm_subset_congr(ctx,i1,j1,g),
                        decide_idxtm_subset_congr(ctx,i2,j2,g),
                    ), DecError::PairNotProd)
                }
            }
            (&BiIdxTm::Lam(ref a,ref asort,ref i),&BiIdxTm::Lam(ref b,_,ref j)) => {
                // Assume lam vars have same sort
                if let &Sort::IdxArrow(ref g1,ref g2) = g {
                    let bodies = decide_idxtm_subset_congr(&ctx.nt_eq(a,b,g1),i,j,g2);
                    let res = bodies.res.clone();
                    let der = IdxTmRule::Lam((a.clone(),b.clone()),asort.clone(),bodies);
                    match res {
                        Ok(true) => succ(der),
                        Ok(false) => fail(der),
                        Err(_) => err(der, DecError::InSubDec)
                    }
                } else { err(
                    IdxTmRule::Lam((a.clone(),b.clone()),asort.clone(),
                        decide_idxtm_subset_congr(ctx,i,j,g)
                    ), DecError::LamNotArrow
                )}
            }
            (&BiIdxTm::App(ref i1, ref i2),&BiIdxTm::App(ref j1, ref j2)) => {
                // find sort of i1 and j1, assume matching arrows
                let g1 = match (&i1.clas,&j1.clas) {
                    (&Ok(ref g),&Ok(_)) => g,
                    _ => {
                        // error out, using bad types for the recursive decisions
                        let der1 = decide_idxtm_subset_congr(ctx,i1,j1,g);
                        let der2 = decide_idxtm_subset_congr(ctx,i2,j2,g);
                        return err(IdxTmRule::App(der1, der2),DecError::AppNotArrow)
                    }
                };
                // find sort of i2 and j2, assume matching types
                let g2 = match (&i2.clas,&j2.clas) {
                    (&Ok(ref g),&Ok(_)) => g,
                    _ => {
                        // fail, using bad types for the recursive decisions
                        let der1 = decide_idxtm_subset_congr(ctx,i1,j1,g1);
                        let der2 = decide_idxtm_subset_congr(ctx,i2,j2,g);
                        return err(IdxTmRule::App(der1, der2),DecError::InSubDec)
                    }
                };
                // assume appropriate types
                let app = decide_idxtm_subset_congr(ctx,i1,j1,g1);
                let par = decide_idxtm_subset_congr(ctx,i2,j2,g2);
                let (r1,r2) = (app.res.clone(),par.res.clone());
                let der = IdxTmRule::App(app,par);
                match (r1,r2) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
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
                let left = decide_idxtm_subset_congr(ctx,x1,x2,&Sort::NmSet);
                let right = decide_idxtm_subset_congr(ctx,y1,y2,&Sort::NmSet);
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
                let right = decide_idxtm_subset(ctx, &*x.term, &*y.term);
                let (l,r) = (left.res.clone(),right.res.clone());
                let der = IdxTmRule::Map(left,right);
                match (l,r) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (&BiIdxTm::FlatMap(ref i1, ref j1),&BiIdxTm::FlatMap(ref i2, ref j2)) => {
                let nmsetarrow = Sort::IdxArrow(Rc::new(Sort::NmSet),Rc::new(Sort::NmSet));
                let left = decide_idxtm_subset_congr(ctx,i1,i2,&nmsetarrow);
                let right = decide_idxtm_subset(ctx, &*j1.term, &*j2.term);
                let (l,r) = (left.res.clone(),right.res.clone());
                let der = IdxTmRule::FlatMap(left,right);
                match (l,r) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (&BiIdxTm::Bin(ref i1,ref i2),&BiIdxTm::Bin(ref j1,ref j2)) => {
                let left = decide_idxtm_subset(ctx,&*i1.term,&*j1.term);
                let right = decide_idxtm_subset(ctx,&*i2.term,&*j2.term);
                let (r1,r2) = (left.res.clone(),right.res.clone());
                let der = IdxTmRule::Bin(left,right);
                match (r1,r2) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (&BiIdxTm::FlatMapStar(ref _i1, ref _j1),&BiIdxTm::FlatMapStar(ref _i2, ref _j2)) => {
                unimplemented!()
            }
            (_, _) => {
                if false {
                    println!("=============================================================================== BEGIN");
                    println!("decide_idxtm_subset: Cannot decide this case:\n Left:\n\t{:?}\n Right:\n\t{:?}", i.term, j.term);
                    println!("This case is not implemented; but, it _may_ indicate a type error.");
                    println!("------------------------------------------------------------------------------- END");
                }
                err(IdxTmRule::Fail, DecError::UnknownCongruence((*i.term).clone(), (*j.term).clone()))
            }
        }
    }

    /// Decide name set subset relation.
    ///
    /// Wraps `decide_idxtm_subset` with a simpler output type.
    //
    pub fn decide_idxtm_subset_simple(ctx: &RelCtx, i:&IdxTm, j:&IdxTm) -> bool
    {
        let d = decide_idxtm_subset(ctx, &i, &j);
        if d.res == Ok(true) {
            //println!("decide_idxtm_subset: success:\n\t{:?}\n\t{:?}", i, j);
            return true
        }
        else {
            //println!("decide_idxtm_subset: failed:\n\t{:?}\n\t{:?}", i, j);
            return false
        }
    }
    
    /// Decide type subset relation on normalized versions of the given terms.
    pub fn decide_type_subset_norm(ctx: &RelCtx, a:Type, b:Type) -> bool {
        // TODO-someday: Make this operation cheaper somehow (use traits in a clever way?)
        let (ctx1, ctx2) = ctxs_of_relctx((*ctx).clone());
        let a = normal::normal_type(&ctx1, &a);
        let b = normal::normal_type(&ctx2, &b);
        //println!("decide_type_subset_norm: BEGIN:\n\t{:?}\n\t{:?}", a, b);
        decide_type_subset(ctx, a, b)
    }

    /// Decide type subset relation
    pub fn decide_type_subset(ctx: &RelCtx, a:Type, b:Type) -> bool {
        if a == b { true } else {
            match (a,b) {
                (Type::Ident(x), b) => {
                    match ctx.lookup_type_def(&x) {
                        None => false,
                        Some(a) => decide_type_subset(ctx, a, b)
                    }
                }
                (a, Type::Ident(y)) => {
                    match ctx.lookup_type_def(&y) {
                        None => false,
                        Some(b) => decide_type_subset(ctx, a, b)
                    }
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
                    decide_idxtm_subset_simple(ctx, &i, &j) &&
                        decide_type_subset_rec(ctx, a, b)
                }
                (Type::Thk(i, ce1), Type::Thk(j, ce2)) => {
                    decide_idxtm_subset_simple(ctx, &i, &j) &&
                        decide_ceffect_subset_rec(ctx, ce1, ce2)
                }
                (Type::IdxApp(a, i), Type::IdxApp(b, j)) => {
                    decide_type_subset_rec(ctx, a, b) &&
                        decide_idxtm_subset_simple(ctx, &i, &j)
                }
                (Type::TypeApp(a1, b1), Type::TypeApp(a2, b2)) => {
                    decide_type_subset_rec(ctx, a1, a2) &&
                        decide_type_subset_rec(ctx, b1, b2)
                }
                (Type::Nm(i), Type::Nm(j)) => {
                    decide_idxtm_subset_simple(ctx, &i, &j)
                }
                (Type::NmFn(m), Type::NmFn(n)) => {
                    if m == n { true }
                    else {
                        let (ctx1, ctx2) = ctxs_of_relctx(ctx.clone());
                        let n = normal::normal_nmtm(&ctx1, n);
                        let m = normal::normal_nmtm(&ctx2, m);
                        let _nmarrow = fgi_sort![ Nm -> Nm ];
                        // TODO-Someday:
                        //super::equiv::decide_nmtm_equiv(ctx, &m, &n, &nmarrow).res
                        //== Ok(true)
                        m == n
                    }
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
                (Type::Exists(x1, g1, _p1, a1), Type::Exists(x2, g2, _p2, a2)) => {
                    // extend ctx with x1 ~~ x2.  Prove: p1 ==> p2 by
                    // extending context with p1, to prove p2. Show
                    // that a1 <= a2.
                    if g1 == g2 {
                        // XXX/TODO
                        //decide_prop(&ctx.prop_true(p1), p2)
                        //&&
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
            (Effect::WR(ref w1, ref r1),Effect::WR(ref w2, ref r2)) => {
                let wd = decide_idxtm_subset(ctx, w1, w2);
                let rd = decide_idxtm_subset(ctx, r1, r2);
                match (wd.res, rd.res) {
                    (Ok(true),Ok(true)) => true,
                    _ => false,
                }
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
    use bitype::NmTmRule as BiNmTm;
    use bitype::IdxTmRule as BiIdxTm;
    //use std::fmt;
    //use std::rc::Rc;
    use super::*;

    /// Name term apartness rules
    ///
    /// Fig. 24 of https://arxiv.org/abs/1610.00097v5
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
        App(NmTmDec, equiv::NmTmDec),
        Beta(NmTmDer, NmTmDer, NmTmDec),
        NoParse(String),
    }
    pub type NmTmDec  = Dec<NmTmRule>;
    impl HasClas for NmTmRule {
        type Term = NameTm;
        type Clas = Sort;
        fn tm_fam() -> String { "NmTm".to_string() }
    }
    
    /// Index term apartness rules
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
        Sing(NmTmDec),
        Apart(IdxTmDec, IdxTmDec),
        Map(NmTmDec, equiv::IdxTmDec),
        FlatMap(IdxTmDec, IdxTmDec),
        FlatMapStar(IdxTmDec, equiv::IdxTmDec),
        NoParse(String),
    }
    pub type IdxTmDec  = Dec<IdxTmRule>;
    impl HasClas for IdxTmRule {
        type Term = IdxTm;
        type Clas = Sort;
        fn tm_fam () -> String { "IdxTm".to_string() }
    }

    /// Decide if two name terms are apart under the given context
    pub fn decide_nmtm_apart(ctx: &RelCtx, n:&NmTmDer, m:&NmTmDer, g:&Sort) -> NmTmDec {
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
            (&BiNmTm::Var(ref v1),&BiNmTm::Var(ref v2)) => {
                if ctx.lookup_nvarapart(v1,v2,g) {
                    succ(NmTmRule::Var((v1.clone(),v2.clone())))
                } else {
                    fail(NmTmRule::Var((v1.clone(),v2.clone())))
                }
            }
            (&BiNmTm::Bin(ref m1, ref m2),nr) => {
                // TODO: check and report error cases?
                let t1_der = equiv::decide_nmtm_equiv(ctx, m1, n, &Sort::Nm);
                if Ok(true) == t1_der.res { return succ(NmTmRule::BinEq1(t1_der)) };
                let t2_der = equiv::decide_nmtm_equiv(ctx, m2, n, &Sort::Nm);
                if Ok(true) == t2_der.res { return succ(NmTmRule::BinEq2(t2_der)) };
                if let &BiNmTm::Bin(ref n1, ref n2) = nr {
                    let b1_der = decide_nmtm_apart(ctx, m1, n1, &Sort::Nm);
                    if Ok(true) == b1_der.res { return succ(NmTmRule::Bin1(b1_der)) };
                    let b2_der = decide_nmtm_apart(ctx, m2, n2, &Sort::Nm);
                    if Ok(true) == b2_der.res { return succ(NmTmRule::Bin1(b2_der)) };
                    fail(NmTmRule::Bin1(b1_der))
                } else {
                    fail(NmTmRule::BinEq1(t1_der))
                }
            }
            (&BiNmTm::Lam(ref a,ref asort,ref m),&BiNmTm::Lam(ref b,_,ref n)) => {
                // Assume lam vars have same sort
                if let &Sort::NmArrow(ref g1,ref g2) = g {
                    let bodies = decide_nmtm_apart(&ctx.nt_eq(a,b,g1),m,n,g2);
                    let res = bodies.res.clone();
                    let der = NmTmRule::Lam((a.clone(),b.clone()),asort.clone(),bodies);
                    match res {
                        Ok(true) => succ(der),
                        Ok(false) => fail(der),
                        Err(_) => err(der, DecError::InSubDec)
                    }
                } else {err(
                    NmTmRule::Lam((a.clone(),b.clone()),asort.clone(),
                        decide_nmtm_apart(ctx,m,n,g)
                    ), DecError::LamNotArrow
                )}
            }
            (&BiNmTm::App(ref m1,ref m2),&BiNmTm::App(ref n1,ref n2)) => {
                // find sort of m1 and n1, assume matching arrows
                let g1 = match (&m1.clas,&n1.clas) {
                    (&Ok(ref g),&Ok(_)) => g,
                    _ => {
                        // error out, using bad types for the recursive decisions
                        let der1 = decide_nmtm_apart(ctx,m1,n1,g);
                        let der2 = equiv::decide_nmtm_equiv(ctx,m2,n2,g);
                        return err(NmTmRule::App(der1, der2),DecError::AppNotArrow)
                    }
                };
                // find sort of m2 and n2, assume matching types
                let g2 = match (&m2.clas,&n2.clas) {
                    (&Ok(ref g),&Ok(_)) => g,
                    _ => {
                        // fail, using bad types for the recursive decisions
                        let der1 = decide_nmtm_apart(ctx,m1,n1,g1);
                        let der2 = equiv::decide_nmtm_equiv(ctx,m2,n2,g);
                        return err(NmTmRule::App(der1, der2),DecError::InSubDec)
                    }
                };
                // assume appropriate types
                let app = decide_nmtm_apart(ctx,m1,n1,g1);
                let par = equiv::decide_nmtm_equiv(ctx,m2,n2,g2);
                let (r1,r2) = (app.res.clone(),par.res.clone());
                let der = NmTmRule::App(app,par);
                match (r1,r2) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (a,b) => {
                println!("decide_nmtm_apart non-struct:\n\
                          \t{:?}\n\
                          Versus\n\
                          \t{:?}", a, b);
                panic!("XXX");
            }
        }
    }

    /// Decide if two index terms are apart under the given context
    pub fn decide_idxtm_apart(ctx: &RelCtx, i:&IdxTmDer, j:&IdxTmDer, g:&Sort) -> IdxTmDec {
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
            (&BiIdxTm::Var(ref v1),&BiIdxTm::Var(ref v2)) => {
                if ctx.lookup_ivarapart(v1,v2,g) {
                    succ(IdxTmRule::Var((v1.clone(),v2.clone())))
                } else {
                    fail(IdxTmRule::Var((v1.clone(),v2.clone())))
                }
            }
            (&BiIdxTm::Pair(ref i1,ref i2),&BiIdxTm::Pair(ref j1,ref j2)) => {
                if let &Sort::Prod(ref g1,ref g2) = g {
                    let left = decide_idxtm_apart(ctx,i1,j1,g1);
                    if Ok(true) == left.res { return succ(IdxTmRule::Proj1(left)) }
                    let right = decide_idxtm_apart(ctx,i2,j2,g2);
                    if Ok(true) == right.res { return succ(IdxTmRule::Proj2(right)) }
                    // TODO: check for and return errors?
                    fail(IdxTmRule::Proj1(left))
                } else {
                    err(IdxTmRule::Proj1(
                        decide_idxtm_apart(ctx,i1,j1,g),
                    ), DecError::PairNotProd)
                }
            }
            (&BiIdxTm::Lam(ref a,ref asort,ref i),&BiIdxTm::Lam(ref b,_,ref j)) => {
                // Assume lam vars have same sort
                if let &Sort::IdxArrow(ref g1,ref g2) = g {
                    let bodies = decide_idxtm_apart(&ctx.nt_eq(a,b,g1),i,j,g2);
                    let res = bodies.res.clone();
                    let der = IdxTmRule::Lam((a.clone(),b.clone()),asort.clone(),bodies);
                    match res {
                        Ok(true) => succ(der),
                        Ok(false) => fail(der),
                        Err(_) => err(der, DecError::InSubDec)
                    }
                } else { err(
                    IdxTmRule::Lam((a.clone(),b.clone()),asort.clone(),
                        decide_idxtm_apart(ctx,i,j,g)
                    ), DecError::LamNotArrow
                )}
            }
            (&BiIdxTm::App(ref i1,ref i2),&BiIdxTm::App(ref j1,ref j2)) => {
                // find sort of i1 and j1, assume matching arrows
                let g1 = match (&i1.clas,&j1.clas) {
                    (&Ok(ref g),&Ok(_)) => g,
                    _ => {
                        // error out, using bad types for the recursive decisions
                        let der1 = decide_idxtm_apart(ctx,i1,j1,g);
                        let der2 = equiv::decide_idxtm_equiv(ctx,i2,j2,g);
                        return err(IdxTmRule::App(der1, der2),DecError::AppNotArrow)
                    }
                };
                // find sort of i2 and j2, assume matching types
                let g2 = match (&i2.clas,&j2.clas) {
                    (&Ok(ref g),&Ok(_)) => g,
                    _ => {
                        // fail, using bad types for the recursive decisions
                        let der1 = decide_idxtm_apart(ctx,i1,j1,g1);
                        let der2 = equiv::decide_idxtm_equiv(ctx,i2,j2,g);
                        return err(IdxTmRule::App(der1, der2),DecError::InSubDec)
                    }
                };
                // assume appropriate types
                let app = decide_idxtm_apart(ctx,i1,j1,g1);
                let par = equiv::decide_idxtm_equiv(ctx,i2,j2,g2);
                let (r1,r2) = (app.res.clone(),par.res.clone());
                let der = IdxTmRule::App(app,par);
                match (r1,r2) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (&BiIdxTm::Empty,_jr) => {
                // TODO: How does this work?
                unimplemented!("decide_idxtm_apart empty")
            }
            (&BiIdxTm::Sing(ref m),&BiIdxTm::Sing(ref n)) => {
                // Assume sort NmSet
                let nder = decide_nmtm_apart(ctx,m,n,&Sort::Nm);
                let res = nder.res.clone();
                let der = IdxTmRule::Sing(nder);
                match res {
                    Ok(true) => succ(der),
                    Ok(false) => fail(der),
                    Err(_) => err(der, DecError::InSubDec)
                }
            }
            (&BiIdxTm::Apart(ref x1,ref x2),_) => {
                // Assume sort NmSet
                let left = decide_idxtm_apart(ctx,x1,j,&Sort::NmSet);
                let right = decide_idxtm_apart(ctx,x2,j,&Sort::NmSet);
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
                let left = decide_nmtm_apart(ctx,m,n,&nmarrow);
                let right = equiv::decide_idxtm_equiv(ctx,x,y,&Sort::NmSet);
                let (l,r) = (left.res.clone(),right.res.clone());
                let der = IdxTmRule::Map(left,right);
                match (l,r) {
                    (Ok(true),Ok(true)) => succ(der),
                    (Ok(_),Ok(_)) => fail(der),
                    (Err(_),_ ) | (_,Err(_)) => err(der, DecError::InSubDec)
                }
            }
            (_ir, _jr) => {
                unimplemented!("decide_idxtm_apart non-struct")
            }
        }
    }

}
