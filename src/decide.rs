/*! Decision procedures for Fungi type and effect system. */

use crate::{ast::*, bitype::{Ext,Ctx,HasClas,TypeError}, normal, display};
use std::rc::Rc;

/// Pair of related variables
pub type Var2 = (Var, Var);

/// Relational typing context: Relates pairs of variables, terms, etc
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
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
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub enum DecError {
    /// Type/sort/kind error during the decision procedure
    TypeError(TypeError),
    InSubDec,
    LamNotArrow,
    AppNotArrow,
    PairNotProd,
    /// search-based decision procedure fails to find proof of a subset relation
    SubsetSearchFailureMisc(String),
    /// search-based decision procedure fails to find proof of a membership/subset relation for a name set term
    SubsetSearchFailureTm(normal::NmSetTm,normal::NmSet),
    /// search-based decision procedure fails to find proof of a membership/subset relation for a name set term
    SubsetSearchFailure(IdxTm,IdxTm),
    /// Unknown case of congruence (could be a mismatch)
    UnknownCongruence(IdxTm, IdxTm),
}

/// Derivation for a decision procedure, expressed as deductive inference rules
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
pub struct Dec<Rule:HasClas> {
    pub ctx:RelCtx,
    pub rule:Rc<Rule>,
    pub clas:Rule::Clas,
    pub res:Result<bool,DecError>,
}

/// Decide effect relationships
pub mod effect {
    use crate::{
        ast::*, normal, normal::{NmSet,NmSetCons}, bitype, bitype::{Ext,Ctx}, 
        decide::equiv, vt100,
    };
    use std::rc::Rc;
    
    /// Computation role, either _Archivist_ or _Editor_.
    #[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
    pub enum Role {
        Archivist,
        Editor,
    }
    /// Effect-related decision errors
    #[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
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
                let idz = equiv::decide_idxtm_equiv(&rctx, &id, &ed, &Sort::NmSet);
                let jdz = equiv::decide_idxtm_equiv(&rctx, &jd, &ed, &Sort::NmSet);
                match (idz.res, jdz.res) {
                    (Result::Ok(true), Result::Ok(true)) => true,
                    _ => false
                }
            }
        }
    }

    /// Tactic to find an index term `j` such that `NmSet(ns1) == NmSet(ns2) % j`
    pub fn decide_nmset_subtraction(ctx:&Ctx, ns1:NmSet, ns2:NmSet) -> Result<IdxTm, Error> {
        fgi_db!("^decide_nmset_subtraction: from {}, subtract {}", &ns1, &ns2);
        db_region_open!(false, crate::vt100::DecideBracket);
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
                fgi_db!("^decide_nmset_subtraction: Failure\nFrom:\n\t{}\nCannot subtract:\n\t{}", &ns1, &t2);
                db_region_close!();
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
        fgi_db!("^decide_idxtm_subtraction: holds: {} ⊢ {} - {} ≡ {} : NmSet",
                ctx, ns1, ns2, i_minus_j);
        db_region_close!();
        Result::Ok(i_minus_j)
    }
    
    pub fn test_idxtm_equiv(ctx:&Ctx, i:&IdxTm, j:&IdxTm) -> bool {
        fgi_db!("decide if {} ⊢ {} ≡ {} : NmSet", ctx, i, j);
        db_region_open!(false, crate::vt100::DecideBracket);
        let id = bitype::synth_idxtm(&Ext::empty(), ctx, i);
        let jd = bitype::synth_idxtm(&Ext::empty(), ctx, j);       
        let b = match id.clas {
            Result::Ok(ref sort) => {
                let rctx = super::relctx_of_ctx(ctx);
                let eq = equiv::decide_idxtm_equiv(&rctx, &id, &jd, sort);
                //fgi_db!("test_idxtm_equiv: {:?} =({})= {:?}:\n\t{:?}", i, eq.res == Result::Ok(true), j, eq);
                match eq.res {
                    Result::Ok(true) => true,
                    _ => false
                }
            }
            _ => {
                fgi_db!("sorting error for terms: {} and {}", i, j);
                false
            }
        };
        if b { fgi_db!("^yes") } else { fgi_db!("^no") }
        db_region_close!();
        b
    }

    pub fn test_idxtm_empty(ctx:&Ctx, i:&IdxTm) -> bool {
        fgi_db!("decide if {} ⊢ {} ≡ 0 : NmSet", ctx, i);
        db_region_open!(false, crate::vt100::DecideBracket);
        let b = test_idxtm_equiv(ctx, 
                                 &normal::normal_idxtm(ctx, i.clone()), 
                                 &normal::normal_idxtm(ctx, IdxTm::Empty));
        if b { fgi_db!("^yes") } else { fgi_db!("^no") }
        db_region_close!();
        b
    }

    /// Tactic to find an index term `j2` such that `i = j % j2`
    ///
    /// TODO: "Verify" the results using our decision procedures; return those derivations with the term that we find
    pub fn decide_idxtm_subtraction(ctx:&Ctx, i:IdxTm, j:IdxTm) -> Result<IdxTm, Error> {
        if false {
            fgi_db!("\x1B[0;1mdecide_idxtm_subtraction:\x1B[0;0m\n From:\n\t{}\n Subtract:\n\t{}", &i, &j);
        } else {
            fgi_db!("\x1B[0;1mdecide_idxtm_subtraction:\x1B[0;0m from {}, subtract {}", &i, &j);            
        }
        if test_idxtm_empty(ctx, &j) {
            // Special (but common) case: The second index is the empty name set. The result is the first index.
            fgi_db!("^decide_idxtm_subtraction:\n\tEmpty second term.");
            return Result::Ok(i)
        } else if test_idxtm_equiv(ctx, &i, &j) {
            // Special (but common) case: They are equal.  
            // The result is the emptyset.
            fgi_db!("^decide_idxtm_subtraction: Equal");
            return Result::Ok(IdxTm::Empty)
        } else {
            fgi_db!("^decide_idxtm_subtraction: Not (yet) apparently equal.");
        };
        // Next, try normalizing, and testing equality again, and then failing that, more cases
        fgi_db!("^decide_idxtm_subtraction: normalizing index terms...");
        let ni = normal::normal_idxtm(ctx, i.clone());
        let nj = normal::normal_idxtm(ctx, j);
        fgi_db!("^decide_idxtm_subtraction: normalizing index terms: done.");
        if false {
            fgi_db!("^decide_idxtm_subtraction:\n From:\n\t{}\n Subtract:\n\t{}", &ni, &nj);
        } else {
            fgi_db!("^decide_idxtm_subtraction: from {}, subtract {}", &ni, &nj);
        }
        if test_idxtm_empty(ctx, &nj) {
            // Special (but common) case: The second index is the empty name set. The result is the first index.
            fgi_db!("^decide_idxtm_subtraction: Empty second term.");
            return Result::Ok(i)
        } else if test_idxtm_equiv(ctx, &ni, &nj) {
            // Special (but common) case: They are equal.  
            // The result is the emptyset.
            fgi_db!("^decide_idxtm_subtraction: Equal.");
            return Result::Ok(IdxTm::Empty)
        } else {
            fgi_db!("^decide_idxtm_subtraction: Not (apparently) equal.");
        };
        match (ni, nj) {
            (IdxTm::Var(x), j) => {
                let xdef = bitype::find_defs_for_idxtm_var(&ctx, &x);
                match xdef {
                    None => {
                        //fgi_db!("^decide_idxtm_subtraction: Failure:\n From variable (with no known decomposition):\n\t{}\n Cannot subtract index term:\n\t{}", &x, &j);
                        Result::Err( Error::CannotSubtractFromVar(x, j) )
                    }
                    Some(xdef) => {
                        //fgi_db!("^decide_idxtm_subtraction: Using {} == {} ...", x, xdef);
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
            // (IdxTm::Map(n1, i1), IdxTm::Map(n2, i2)) => {
            //     let sort = fgi_sort!("[Nm -> Nm]");
            //     let n1 = panic!("XXX");
            //     let n2 = panic!("XXX");
            //     let n1_n2_equiv = equiv::decide_nmtm_equiv(&super::relctx_of_ctx(ctx), n1, n2, &sort);
            //     match n1_n2_equiv.res {
            //         Ok(true) => {
            //             decide_idxtm_subtraction(ctx, (*i1).clone(), (*i2).clone())
            //         }
            //         _ => {
            //             fgi_db!("^decide_idxtm_subtraction: Failure:\n From index term:\n\t{}\n We do not know how to subtract index term:\n\t{}", &i, &j);
            //             Result::Err( Error::CannotSubtractFromIdxTm(i, j) )
            //         }
            //     }
            // }
            (i, j) => {
                fgi_db!("^decide_idxtm_subtraction: Failure:\n From index term:\n\t{}\n We do not know how to subtract index term:\n\t{}", &i, &j);
                Result::Err( Error::CannotSubtractFromIdxTm(i, j) )
            }
        }        
    }

    pub fn decide_effect_subtraction_db(ctx:&Ctx, r:Role, eff1:Effect, eff2:Effect) -> Result<Effect, Error> {
        use crate::vt100;
        fgi_db!("{}decide if: {}{} {}⊢ {}{} {}- {}{} {}≡ {}?",
                vt100::DecideIf{},
                vt100::VDash{}, ctx,
                vt100::VDash{},
                vt100::Effect{}, eff1,
                vt100::EffectSub{},
                vt100::Effect{}, eff2,
                vt100::Equiv{},
                vt100::Effect{}
        );
        db_region_open!(false, vt100::DecideBracket);
        let res = decide_effect_subtraction(ctx, r, eff1.clone(), eff2.clone());
        db_region_close!();
        match &res {
            Ok(ref eff3) => {
                fgi_db!("  {}success: {}{} {}⊢ {}{} {}- {}{} {}≡ {}{}",
                        vt100::DecideTrue{},
                        vt100::VDash{}, ctx,
                        vt100::VDash{},
                        vt100::Effect{}, eff1,
                        vt100::EffectSub{},
                        vt100::Effect{}, eff2,
                        vt100::Equiv{},
                        /*vt100::Effect{}, */ vt100::DecideTrue{}, eff3)
            }
            Err(_err) => {
                fgi_db!("  {}failure: {}{} {}⊬ {}{} {}- {}{} {}≡ {}?",
                        vt100::DecideFail{},
                        vt100::VDash{}, ctx,
                        vt100::NotVDash{},
                        vt100::Effect{}, eff1,
                        vt100::NotVDash{},                        
                        vt100::Effect{}, eff2,
                        vt100::Equiv{},
                        vt100::Effect{})
            }
        };
        res
    }


    /// Tactic to find the result effect `eff3` such that `eff1 = eff2 then eff3`
    ///
    /// TODO: "Verify" the results using our decision procedures; return those derivations with the term that we find    
    pub fn decide_effect_subtraction(ctx:&Ctx, r:Role, eff1:Effect, eff2:Effect) -> Result<Effect, Error> {
        assert_eq!(r, Role::Archivist);
        let res = if decide_effect_empty(ctx, eff2.clone()) {
            fgi_db!("^decide_effect_subtraction: holds: {} ⊢ {} - {} ≡ {}, since {} is empty",
                    ctx, &eff1, &eff2, &eff1, &eff2);
            Result::Ok(eff1.clone())
        }
        else {
            match (eff1.clone(), eff2.clone()) {
                (Effect::WR(wr1, rd1), Effect::WR(wr2, rd2)) => {
                    fgi_db!("Writes:");
                    db_region_open!(false, vt100::DecideBracket);
                    let wr3 = decide_idxtm_subtraction(ctx, wr1.clone(), wr2.clone());
                    db_region_close!();
                    use super::subset;
                    
                    // TODO: Figure out the right place to put this
                    // normalization step, given the switching between
                    // relational and ordinary typing contexts
                    // everywhere.
                    fgi_db!("Reads:");
                    db_region_open!(false, vt100::DecideBracket);
                    let rd1n = normal::normal_idxtm(ctx, rd1.clone());
                    let rd2n = normal::normal_idxtm(ctx, rd2.clone());
                    let rdsub = subset::decide_idxtm_subset(
                        &super::relctx_of_ctx(ctx),
                        // rd2: Candidate to be the smaller set
                        &rd2n,
                        // rd1: Candidate to be the larger set
                        &rd1n.clone()
                    );
                    db_region_close!();
                    match (wr3, rdsub.res) {
                        (Ok(wr3), Ok(_)) => {
                            let eff3 = Effect::WR(wr3, rd1);
                            Ok(eff3)
                        },
                        (Err(err),_) => {
                            db_region_open!(false, vt100::DecideBracket);
                            fgi_db!("decide_effect_subtraction: Cannot subtract write set:");
                            fgi_db!(" Superset (candidate):\n\t{}", &wr1);
                            fgi_db!(" Subset (candidate):\n\t{}", &wr2);
                            fgi_db!("\n\
                                     (If you believe this subset relationship holds, \
                                     Fungi may need additional reasoning in its `decide` \
                                     and/or `normal` modules...)");
                            db_region_close!();
                            Result::Err(err)
                        }
                        // TODO-someday: gather all errors together
                        (_,Err(err)) => {
                            db_region_open!(false, vt100::DecideBracket);
                            fgi_db!("decide_effect_subtraction: Cannot decide read subset:");
                            fgi_db!(" Error: {}\n", err);
                            fgi_db!(" Superset (candidate):\n\t{}", &rd1n);
                            fgi_db!(" Subset (candidate):\n\t{}", &rd2n);
                            fgi_db!("\n\
                                     (If you believe this subset relationship holds, \
                                     Fungi may need additional reasoning in its `decide` \
                                     and/or `normal` modules...)");
                            db_region_close!();
                            Result::Err(Error::CannotDecideReadSubset(Rc::new(err)))
                        },
                    }
                }
                _ => {
                    fgi_db!("^decide_effect_subtraction: Failure: {} ⊬ {} - {} ≡ ?",
                            ctx, &eff1, &eff2);
                    Result::Err( Error::CannotSubtract(eff1, eff2) )
                }
            }
        };
        res
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
    
    pub fn decide_effect_sequencing_db(ctx:&Ctx, r:Role, eff1:Effect, eff2:Effect) -> Result<Effect, Error> {
        use crate::vt100;
        fgi_db!("{}decide if: {}{} {}⊢ {}{} {}then {}{} {}≡ {}?",
                vt100::DecideIf{},
                vt100::VDash{}, ctx,
                vt100::VDash{},
                vt100::Effect{}, eff1,
                vt100::EffectSeq{},
                vt100::Effect{}, eff2,
                vt100::Equiv{},
                vt100::Effect{}
        );
        db_region_open!(false, vt100::DecideBracket);
        let res = decide_effect_sequencing(ctx, r, eff1.clone(), eff2.clone());
        db_region_close!();
        match &res {
            Ok(ref eff3) => {
                fgi_db!("  {}success: {}{} {}⊢ {}{} {}then {}{} {}≡ {}{}",
                        vt100::DecideTrue{},
                        vt100::VDash{}, ctx,
                        vt100::VDash{},
                        vt100::Effect{}, eff1,
                        vt100::EffectSub{},
                        vt100::Effect{}, eff2,
                        vt100::Equiv{},
                        /*vt100::Effect{},*/ vt100::DecideTrue{}, eff3)
            }
            Err(_err) => {
                fgi_db!("  {}failure: {}{} {}⊬ {}{} {}then {}{} {}≡ {}?",
                        vt100::DecideFail{},
                        vt100::VDash{}, ctx,
                        vt100::NotVDash{},
                        vt100::Effect{}, eff1,
                        vt100::NotVDash{},                        
                        vt100::Effect{}, eff2,
                        vt100::Equiv{},
                        vt100::Effect{})
            }
        };
        res
    }

    /// The result effect, if it exists, is `ceffect3` such that `eff1 then ceffect2 = ceffect3`
    ///
    /// This operation is called "effect coalescing" in the formalism
    /// of Fungi.  It's a wrapper around effect sequencing, that
    /// pushes another effect after the existing one within the
    /// `CEffect` syntax, even if under one or more "forall" binders.
    ///
    pub fn decide_effect_ceffect_sequencing_db(ctx:&Ctx, r:Role, eff1:Effect, ce2:CEffect) -> Result<CEffect, Error> {
        match ce2 {
            CEffect::Cons(ctype2, eff2) => {
                match decide_effect_sequencing_db(ctx, r, eff1, eff2) {
                    Err(e) => Err(e),
                    Ok(eff3) => Ok(CEffect::Cons(ctype2, eff3))
                }
            },
            CEffect::ForallType(x,xk,ce) => {
                match decide_effect_ceffect_sequencing_db(ctx, r, eff1, (*ce).clone()) {
                    Err(e) => Err(e),
                    Ok(ce) => Ok(CEffect::ForallType(x,xk,Rc::new(ce)))
                }
            },
            CEffect::ForallIdx(x,xg,p,ce) => {
                match decide_effect_ceffect_sequencing_db(ctx, r, eff1, (*ce).clone()) {
                    Err(e) => Err(e),
                    Ok(ce) => Ok(CEffect::ForallIdx(x,xg,p,Rc::new(ce)))
                }
            }
            CEffect::NoParse(s) => Ok(CEffect::NoParse(s)),
        }
    }

    /// The result effect, if it exists, is `ceffect3` such that `eff1 then ceffect2 = ceffect3`
    ///
    /// This operation is called "effect coalescing" in the formalism
    /// of Fungi.  It's a wrapper around effect sequencing, that
    /// pushes another effect after the existing one within the
    /// `CEffect` syntax, even if under one or more "forall" binders.
    ///
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
                        //fgi_db!("^decide_effect_sequencing: Cannot sequence:\n Effect 1:\n\t{}\n Effect 2:\n\t{}", &eff1, &eff2);
                        Result::Err( Error::CannotSequence(eff1, eff2) )
                    }
                }
            }
            _ => {
                //fgi_db!("^decide_effect_sequencing: Cannot sequence:\n Effect 1:\n\t{}\n Effect 2:\n\t{}", &eff1, &eff2);
                Result::Err( Error::CannotSequence(eff1, eff2) )
            }
        }}
    }
}


/// Decide equivalence of two terms (types, indices, name terms)
pub mod equiv {
    //use ast::*;
    use crate::bitype::{HasClas};
    use crate::bitype::{NmTmDer,IdxTmDer};
    use crate::bitype::NmTmRule as BiNmTm;
    use crate::bitype::IdxTmRule as BiIdxTm;
    use crate::vt100;
    //use std::fmt;
    use std::rc::Rc;
    use super::*;

    /// Name term equivalence rules
    #[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
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
    #[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
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
    #[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
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
    #[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
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
            (_, _) if m.term == n.term => { succ(NmTmRule::Refl(n.clone())) }
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
                fgi_db!("Note: Fungi called: decide_nmtm_equiv on non-struct:\n\
                          \t{}\n\
                          Versus\n\
                          \t{}", a, b);
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
            (_ir, _jr) if i.term == j.term => { 
                //fgi_db!("Refl equiv: {} == {}", i.term, j.term);
                succ(IdxTmRule::Refl(i.clone())) 
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
                if true {
                    db_region_open!(false, vt100::DecideBracket);
                    fgi_db!("decide_idxtm_equiv: Failure: {} ⊬ {} ≡ {} : {}",
                            ctx, i.term, j.term,
                            display::Result{result:i.clas.clone()});
                    //fgi_db!("This case is not implemented; but, it _may_ indicate a type error.");
                    db_region_close!();
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
    use crate::bitype;
    use crate::bitype::{Ctx};
    //use std::fmt;
    use crate::bitype::{IdxTmDer};
    use std::rc::Rc;
    use super::*;
    use super::equiv::{decide_nmtm_equiv};
    use crate::bitype::IdxTmRule as BiIdxTm;
    use crate::normal::NmSetTm;
    use crate::vt100;

    /// Index term equivalence rules
    #[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
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
        EmptySet,
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
            _ => { fgi_db!("{}", p); false }
        }
    }

    // -------------------------------------------------------------
    /// Decide name set subset relation.
    ///
    /// Return true iff name set `i` is a subset of, or equal to, name
    /// set `j`.  Uses `decide_idxtm_congr` as a subroutine.
    //
    pub fn decide_nmsettm_subset(ctx: &RelCtx, tm1:&NmSetTm, tm2:&NmSetTm) -> IdxTmDec {
        fgi_db!("decide if: {} ⊢ {} ⊆ {} : NmSet", ctx, tm1, tm2);
        db_region_open!(false, vt100::DecideBracket);
        let res = match (tm1, tm2) {
            (&NmSetTm::Single(ref x), &NmSetTm::Single(ref y)) => {
                let (ctx1, ctx2) = ctxs_of_relctx(ctx.clone());
                let xd = bitype::synth_nmtm(&Ext::empty(), &ctx1, x);
                let yd = bitype::synth_nmtm(&Ext::empty(), &ctx2, y);
                let dec = decide_nmtm_equiv(ctx, &xd, &yd, &Sort::Nm);
                Dec { ctx:ctx.clone(),
                      rule:Rc::new(IdxTmRule::Sing(dec.clone())),
                      clas:Sort::NmSet,
                      res:dec.res.clone()
                }
            },
            (&NmSetTm::Single(ref x), &NmSetTm::Subset(ref y)) => {
                decide_idxtm_subset(ctx, &IdxTm::Sing(x.clone()), y)
            },
            (&NmSetTm::Subset(ref x), &NmSetTm::Single(ref y)) => {
                decide_idxtm_subset(ctx, x, &IdxTm::Sing(y.clone()))
            },
            (&NmSetTm::Subset(ref x), &NmSetTm::Subset(ref y)) => {
                decide_idxtm_subset(ctx, x, y)
            }
        };
        db_region_close!();
        fgi_db!("{} ⊢ {} ⊆ {} : NmSet ==> {}", ctx, tm1, tm2, res);
        res
    }

    // -------------------------------------------------------------
    /// Decide name set subset relation.
    ///
    /// Return true iff name set `i` is a subset of, or equal to, name
    /// set `j`.  Uses `decide_idxtm_congr` as a subroutine.
    //
    pub fn decide_nmsettm_subset_simple(ctx: &RelCtx, tm1:&NmSetTm, tm2:&NmSetTm) -> bool {
        fgi_db!("decide if: {} ⊢ {} ⊆ {} : NmSet", ctx, tm1, tm2);
        db_region_open!(false, vt100::DecideBracket);
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
        db_region_close!();
        fgi_db!("{} ⊢ {} ⊆ {} : NmSet ==> {}", ctx, tm1, tm2, res);
        res
    }

    // -------------------------------------------------------------
    /// Decide name set subset relation.
    ///
    /// Return true iff name set `i` is a subset of, or equal to, name
    /// set `j`.  Uses `decide_idxtm_congr` as a subroutine.
    //
    pub fn decide_nmsettm_subset_speculative(ctx: &RelCtx, tm1:&NmSetTm, tm2:&NmSetTm) -> bool {
        fgi_db!("decide_nmsettm_subset_speculative: decide if: {} ⊢ {} ⊆ {} : NmSet",
                ctx, tm1, tm2);
        db_region_open!(false, vt100::DecideBracket);
        let res = match (tm1, tm2) {
            (&NmSetTm::Single(ref x), &NmSetTm::Single(ref y)) => {
                // TODO -- use equiv module
                x == y
            },
            (&NmSetTm::Single(ref x), &NmSetTm::Subset(ref y)) => {
                decide_idxtm_subset_speculative(ctx, &IdxTm::Sing(x.clone()), y)
            },
            (&NmSetTm::Subset(ref x), &NmSetTm::Single(ref y)) => {
                decide_idxtm_subset_speculative(ctx, x, &IdxTm::Sing(y.clone()))
            },
            (&NmSetTm::Subset(ref x), &NmSetTm::Subset(ref y)) => {
                decide_idxtm_subset_speculative(ctx, x, y)
            }
        };
        db_region_close!();        
        res
    }


    pub fn decide_idxtm_subset_db(ctx: &RelCtx, i:&IdxTm, j:&IdxTm) -> IdxTmDec {
        fgi_db!("decide if: {} ⊢ {} ⊆ {} : NmSet", ctx, i, j);
        db_region_open!(false, vt100::DecideBracket);
        let res = decide_idxtm_subset(ctx, i, j);
        db_region_close!();
        match res.res {
            Ok(true) => fgi_db!("holds"),
            _        => fgi_db!("fails to hold")
        };
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
        
        // Basecase: If `a` is the empty set, and `b` is anything with
        // sort NmSet, then the subset holds.
        {
            //fgi_db!("testing {} =?= emptyset", a);
            let (ctx1, _) = ctxs_of_relctx(ctx.clone());
            let ed = bitype::synth_idxtm(&Ext::empty(), &ctx1, 
                                         &normal::normal_idxtm(&ctx1, IdxTm::Empty));
            let ad = bitype::synth_idxtm(&Ext::empty(), &ctx1, &a);
            let ad = equiv::decide_idxtm_equiv(&ctx, &ad, &ed, &Sort::NmSet);
            match ad.res {
                Result::Ok(true) => {
                    return Dec{
                        ctx:ctx.clone(),
                        rule:Rc::new(IdxTmRule::EmptySet),
                        clas:Sort::NmSet,
                        res:Ok(true)
                    }
                },
                _ => {
                    //fgi_db!("testing found: {} =/= emptyset", a);
                }
            }
        }
            
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
                            //fgi_db!("No defs for {}, looking for subset:\t\n{}", x, &a);
                            //panic!("TODO: {}", ctx)
                            return Dec{
                                ctx:ctx.clone(),
                                rule:Rc::new(IdxTmRule::Fail),
                                clas:Sort::NmSet,
                                res:Err(DecError::SubsetSearchFailureMisc(format!("Subcase-1")))
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
                                //fgi_db!("decide_idxtm_subset:\n  {}\n  {}\nTRUE(3)!",
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
                            res:Err(DecError::SubsetSearchFailureMisc(format!("Subcase-3")))
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
                                    decide_nmsettm_subset_speculative(ctx, tm1, tm2)
                                {
                                    found_tm1 = true;
                                }
                            }
                            if found_tm1 { continue } else {
                                if true {
                                    fgi_db!("^decide_idxtm_subset: Term not found in superset candidate:\n\
                                              \t{}\n\
                                              Term above is absent among the superset candidate's terms:\n\
                                              \t{:?}",
                                             tm1, b_ns.terms)
                                };
                                return Dec{
                                    ctx:ctx.clone(),
                                    rule:Rc::new(IdxTmRule::Fail),
                                    clas:Sort::NmSet,
                                    res:Err(DecError::SubsetSearchFailureTm(
                                        tm1.clone(),
                                        b_ns
                                    ))
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
                    // Subcase 5: Perhaps the term is present as a subset?
                    a => {
                        // Look for the term in the name set `b_ns`
                        let a_ns_tm = normal::NmSetTm::Subset(a.clone());
                        for b_ns_tm in b_ns.terms.iter() {
                            // TODO: Use equiv checking, not ==, which may be too restrictive.
                            if b_ns_tm == &a_ns_tm {
                                return Dec{
                                    ctx:ctx.clone(),
                                    rule:Rc::new(IdxTmRule::SubsetRefl(a_ns_tm)),
                                    clas:Sort::NmSet,
                                    res:Ok(true)
                                }
                            }
                            else { continue }
                        }
                        fgi_db!("decide_idxtm_subset: Cannot decide subset:");
                        db_region_open!(false, vt100::DecideBracket);
                        fgi_db!(" Superset (candidate): {}", &b);
                        fgi_db!("   Subset (candidate): {}", &a);
                        fgi_db!("\n\
                                 (If you believe this subset relationship holds, \
                                 Fungi may need additional reasoning in its `decide` \
                                 and/or `normal` modules...)");
                        db_region_close!();
                        return Dec{
                            ctx:ctx.clone(),
                            rule:Rc::new(IdxTmRule::Fail),
                            clas:Sort::NmSet,
                            res:Err(DecError::SubsetSearchFailure(a, b))
                        }
                    }
                }
            },
            _ => {
                let res = decide_idxtm_subset_congr (
                    ctx,
                    &a_bit, &b_bit,
                    &Sort::NmSet
                );
                res                    
            }
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
            (_ir, _jr) if i.term == j.term => {
                //fgi_db!("Refl subset: {} == {}", i, j);
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
                db_region_open!(false, vt100::DecideBracket);
                fgi_db!("decide_idxtm_subset: Cannot decide this case:\n Left:\n\t{}\n Right:\n\t{}", i.term, j.term);
                fgi_db!("This case is not implemented; but, it _may_ indicate a type error.");
                db_region_close!();
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
            if i != j {
                //fgi_db!("\x1B[0;1mdecide_idxtm_subset: holds:\x1B[0;0m\n\t{}\n  ≤\n\t{}", i, j);
                fgi_db!("\x1B[0;1mdecide_idxtm_subset: holds: \x1B[0;0m{} ⊢ {} ≤ {}", ctx, i, j);
            };
            return true
        }
        else {
            fgi_db!("\x1B[0;1mdecide_idxtm_subset:\x1B[0;1;31m fails to hold:\x1B[0;0m\n\t{}\n  \x1B[1;31mNOT(≤)\x1B[0;0m\n\t{}", i, j);
            return false
        }
    }

    /// Decide name set subset relation.  
    ///
    /// This is like decide_idxtm_subset_simple, but is intended to be
    /// called in speculative situations (e.g., searching for an
    /// equivalent term among many in a set of terms).
    ///
    /// Wraps `decide_idxtm_subset` with a simpler output type.
    //
    pub fn decide_idxtm_subset_speculative(ctx: &RelCtx, i:&IdxTm, j:&IdxTm) -> bool
    {
        let d = decide_idxtm_subset(ctx, &i, &j);
        if d.res == Ok(true) {
            if i != j {
                fgi_db!("\x1B[0;1mdecide_idxtm_subset: holds: \x1B[0;0m{} ⊢ {} ≤ {}", ctx, i, j);
            };
            return true
        }
        else {
            //fgi_db!("\x1B[0;1mdecide_idxtm_subset:\x1B[0;1;31m fails to hold:\x1B[0;0m\n\t{}\n  \x1B[1;31mNOT(≤)\x1B[0;0m\n\t{}", i, j);
            return false
        }
    }

    pub fn decide_type_subset_norm_db(ctx: &RelCtx, a:Type, b:Type) -> bool {
        use crate::vt100;
        fgi_db!("{}decide if: {}{} {}⊢ {}{} {}⊆ {}{}",
                vt100::DecideIf{},
                vt100::VDash{}, ctx,
                vt100::Kw{},
                vt100::Type{}, a,
                vt100::Kw{},
                vt100::Type{}, b
        );
        db_region_open!(false);
        let res = decide_type_subset_norm(ctx, a.clone(), b.clone());
        db_region_close!();
        if res {
            fgi_db!("{}  success: {}{} {}⊢ {}{} {}⊆ {}{}",
                    vt100::DecideTrue{},
                    vt100::VDash{}, ctx,
                    vt100::Kw{},
                    vt100::Type{}, a,
                    vt100::DecideTrue{},
                    vt100::Type{}, b)
        } else {        
            fgi_db!("{}  failure: {}{} {}⊢ {}{} {}⊆ {}{}",
                    vt100::DecideFail{},
                    vt100::VDash{}, ctx,
                    vt100::Kw{},
                    vt100::Type{}, a,
                    vt100::DecideFail{},
                    vt100::Type{}, b)
        };
        res
    }

    
    /// Decide type subset relation on normalized versions of the given terms.
    pub fn decide_type_subset_norm(ctx: &RelCtx, a:Type, b:Type) -> bool {
        use crate::expand;
        if a == b { true }
        else {
            // TODO-someday: Make this operation cheaper somehow (use traits in a clever way?)
            let (ctx1, ctx2) = ctxs_of_relctx((*ctx).clone());
            let a = expand::expand_type(&ctx1, a);
            let a = normal::normal_type(&ctx1, &a);
            let b = expand::expand_type(&ctx2, b);
            let b = normal::normal_type(&ctx2, &b);
            let r = decide_type_subset(ctx, a.clone(), b.clone());
            return r
        }
    }

    /// Decide type subset relation
    pub fn decide_type_subset(ctx: &RelCtx, a:Type, b:Type) -> bool {
        if a == b { true } else {
            match (a,b) {
                (Type::Ident(y), b) => {
                    let a = crate::expand::expand_type(&ctxs_of_relctx(ctx.clone()).0,Type::Ident(y));
                    decide_type_subset(ctx, a, b)
                }
                (a, Type::Ident(y)) => {
                    let b = crate::expand::expand_type(&ctxs_of_relctx(ctx.clone()).1,Type::Ident(y));
                    decide_type_subset(ctx, a, b)
                }
                (Type::IdentDef(_x, a), b) => {
                    decide_type_subset(ctx, (*a).clone(), b)
                }
                (a, Type::IdentDef(_y, b)) => {
                    decide_type_subset(ctx, a, (*b).clone())
                },
                (Type::Abstract(x), Type::Abstract(y)) => {
                    x == y
                },
                (Type::IdentUndef(x), Type::IdentUndef(y)) => {
                    x == y
                },
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
                        fgi_db!("Error: {} =/= {}", g1, g2);
                        false
                            
                    }
                }
                (Type::Rec(x1, a1), Type::Rec(x2, a2)) => {
                    decide_type_subset_rec(
                        &ctx.add_tvars(x1, x2),
                        a1, a2)
                }                
                (x,y) => {
                    fgi_db!("Cannot prove these types are related (as first subtype of second):\n\t{}\nand:\n\t{}", x, y);
                    false
                }
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

    pub fn decide_ceffect_subset_db(ctx: &RelCtx, ce1:CEffect, ce2:CEffect) -> bool {
        use crate::vt100;
        fgi_db!("{}decide if: {}{} {}⊢ {}{} {}⊆ {}{}",
                vt100::DecideIf{},
                vt100::VDash{}, ctx,
                vt100::Kw{},
                vt100::Type{}, ce1,
                vt100::Kw{},
                vt100::Type{}, ce2
        );
        db_region_open!(false);
        let res = decide_ceffect_subset(ctx, ce1.clone(), ce2.clone());
        if res {
            fgi_db!("{}  success: {}{} {}⊢ {}{} {}⊆ {}{}",
                    vt100::DecideTrue{},
                    vt100::VDash{}, ctx,
                    vt100::Kw{},
                    vt100::Type{}, ce1,
                    vt100::DecideTrue{},
                    vt100::Type{}, ce2)
        } else {        
            fgi_db!("{}  failure: {}{} {}⊢ {}{} {}⊆ {}{}",
                    vt100::DecideFail{},
                    vt100::VDash{}, ctx,
                    vt100::Kw{},
                    vt100::Type{}, ce1,
                    vt100::DecideFail{},
                    vt100::Type{}, ce2)
        };
        res
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
    use crate::bitype::{HasClas};
    use crate::bitype::{NmTmDer,IdxTmDer};
    use crate::bitype::NmTmRule as BiNmTm;
    use crate::bitype::IdxTmRule as BiIdxTm;
    //use std::fmt;
    //use std::rc::Rc;
    use super::*;

    /// Name term apartness rules
    ///
    /// Fig. 24 of https://arxiv.org/abs/1610.00097v5
    ///
    #[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
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
    #[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize)]
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
                fgi_db!("decide_nmtm_apart non-struct:\n\
                          \t{}\n\
                          Versus\n\
                          \t{}", a, b);
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
