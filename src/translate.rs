//! Translation, from Ast (`ast` module) to Target Ast (`tgt_ast` module)
///
///

use std::rc::Rc;
use ast;
use tgt_ast;

pub use ast::Var         as Var;
pub use ast::LetHint     as LetHint;
pub use ast::TCtxt       as AstCtx;
pub use ast::Type        as AstType;
pub use ast::CType       as AstCType;
pub use ast::typing::Val as AstVal;
pub use ast::typing::Exp as AstExp;

pub use tgt_ast::typing::Val   as TgtVal;
pub use tgt_ast::typing::ValTD as TgtValTD;
pub use tgt_ast::typing::Exp   as TgtExp;
pub use tgt_ast::typing::ExpTD as TgtExpTD;
pub use tgt_ast::TCtxt         as TgtCtx;
pub use tgt_ast::Type          as TgtType;
pub use tgt_ast::CType         as TgtCType;
pub use tgt_ast::NameTm        as NmTm;
pub use tgt_ast::IdxTm         as IdxTm;
pub use tgt_ast::CEffect       as CEffect;
pub use tgt_ast::Effect        as Effect;


pub fn tr_type(c:TrCtx, t:&AstType) -> (TrCtx, TgtType) {
    unimplemented!()
}

pub fn tr_ctype(c:TrCtx, t:&AstCType) -> (TrCtx, AstCType) {
    unimplemented!()
}


// todo: ambient information:
// - name variable, and its nameset variable
// - name space

pub fn tr_val(c:TrCtx, v:&AstVal) -> TgtValTD {
    unimplemented!()
}

/// Translation context (for expressions)
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
pub struct TrCtx {
    /// target typing context
    tgt_ctx:TgtCtx,
    /// name space is full path of scopes
    tgt_ns:NmTm,
    /// ambient name, variable
    amb_nm:Var,
    /// set from which ambient name is drawn
    amb_nmset:IdxTm,
}

pub fn tr_ctx_bind_var(c:TrCtx, x:Var, t:TgtType) -> TrCtx {
    unimplemented!()
}

pub fn tr_ctx_bind_amb_nm(c:TrCtx, t:IdxTm) -> TrCtx {
    unimplemented!()
}

pub fn tgt_val_td(c:TrCtx, v:TgtVal, t:TgtType) -> TgtValTD {
    unimplemented!()
}

pub fn tgt_exp_td(c:TrCtx, e:TgtExp, ct:CEffect) -> TgtExpTD {
    unimplemented!()
}

pub fn match_nm_prod(t:TgtType) -> Option<(TgtType,IdxTm)> {
    unimplemented!()
}

fn eff_empty() -> Effect {
    Effect::WR(IdxTm::Empty,IdxTm::Empty)
}

fn ctype_w_no_eff(ct:TgtCType) -> CEffect {
    CEffect::Cons(ct, eff_empty())
}

fn ctype_eff1_then_eff2(ct:TgtCType, eff1:Effect, eff2:Effect) -> CEffect {
    unimplemented!()
}

fn ceffect_after_eff(ce:CEffect, eff:Effect) -> CEffect {
    unimplemented!()
}

pub fn tr_proj2(c:TrCtx, e:TgtExpTD, snd_type:TgtType) -> TgtExpTD {
    // todo make fresh names?
    let p = "$p".to_string();
    let x = "$_".to_string();
    let y = "$y".to_string();
    let ct = ctype_w_no_eff(TgtCType::Lift(snd_type));
    // use pair p to compute the projection:
    let proj2_p =
        tgt_exp_td(c.clone(), TgtExp::Split(
            TgtVal::Var(p.clone()), x, y.clone(),
            tgt_exp_td(c.clone(),
                       TgtExp::Ret(TgtVal::Var(y)), ct.clone())),
                   ct.clone());
    // bind pair p, and then do the projection
    tgt_exp_td(c, TgtExp::Let(p, e, proj2_p), ct.clone())
}

pub fn tr_exp(c:TrCtx, e:&AstExp) -> TgtExpTD {
    match e.clone() {
        AstExp::Lam(x,e1) => {
            match e1.ctyp {
                AstCType::Arrow(xt, e1_ct) => {
                    let (c, xtt) = tr_type(c, &xt);
                    let c2 = tr_ctx_bind_var(c.clone(), x.clone(), xtt.clone());
                    let tr_e1 = tr_exp(c.clone(), &*e1.exp);
                    let arrowt = ctype_w_no_eff(TgtCType::Arrow(xtt, Rc::new(tr_e1.ceffect.clone())));
                    tgt_exp_td(c.clone(), TgtExp::Lam(x, tr_e1), arrowt)
                },
                _ => { unreachable!() }
            }
        },
        AstExp::App(e1,v) => {
            let tr_e1 = tr_exp(c.clone(), &*e1.exp);
            let tr_v = tr_val(c.clone(), &v);
            let ce = match tr_e1.ceffect.clone() {
                CEffect::Cons(TgtCType::Arrow(_,ce), eff1) => ceffect_after_eff((*ce).clone(), eff1),
                _ => unreachable!()
            };
            tgt_exp_td(c.clone(), TgtExp::App(tr_e1, (*tr_v.val).clone()), ce)
        },
        AstExp::Ret(v) => {
            let tr_v = tr_val(c.clone(), &v);
            let nt = TgtType::Nm(c.amb_nmset.clone());
            let pt = TgtType::Prod(Rc::new(nt.clone()), Rc::new(tr_v.typ.clone()));
            let ce = ctype_w_no_eff(TgtCType::Lift(pt));
            let amb = tgt_val_td(c.clone(), TgtVal::Var(c.amb_nm.clone()), nt);
            tgt_exp_td(c.clone(), TgtExp::Ret(TgtVal::Pair(amb, tr_v)), ce)
        },
        AstExp::Let(hint, x, e1, e2) => {
            let tr_e1 = tr_exp(c.clone(), &*e1.exp);
            match tr_e1.ceffect.clone() {
                CEffect::Cons(TgtCType::Lift(tx), eff1) => {
                    match match_nm_prod(tx.clone()) {
                        Some((tx_snd, nm_set)) => {
                            // case: e1 returns a value of type `tx`, _and_ additionally, a name.
                            // the name is drawn from a set described by index term `nm_set`.
                            match hint {
                                LetHint::ParAmb => {
                                    // programmer does not want this additional name, so apply the
                                    // translation rule that projects out ret value and drops the additional name.
                                    let tr_proj2_e1 = tr_proj2(c.clone(), tr_e1, tx_snd.clone());
                                    let c2 = tr_ctx_bind_var(c.clone(), x.clone(), tx_snd);
                                    let tr_e2 = tr_exp(c2, &*e2.exp);
                                    match tr_e2.ceffect.clone() {
                                        CEffect::Cons(ct, eff2) => {
                                            let ce = ctype_eff1_then_eff2(ct, eff1, eff2);
                                            tgt_exp_td(c, TgtExp::Let(x, tr_proj2_e1, tr_e2), ce)
                                        },
                                        _ => unreachable!()
                                    }
                                },
                                LetHint::SeqAmb => {
                                    // translate e2 with x and new ambient name in scope
                                    let c2 = tr_ctx_bind_var(c.clone(), x.clone(), tx_snd.clone());
                                    let c2 = tr_ctx_bind_amb_nm(c2, nm_set);
                                    let tr_e2 = tr_exp(c2, &*e2.exp);
                                    match tr_e2.ceffect.clone() {
                                        CEffect::Cons(ct, eff2) => {
                                            // assemble let body to split x into (amb_nm, x),
                                            // putting the new ambient name into scope for tr_e2.
                                            let tr_e2_ce = tr_e2.ceffect.clone();
                                            let split_tr_e2 = TgtExp::Split(TgtVal::Var(x.clone()), c.amb_nm.clone(), x.clone(), tr_e2);
                                            let tr_e2 = tgt_exp_td(c.clone(), split_tr_e2, tr_e2_ce);
                                            let ce = ctype_eff1_then_eff2(ct, eff1, eff2);
                                            tgt_exp_td(c, TgtExp::Let(x, tr_e1, tr_e2), ce)
                                        },
                                        _ => unreachable!(),
                                    }
                                }
                            }
                        },
                        None => {
                            // case: e1 returns a value, and no additional name.
                            match hint {
                                LetHint::ParAmb => {
                                    let c2 = tr_ctx_bind_var(c.clone(), x.clone(), tx);
                                    let tr_e2 = tr_exp(c2, &*e2.exp);
                                    match tr_e2.ceffect.clone() {
                                        CEffect::Cons(ct, eff2) => {
                                            let ce = ctype_eff1_then_eff2(ct, eff1, eff2);
                                            tgt_exp_td(c, TgtExp::Let(x, tr_e1, tr_e2), ce)
                                        },
                                        _ => { unreachable!() }
                                    }
                                },
                                LetHint::SeqAmb => {
                                    // translation error: programmer
                                    // wanted to bind a name from e1,
                                    // but there isn't one to bind.
                                    unimplemented!()
                                }
                            }
                        }
                    }
                },
                _ => {
                    // implies type error in source language and/or translation
                    unreachable!()
                },
            }
        },
        // todo: finish translation cases
        _ => unimplemented!()
    }
}
