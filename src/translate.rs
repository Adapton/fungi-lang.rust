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

pub use tgt_ast::NameTm        as NmTm;
pub use tgt_ast::IdxTm         as IdxTm;
pub use tgt_ast::TCtxt         as TgtCtx;
pub use tgt_ast::Type          as TgtType;
pub use tgt_ast::CType         as TgtCType;
pub use tgt_ast::typing::Val   as TgtVal;
pub use tgt_ast::typing::ValTD as TgtValTD;
pub use tgt_ast::typing::Exp   as TgtExp;
pub use tgt_ast::typing::ExpTD as TgtExpTD;

pub fn tr_type(g:&AstCtx, t:&AstType, tg:&TgtCtx) -> (TgtCtx, TgtType) {
    unimplemented!()
}

pub fn tr_ctype(g: &AstCtx, t:&AstCType, tg:TgtCtx) -> (TgtCtx, AstCType) {
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

pub fn tgt_exp_td(c:TrCtx, e:TgtExp, ct:TgtCType) -> TgtExpTD {
    unimplemented!()
}

pub fn match_nm_prod(t:TgtType) -> Option<(TgtType,IdxTm)> {
    unimplemented!()
}

pub fn tr_proj2(c:TrCtx, e:TgtExpTD, snd_type:TgtType) -> TgtExpTD {
    // todo make fresh names?
    let p = "$p".to_string(); 
    let x = "$x".to_string(); 
    let y = "$y".to_string();
    let ct = TgtCType::Lift(snd_type);
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
        AstExp::Ret(v) => {
            let tr_v = tr_val(c.clone(), &v);
            let nt = TgtType::Nm(c.amb_nmset.clone());
            let pt = TgtType::Prod(Rc::new(nt.clone()), Rc::new(tr_v.typ.clone()));
            let ct = TgtCType::Lift(pt);
            let amb = tgt_val_td(c.clone(), TgtVal::Var(c.amb_nm.clone()), nt);
            tgt_exp_td(c.clone(), TgtExp::Ret(TgtVal::Pair(amb, tr_v)), ct)
        },
        AstExp::Let(hint, x, e1, e2) => {
            let tr_e1 = tr_exp(c.clone(), &*e1.exp);
            match tr_e1.ctype.clone() {
                TgtCType::Arrow(_, _) => { panic!("XXX") },
                TgtCType::Lift(tx) => {
                    match match_nm_prod(tx.clone()) {
                        Some((tx, nm_set)) => {
                            // case: e1 returns a value of type `tx`, _and_ additionally, a name.
                            // the name is drawn from a set described by index term `nm_set`.
                            match hint {
                                LetHint::ParAmb => {
                                    // programmer does not want this
                                    // additional name, so apply the
                                    // translation rule that projects
                                    // out ret value and drops the
                                    // additional name.
                                    let tr_proj2_e1 = tr_proj2(c.clone(), tr_e1, tx.clone());
                                    let c2 = tr_ctx_bind_var(c.clone(), x.clone(), tx);
                                    let tr_e2 = tr_exp(c2, &*e2.exp);
                                    let ct = tr_e2.ctype.clone();                                    
                                    tgt_exp_td(c, TgtExp::Let(x, tr_proj2_e1, tr_e2), ct)
                                },
                                LetHint::SeqAmb => {
                                    let c2 = tr_ctx_bind_var(c.clone(), x.clone(), tx.clone());
                                    let c2 = tr_ctx_bind_amb_nm(c2, nm_set);
                                    let tr_e2 = tr_exp(c2, &*e2.exp);
                                    let ct = tr_e2.ctype.clone();
                                    tgt_exp_td(c, TgtExp::Let(x, tr_e1, tr_e2), ct)
                                }
                            }
                        },
                        None => {
                            // case: e1 returns a value, and no additional name.
                            match hint {
                                LetHint::ParAmb => {
                                    let c2 = tr_ctx_bind_var(c.clone(), x.clone(), tx);
                                    let tr_e2 = tr_exp(c2, &*e2.exp);
                                    let ct = tr_e2.ctype.clone();
                                    tgt_exp_td(c, TgtExp::Let(x, tr_e1, tr_e2), ct)
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
            }
        },
        _ => unimplemented!()
    }
}
