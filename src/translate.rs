//! Translation, from Ast (`ast` module) to Target Ast (`tgt_ast` module)
///
///

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

pub fn tr_val(v:&AstVal, tg:TgtCtx) -> TgtCtx {
    unimplemented!()
}

/// Translation context (for expressions)
pub struct TrCtx {
    tgt_ctx:TgtCtx,
    tgt_ns:NmTm,
    amb_nm:Var,
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

pub fn tr_exp(e:&AstExp, c:TrCtx) -> TgtExpTD {
    match e.clone() {

        AstExp::Let(hint, x, e1, e2) => {
            let tr_e1 = tr_exp(e1, c);
            match tr_e1.ctype {
                TgtCType::Arrow(_, _) => { panic!("XXX") },
                TgtCType::Lift(tx) => {
                    match match_nm_prod(tx) {
                        Some((tx, nm_set)) => {
                            // case: e1 returns a value of type `tx`, _and_ additionally, a name.
                            // the name is drawn from a set described by index term `nm_set`.
                            match hint {
                                LetHint::ParAmb => {
                                    // todo: programmer does not want
                                    // this additional name, so apply
                                    // the translation rule that
                                    // splits and drops the additional
                                    // name.
                                    unimplemented!()
                                },
                                LetHint::SeqAmb => {
                                    let c2 = tr_ctx_bind_var(c.clone(), x, tx);
                                    let c2 = tr_ctx_bind_amb_nm(c2, nm_set);
                                    let tr_e2 = tr_exp(e2, c2);
                                    let ct = tr_e2.ctype.clone();
                                    tgt_exp_td(c, TgtExp::Let(x, tr_e1, tr_e2), ct)
                                }
                            }
                        },
                        None => {
                            // case: e1 returns a value, and no additional name.
                            match hint {
                                LetHint::ParAmb => {
                                    let c2 = tr_ctx_bind_var(c.clone(), x, tx);
                                    let tr_e2 = tr_exp(e2, c2);
                                    let ct = tr_e2.ctype.clone();
                                    let pair_var = format!("{}_{}", x, c2.amb_nm);
                                    let pair_val = tgt_val_td(c2, TgtVal::Var(pair_var), tx);
                                    let tr_e2 = tgt_exp_td(c2, TgtExp::Split(pair_val, x, c2.amb_nm, tr_e2), ct.clone());
                                    tgt_exp_td(c, TgtExp::Let(pair_var, tr_e1, tr_e2), ct.clone())
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
    }
}
