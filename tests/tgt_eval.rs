//#![recursion_limit="128"]
#[macro_use]
extern crate iodyn_lang;


use std::rc::Rc;
use iodyn_lang::tgt_ast::*;
use iodyn_lang::tgt_eval;

fn eval_closed_exp(e:Exp) -> tgt_eval::ExpTerm {
    let mut env = vec![];
    tgt_eval::eval(env, e)
}

fn eval_test_equiv(e1:Exp, e2:Exp) {
    let t1 = eval_closed_exp(e1);
    let t2 = eval_closed_exp(e2);
    assert_eq!(t1, t2)
}

#[test]
fn eval_let () {
    eval_test_equiv(
        tgt_exp![
            let pair  = {ret (1, 2)}
            let (x,y) = {ret pair}
            x < y
        ],
        tgt_exp![
            ret true
        ])
}
