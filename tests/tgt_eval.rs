#![recursion_limit="128"]
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
    println!("> {:?}\n\n", e1);
    let t1 = eval_closed_exp(e1);
    let t2 = eval_closed_exp(e2);
    assert_eq!(t1, t2)
}

#[test]
fn eval_let_pair_natlt () {
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

#[test]
fn eval_lambda_app () {
    eval_test_equiv(
        tgt_exp![
            {#x.#y.x < y} 1 2
        ],
        tgt_exp![
            ret true
        ]);

    eval_test_equiv(
        tgt_exp![
            let x = {{#x.#y.x + y} 1 2}
            {#z1.#z2.#z3. if {z1 < z2} {ret 123} else {ret 321}}
            x 4 666
        ],
        tgt_exp![
            ret 123
        ]);
}

#[test]
fn eval_case () {
    eval_test_equiv(
        tgt_exp![
            match (inj1 2) {
                x => {x + 1}
                y => {ret 0}
            }
        ],
        tgt_exp![
            ret 3
        ]);
    
    eval_test_equiv(
        tgt_exp![
            match (inj2 2) {
                x => {x + 1}
                y => {ret 0}
            }
        ],
        tgt_exp![
            ret 0
        ]);

    // test nested cases; nested injections are a little awkward
    eval_test_equiv(
        tgt_exp![
            match (inj2 (inj2 2)) {
                x => {ret 0}
                x => {ret 0}
                y => {ret y}
            }
        ],
        tgt_exp![
            ret 2
        ])
}

#[test]
fn eval_fix () {
    eval_test_equiv(
        tgt_exp![
            let rec f:(Thk[0] Nat -> (Nat -> (F Nat |> {0;0}) |> {0;0}) {0;0}) = {
                #x. if {x == 0} {ret 123} else {ret 321}
            }
            {force f} 0
        ],
        tgt_exp![
            ret 123
        ]);
        
    eval_test_equiv(
        tgt_exp![
            let rec f:(Thk[0] Nat -> (Nat -> (F Nat |> {0;0}) |> {0;0}) {0;0}) = {
                #x. if {x == 0} {{force f} 1} else {ret 321}
            }
            {force f} 0
        ],
        tgt_exp![
            ret 321
        ]);

    eval_test_equiv(
        tgt_exp![
            let rec f:(Thk[0] Nat -> (Nat -> (F Nat |> {0;0}) |> {0;0}) {0;0}) = {
                #x. if {x == 0} {let x = {x + 1} {force f} x} else {ret x}
            }
            {force f} 0
        ],
        tgt_exp![
            ret 1
        ]);

    eval_test_equiv(
        tgt_exp![
            let rec f:(Thk[0] Nat -> (Nat -> (F Nat |> {0;0}) |> {0;0}) {0;0}) = {
                #x. #end. if {x < end} {let x = {x + 1} {force f} x end} else {ret x}
            }
            {force f} 0 2
        ],
        tgt_exp![
            ret 2
        ])      

}
