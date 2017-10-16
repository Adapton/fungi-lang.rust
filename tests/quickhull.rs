#[macro_use]
extern crate iodyn_lang;

use std::rc::Rc;
use iodyn_lang::ast::*;
use iodyn_lang::bitype;

#[test]
fn test_main_algo() {
  let ctx = TCtxt::Empty
    .var("highest".to_string(),make_type![U((nat x nat) -> ((nat x nat) -> F (nat x nat)))])
    .var("make_r_line".to_string(),make_type![U((nat x nat) -> (((nat x nat) x (nat x nat)) -> F (nat x nat)))])
    .var("make_l_line".to_string(),make_type![U((nat x nat) -> (((nat x nat) x (nat x nat)) -> F (nat x nat)))])
  ;
  let ast = make_exp![
      [#line!()] {fix qh. lam pts. lam line. lam hull. {
      // if pts is empty return hull else 
      [#line!()] let mid = { SeqFoldUp(pts,(0,0),{lam p.ret p},{force highest}) }
      [#line!()] let hull = {
        [#line!()] let r_line = {{{force make_r_line} mid} line}
        [#line!()] let r_pts = {SeqFilter(pts,{{force above_line} r_line})}
        [#line!()] {{{{force qh} r_pts} r_line} hull}
      }
      [#line!()] let hull = {SeqAppend(hull,mid)}
      [#line!()] let l_line = {{{force make_l_line} line} mid}
      [#line!()] let l_pts = {SeqFilter(pts,{{force above_line} l_line})}
      [#line!()]   {{{{force qh} l_pts} l_line} hull}
      }}
      : Seq((nat x nat)) -> 
            (((nat x nat) x (nat x nat)) -> 
             (Seq((nat x nat)) -> F Seq((nat x nat))))
  ];

  //println!("ast: {:?}", ast);
  assert!(bitype::synth_exp(None, &ctx, &ast) != None)
}
