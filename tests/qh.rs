#[macro_use]
extern crate iodyn_lang;

use std::rc::Rc;
use iodyn_lang::ast::*;
use iodyn_lang::bitype;

#[test]
fn test_main_algo() {
  let ctx = TCtxt::Empty
    .var("pts".to_string(),make_type![Seq((nat x nat))])
    .var("line".to_string(),make_type![((nat x nat) x (nat x nat))])
    .var("hull".to_string(),make_type![Seq((nat x nat))])
    .var("true".to_string(),make_type![bool])
  ;

  let ast = make_exp![
    // TODO: write these supplemental functions
    // let highest = ret {thunk {lam l.lam r. ret l}}
    // let make_r_line = {lam m.lam l.ret l}
    // let make_l_line = {lam l.lam m.ret l}
    // let above_line = {lam ln.lam pt.ret true}
    // ret {{{
      fix qh.lam pts.lam line.lam hull.{
      // if pts is empty return hull else 
      let mid = { SeqFoldUp(pts,(0,0),{lam p.ret p},{force highest}) }
      let hull = {
        let r_line = {{{force make_r_line} mid} line}
        let r_pts = {SeqFilter(pts,{{force above_line} r_line})}
        {{{{force qh} r_pts} r_line} hull}
      }
      let hull = {SeqAppend(hull,mid)}
      let l_line = {{{force make_l_line} line} mid}
      let l_pts = {SeqFilter(pts,{{force above_line} l_line})}
      {{{{force qh} l_pts} l_line} hull}
      }
    //   ret {{{force qh} l_pts} l_line} hull
    // } pts } line } hull
  ];

  //println!("ast: {:?}", ast);
  assert!(bitype::synth_exp(None, &ctx, &ast) != None)
}
