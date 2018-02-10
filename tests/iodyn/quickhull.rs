#[macro_use]
extern crate iodyn_lang;

use std::rc::Rc;
use iodyn_lang::ast::*;
use iodyn_lang::bitype;

#[test]
fn test_main_algo() {
  let ctx = TCtxt::Empty
    // choose the point with the greatest vertical component
    .var("highest".to_string(),make_type![U (nat x nat) -> (nat x nat) -> F (nat x nat)])
    // make line from point and right side of line
    .var("make_r_line".to_string(),make_type![U (nat x nat) -> ((nat x nat) x (nat x nat)) -> F ((nat x nat) x (nat x nat))])
    // make line from left side of line and point
    .var("make_l_line".to_string(),make_type![U ((nat x nat) x (nat x nat)) -> (nat x nat) -> F ((nat x nat) x (nat x nat))])
    // check if point is above line
    .var("above_line".to_string(),make_type![U ((nat x nat) x (nat x nat)) -> (nat x nat) -> F bool])
  ;
  let ast = make_exp![
      [#line!()] {fix qh. lam pts. lam line. lam hull.
      [#line!()] let complete = { SeqIsEmpty(pts) }
      [#line!()] if (complete) then { ret hull } else {
        [#line!()] let mid = { SeqFoldUp(pts, (0,0), lam p.ret p, force highest) }
        [#line!()] let hull = {
          [#line!()] let r_line = { {force make_r_line} mid line }
          [#line!()] let r_pts = { [s [sym filt-r]] SeqFilter(pts, {force above_line} r_line) }
          [#line!()] [s [sym rec-r]] {force qh} r_pts r_line hull
        }
        [#line!()] let hull = { SeqAppend(hull, mid) }
        [#line!()] let l_line = { {force make_l_line} line mid }
        [#line!()] let l_pts = { [s [sym filt-l]] SeqFilter(pts, {force above_line} l_line) }
        [#line!()] [s [sym rec-l]] {force qh} l_pts l_line hull
      }} : Seq((nat x nat)) ->
          ((nat x nat) x (nat x nat)) ->
          Seq((nat x nat)) ->
          F Seq((nat x nat))
  ];

  //println!("ast: {:?}", ast);
  assert!(bitype::synth_exp(None, &ctx, &ast) != None)
}
