#[macro_use]
extern crate iodyn_lang;

use iodyn_lang::ast::*;

// #[test]
// fn test_main_algo() {
//   let ctxt = TCtxt::Empty
//     .var(make_val![pts],make_type![Seq((nat x nat))])
//     .var(make_val![line],make_type![((nat x nat) x (nat x nat))])
//     .var(make_val![hull],make_type![Seq((nat x nat))])
//     .var(make_val![true],make_type![bool])
//   ;

//   let ast = make_exp![
//     // TODO: write these supplemental functions
//     let highest = {lam l.lam r. ret l}
//     let make_r_line = {lam m.lam l.ret l}
//     let make_l_line = {lam l.lam m.ret l}
//     let above_line = {lam ln.lam pt.ret true}
//     ret {{{fix qh.lam pts.lam line.lam hull.
//       // if pts is empty return hull else 
//       let mid = { SeqFoldUp(pts,(0,0),{lam p.ret p},highest) }
//       let hull = {
//         let r_line = {{make_r_line} (mid, line)}
//         let r_pts = {SeqFilter(pts,{above_line} r_line)}
//         ret {{{force qh} r_pts} r_line} hull
//       }
//       let hull = {SeqAppend(hull,mid)}
//       let l_line = {{make_l_line} (line, mid)}
//       let l_pts = {SeqFilter(pts,{above_line} l_line)}
//       ret {{{force qh} l_pts} l_line} hull
//     } pts } line } hull
//   ];

//   //println!("ast: {:?}", ast);
//   assert!(bitype::synth_exp(None, &ctx, &ast) != None)
// }
