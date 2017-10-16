#[macro_use]
extern crate iodyn_lang;

use std::rc::Rc;
use iodyn_lang::ast::*;

// Issues:
//
// - macro expansion error from Rust compiler:
//   "error: recursion limit reached while expanding the macro `split_comma`"
//
// - need macro for `let (x,y) = {e1} {e2}` in both programs below

/// This version of quicksort uses a stack to represent the output
/// accumulator argument, sorted.  This accumulator argument pattern
/// is used in (all?) prior SAC versions of quicksort.
#[test]
fn qs_w_accumulator() {
    let ast = make_exp![
        fix qs. lam inp. lam sorted.
           SeqFoldUp(inp,
            sorted,
            lam elm. {StackPush(elm, sorted)},
            lam l. lam r.{
                let piv = {SeqGetFirst(r)}
                let inp = {SeqAppend(l,r)}
                let lte_gt = {SeqSplit(inp, lam x. NatLte(x, piv))}
                let (lte,gt) = lte_gt
                let sorted = {{{force qs} gt}  sorted}
                let sorted = {{{force gs} lte} sorted}
                ret sorted
            })
    ];
    ()
}


/// This version of quicksort uses sequences to represent the sorted
/// output, and it uses SeqAppend to combine them.  It does not use an
/// accumulator argument, unlike (all?) versions of quicksort in the
/// SAC literature.
#[test]
fn qs_w_append() {
    let ast = make_exp![
        fix qs. lam inp.
           SeqFoldUp(inp,
            SeqEmpty,
            lam elm. {SeqSingleton(elm)},
            lam l. lam r.{
                let piv = {SeqGetFirst(r)}
                let inp = {SeqAppend(l,r)}
                let lte_gt = {SeqSplit(inp, lam x. NatLte(x, piv))}
                let (lte,gt) = lte_gt
                let sorted_lte = {{force qs} gt}
                let sorted_gt = {{force qs} lte}
                {SeqAppend(sorted_lte, sorted_gt)}
            })
    ];
    ()
}
