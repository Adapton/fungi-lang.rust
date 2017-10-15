#[macro_use]
extern crate iodyn_lang;

use iodyn_lang::ast::*;

// # Incremental rank sort
//
// Below, we consider an _incremental_ variation of rank sort, as
// expressed implicitly in IODyn.  Then, we consider several naming
// strategies, as expressed by IODyn compilation hints. 
//
// ### (Non-incremental) rank sort vs (non-incremental) comparison-based sorts
//
// As preparation for incremental rank sort, first recall the
// _ordinary_ (fixed-input) rank sort algorithm, aka the "postoffice
// sort" algorithm.  In contrast to sorting algorithms that only
// require clients provide a notion of pair-wise element comparison,
// rank sort also requires a way of _interpolating_ between two
// elements, or otherwise quantizing the space of possible elements,
// to break it into partitioned subspaces ("bins") _before_ seeing any
// of the elements to be sorted.  Later, as it sees each element,
// ranksort efficiently places the element into one of the prepared
// bins (e.g., by doing an imperative array-based update).  Since the
// bins are sorted, by definition, the elements are sorted.  In sum,
// rank sort compares input elements to bins, sometimes implicitly
// (e.g., with array operations), and does not compare input elements
// to other input elements.
//
// For real-world intuition, think of how one would sort physical
// post-marked envelopes by their zip codes.  Before seeing any
// envelopes, we know how to create "bins" for all possible zip code
// prefixes (or if we have enough space for bins, e.g., in a computer
// program, we create a bin for each unique zip code).  As we see each
// envelope, we simply place it into the right bin, perhaps with other
// envelopes that also fell into that bin (no further comparison
// between these envelopes occurs, however).
// 
// ### Incremental rank sort in IODyn
//
// In our incremental version of rank sort, we wish to create the
// right number of bins, and for these choices to scale naturally as
// the input sequence grows or shrinks across incremental updates.  
//
// To do so, we assume a _measure_ on the elements (?? is that the
// right mathematical def here?), which permits us to take weighted
// averages of two elements and produce a third, interpolated element.
// We divide the sequence by interpolating and splitting it,
// recursively, until the sequence consists of equal elements, or it
// consists of base case that we can sort with another sorting
// primitive, e.g., VecSort.

// Issues:
//
// - need macro for `let (x,y) = {e1} {e2}` in both programs below

// /// This version of ranksort uses a stack to represent the output
// /// accumulator argument, sorted.
//
// #[test]
// fn rs_w_accumulator() {
//     let ast = make_exp![
//         fix rs. lam inp. lam sorted.
//            SeqFoldUp(inp, 
//             sorted,
//             lam elm. {StackPush(elm, sorted)},
//             lam l. lam r.
//                 let inp = {SeqAppend(l,r)}
//                 let ave = {{force seq_ave} inp}
//                 let eq_lt_gt = {SeqSplit3(inp, lam x. NatEq(x, ave), lam x. NatLte(x, ave))}
//                 let (eq,lte,gt) = {eq_lte_gt}
//                 let sorted = {{{force rs} gt}  sorted}
//                 let sorted = {SeqFoldSeq(eq, sorted, lam x. StackPush(x, sorted))}
//                 let sorted = {{{force rs} lte} sorted}
//                 ret sorted
//            )
//     ];
//     ()
// }
