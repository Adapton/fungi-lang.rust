#![recursion_limit="128"]
#[macro_use]
extern crate iodyn_lang;

use std::rc::Rc;
use iodyn_lang::bitype;
use iodyn_lang::tgt_ast::*;

// Sequence Examples from the following paper:
//
// [Refinment types for precisely-named cache locations](https://arxiv.org/pdf/1610.00097.pdf)
//

#[test]
fn fungi_seq() {

    let fungi_seq : Exp = tgt_exp![
        // always Nats
        type Vec = (user(Vec))

        let vec_filter:( Thk[0]
            Vec Nat -> (
                (Thk[0] Nat -> (F Bool |> {0;0}) |> {0;0}) ->
                (F Vec Nat |> {0;0}) |> {0;0}
            ) |> {0;0}
        ) = {
            unimplemented
        }

        let vec_map:( Thk[0]
            Vec Nat -> (
                (Thk[0] Nat -> (F Nat |> {0;0}) |> {0;0}) ->
                (F Vec Nat |> {0;0}) |> {0;0}
            ) |> {0;0}
        ) = {
            unimplemented
        }

        type Seq = (
            rec Seq.#X.#Y.
            (+ Vec 
             + (exists (X1,X2,X3)   :NmSet | (X1%X2%X3=X).
                exists (Y1,Y2,Y3,Y4):NmSet | (Y1%Y2%Y3%Y4=Y).
                x Nm[X1] x Nat
                x Ref[Y1](Seq[X2][Y2])
                x Ref[Y3](Seq[X3][Y4]))
            )
        )

        let nums:(Seq[X][Y] Nat) = { unimplemented }

        let rec max:(
            Thk[0] foralli (X,Y):NmSet.
                Seq[X][Y] Nat -> (F Nat |>
                    {(#x.{x,@1} % {x,@2}) X; 0})
                |> {0;0}
        ) = {
            #seq. unroll seq seq. match seq {
                vec => { {force vec_max} vec }
                bin => {
                    let (n,_x,l,r) = {ret bin}
                    let (unused, ml) = { memo{n,(@1)}{ {force max} {!l} } }
                    let (unused, mr) = { memo{n,(@2)}{ {force max} {!r} } }
                    if { mr < ml } {ret ml} else {ret mr}
                }
            }
        }
        
        let rec filter:(
            Thk[0] foralli (X,Y):NmSet.
                (Seq[X][Y] Nat) -> (
                    (Thk[0] Nat -> (F Bool |> {0;0}) |> {0;0}) ->
                    (F Nat |> {(#x.{x,@1} % {x,@2}) X; 0})
                    |> {0;0}
                ) |> {0;0}
        ) = {
            #seq. #f. unroll match seq {
                vec => { {force vec_filter} f vec }
                bin => {
                    let (n,lev,l,r) = {ret bin}
                    let (rsl, sl) = { memo{n,(@1)}{ {force filter} f {!l} } }
                    let (rsr, sr) = { memo{n,(@2)}{ {force filter} f {!r} } }
                    // if left is empty, return the right
                    if {{force is_empty} sl} { ret sr }
                    else { // if right is empty, return the left
                        if {{force is_empty} sr} { ret sl }
                        else {
                            // neither are empty; construct SeqBin node:
                            ret roll inj2 (n,lev,rsl,rsr)
                        }
                    }
                }
            }
        }

        let rec map:(
            Thk[0] foralli (X,Y):NmSet.
                (Seq[X][Y] Nat) -> (
                    (Thk[0] Nat -> (F Nat |> {0;0}) |> {0;0}) ->
                    (F Nat |> {(#x.{x,@1} % {x,@2}) X; 0})
                    |> {0;0}
                ) |> {0;0}
        ) = {
            #seq. #f. unroll match seq {
                vec => { {force vec_map } f vec }
                bin => {
                    let (n,lev,l,r) = {ret bin}
                    let (rsl, sl) = { memo{n,(@1)}{ {force map} f {!l} } }
                    let (rsr, sr) = { memo{n,(@2)}{ {force map} f {!r} } }
                    ret roll inj2 (n,lev,rsl,rsr)
                }
            }
        }

        {force max} nums
    ];
    println!("{:?}", fungi_seq);
}
