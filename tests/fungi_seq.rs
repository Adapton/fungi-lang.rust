#![recursion_limit="1128"]
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

        //
        // --- === Vector Module === ---
        //
        type Vec = (user(Vec))
            
        let vec_filter:(
            Thk[0]
                0 (Vec Nat) ->
                0 (Thk[0] 0 Nat -> 0 F Bool) ->
                0 F Vec Nat
        ) = {
            unimplemented
        }

        let vec_map:(
            Thk[0]
                0 Vec Nat ->
                0 (Thk[0] 0 Nat -> 0 F Nat) ->
                0 F Vec Nat
        ) = {
            unimplemented
        }

        //
        // --- === Sequence Module === ---
        //
        type Seq = (
            rec Seq.#X.#Y.
            (+ Vec 
             + (exists (X1,X2,X3)   :NmSet | (X1%X2%X3=X).
                exists (Y1,Y2,Y3,Y4):NmSet | (Y1%Y2%Y3%Y4=Y).
                x Nm[X1] x Nat // <-- Name and level
                x Ref[Y1](Seq[X2][Y2])
                x Ref[Y3](Seq[X3][Y4]))
            )
        )

        let rec max:(
            Thk[0]
                0 foralli (X,Y):NmSet.
                0 Seq[X][Y] Nat ->
                F Nat
                |> {(#x.{x,@1} % {x,@2}) X; 0}
        ) = {
            #seq. unroll seq seq. match seq {
                vec => { {force vec_max} vec }
                bin => {
                    let (n,_x,l,r) = {ret bin}
                    let (_l, ml) = { memo{n,(@1)}{ {force max} {!l} } }
                    let (_r, mr) = { memo{n,(@2)}{ {force max} {!r} } }
                    if { mr < ml } {ret ml} else {ret mr}
                }
            }
        }
        
        let rec is_empty:(
            Thk[0]
                0 foralli (X,Y):NmSet.
                0 (Seq[X][Y] Nat) ->
                F Bool
                |> {0;Y}
        ) = {
            #seq. unroll match seq {
                vec => { {force vec_is_empty} vec }
                bin => {
                    let (n,lev,l,r) = {ret bin}
                    if {{force is_empty} {!l}} {
                        {{force is_empty} {!r}}
                    } else {
                        ret false
                    }
                }
            }
        }
        
        let rec is_singleton:(
            Thk[0]
                0 foralli (X,Y):NmSet.
                0 (Seq[X][Y] Nat) ->
                0 F Bool
        ) = {
            #seq. unroll match seq {
                vec => { {force vec_is_singleton} vec }
                bin => { ret false }
            }
        }

        let rec monoid:(
            Thk[0] foralli (X,Y):NmSet.
                0 (Seq[X][Y] Nat) ->
                0 (Thk[0] 0 Nat -> 0 Nat -> 0 F Bool) ->
                F Nat
                |> {(#x.{x,@1} % {x,@2}) X; 0}
        ) = {
            #seq. #binop. unroll seq seq. match seq {
                vec => { {force vec_monoid} vec }
                bin => {
                    let (n,_x,l,r) = {ret bin}
                    let (_l, ml) = { memo{n,(@1)}{ {force monoid} {!l} } }
                    let (_r, mr) = { memo{n,(@2)}{ {force monoid} {!r} } }
                    {{force binop} ml mr}
                }
            }
        }
        
        let rec map:(
            Thk[0] foralli (X,Y):NmSet.
                0 (Seq[X][Y] Nat) ->
                0 (Thk[0] 0 Nat -> 0 F Nat)
                F Nat
                |> {(#x.{x,@1} % {x,@2}) X; Y}
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
               
        let rec filter:(
            Thk[0] foralli (X,Y):NmSet.
                0 (Seq[X][Y] Nat) ->
                0 (Thk[0] 0 Nat -> (0 F Bool)) ->
                F Nat
                |> {(#x.{x,@1} % {x,@2}) X; Y}
        ) = {
            #seq. #f. unroll match seq {
                vec => { {force vec_filter} f vec }
                bin => {
                    let (n,lev,l,r) = {ret bin}
                    let (rsl, sl) = { memo{n,(@1)}{ {force filter} f {!l} } }
                    let (rsr, sr) = { memo{n,(@2)}{ {force filter} f {!r} } }
                    if {{force is_empty} sl} { ret sr }
                    else { if {{force is_empty} sr} { ret sl }
                           else { ret roll inj2 (n,lev,rsl,rsr) }
                    }
                }
            }
        }

        let rec map_filter:(
            Thk[0] foralli (X,Y):NmSet.
                0 (Seq[X][Y] Nat) ->
                0 (Thk[0] 0 Nat -> 0 F (+ Unit + Nat)) ->
                F Nat
                |> {(#x.{x,@1} % {x,@2}) X; Y}
        ) = {
            #seq. #f. unroll match seq {
                vec => { {force vec_map_filter} f vec }
                bin => {
                    let (n,lev,l,r) = {ret bin}
                    let (rsl, sl) = { memo{n,(@1)}{ {force map_filter} f {!l} } }
                    let (rsr, sr) = { memo{n,(@2)}{ {force map_filter} f {!r} } }
                    if {{force is_empty} sl} { ret sr }
                    else { if {{force is_empty} sr} { ret sl }
                           else { ret roll inj2 (n,lev,rsl,rsr) }
                    }
                }
            }
        }


        //
        // --- === List Module === ---
        //
        type List = (
            rec Seq.#X.#Y.
            (+ Vec // <-- Basecase with no level, name or ref
             + (exists (X1,X2,X3)   :NmSet | (X1%X2%X3=X).
                exists (Y1,Y2,Y3,Y4):NmSet | (Y1%Y2%Y3%Y4=Y).
                x Nm[X1] x Nat // <-- Name and level
                x Vec // <-- elements here (a chunk in a vector)
                x Ref[Y1](Seq[X2][Y2])) // <-- Tail pointer
            )
        )

        // Convert sequence to the isomorphic list
        let rec list_l2r_rec: (
            Thk[0] foralli (X,X1,X2,X3, Y,Y1,Y2):NmSet | ((X1%X2%X3)=X)and((Y1%Y2%Y3)=Y).
                0 (Seq[X1][Y1] Nat) ->
                0 (x Nm[X3] x Nat x Ref[Y3](List[X2][Y2])) ->
                F List[X][Y]
                |> {X;Y}
        ) = {
            #seq. #rest. unroll match seq {
                vec => { ret roll inj2 (n,lev,vec,rest) }
                bin => {
                    let (n,lev,l,r) = {ret bin}
                    let (rr, _) = { memo{n,(@2)}{ {force list_l2r_rec} rest       {!r} } }
                    let (_, ll) = { memo{n,(@1)}{ {force list_l2r_rec} (n,lev,rr) {!l} } }
                    { ret ll }
                }
            }
        }        

        // Convert sequence to the isomorphic list
        // -- special rightmost recursion
        // (no accum info)
        let rec list_l2r_rmost: (
            Thk[0] foralli (X,Y):NmSet.
                0 (Seq[X][Y] Nat) ->
                F List[X][X]
                |> {X;Y}
        ) = {
            #seq. #rest. unroll match seq {
                vec => { ret roll inj1 vec }
                bin => {
                    let (n,lev,l,r) = {ret bin}
                    let (rr, _) = { memo{n,(@1)}{ {force list_l2r_rmost}          {!r} } }
                    let (_, ll) = { memo{n,(@2)}{ {force list_l2r_rec} (n,lev,lr) {!l} } }
                    { ret ll }
                }
            }
        }

        // Convert sequence to the isomorphic list, left-to-right
        let rec list_l2r: (
            Thk[0] foralli (X,Y):NmSet.
                0 (Seq[X][Y] Nat) ->
                F List[X][X]
                |> {X;Y}
        ) = { #seq. {force list_l2r_rmost} seq }


        // Convert a list into a balanced level tree (a sequence), with a single pass
        let rec seq_of_list: (
            Thk[0] foralli (X,Y):NmSet.                
                0 List[X][Y] ->
                F Seq[X][Y]
                |> {X;Y}
        ) = {
            unimplemented
        }
        
        // dummy "main":
        let nums:(Seq[X][Y] Nat) = { unimplemented }
        {force max} nums
    ];
    println!("{:?}", fungi_seq);
}


/*

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

*/
