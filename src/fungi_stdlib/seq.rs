/*!

# Sequences in Fungi: 

## Linked lists vs Level trees
        
In most functional languages, **linked lists** play a central role in
organizing sequential data, the way that arrays play a central role in
imperative languages.

In Fungi, computations have the potential to be incremental, and as a
result, we reconsider the role of linked lists in our functional
programs.  In Fungi, linked-lists represent "iterators" --- lists
sometimes organize sequences as their are processed or transformed ---
but in Fungi, lists not the data structure for storing or editing that
sequence data, or for aggregating it with folds or other iteration
patterns.

Instead, to organize sequences for accesses, updates or incremental
folds, Fungi programs use balanced **level trees**.  In particular,
before we iterate over a linked list, we create a balanced level tree
from its elements to better organize later incremental reuse, via
change propagation.

## Level trees

Level trees are balanced, binary trees that represent sequences of
elements, stored at their leaves.  A level tree permits O(log n) reads
and writes to the sequence, where writes may overwrite, insert or
remove elements from the sequence.

When the editor updates a sequence, they often want to do so
imperatively.  When the archivist updates a sequence, they do so
functionally, such that the update preserves (and does not overwrite)
existing store data.

Below, we focus on the archivist's operations for sequences:
Conversion to and from lists, and various flavors of folding (over
level trees, not lists).

During change propagation over the archivist's incremental folds, this
balanced tree structure ensures that the (isomorphic) dependency graph
it induces is shallow.  In particular, from any root of a fold to any
thunk it calls (transitively), there are at most O(log n) transitive
force edges to clean or dirty.

## Related

 - See also [Refinement types for precisely-named cache locations](https://arxiv.org/pdf/1610.00097.pdf)

*/


#![recursion_limit="1128"]
#[macro_use]

use std::rc::Rc;

use bitype;
use tgt_ast::*;

pub fn exp () -> Exp { tgt_exp![
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
        rec Seq. foralli (X,Y):NmSet.
            (+ Vec 
             + (exists (X1,X2,X3)   :NmSet | (X1%X2%X3=X).
                exists (Y1,Y2,Y3,Y4):NmSet | (Y1%Y2%Y3%Y4=Y).
                x Nm[X1] x Nat // <-- Name and level
                x Ref[Y1](Seq[X2][Y2])
                x Ref[Y3](Seq[X3][Y4]))
            )
    )
        
    let rec max:(
        Thk[0] foralli (X,Y):NmSet.
            0 Seq[X][Y] Nat ->
            ~~ {(#x.{x,@1} % {x,@2}) X; 0} ~~
            F Nat
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
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y] Nat) ->
            ~~ 0; Y ~~
            F Bool
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
        Thk[0] foralli (X,Y):NmSet.
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
            ~~ (#x.{x,@1} % {x,@2}) X; 0 ~~
            F Nat        
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
            ~~ (#x.{x,@1} % {x,@2}) X; Y ~~
            F Nat
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
            ~~ (#x.{x,@1} % {x,@2}) X; Y ~~
            F Nat
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
            ~~ (#x.{x,@1} % {x,@2}) X; Y ~~
            F Nat
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
    // --- === List (Sub) Module === ---
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
            ~~ X; Y ~~
            F List[X][Y]
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
            ~~ X; Y ~~
            F List[X][X]
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
            ~~ X; Y ~~
            F List[X][X]
    ) = { #seq. {force list_l2r_rmost} seq }
    
    
    // Convert a list into a balanced level tree (a sequence), with a single pass
    let rec seq_of_list: (
        Thk[0] foralli (X,Y):NmSet.                
            0 List[X][Y] ->
            ~~ X;Y ~~
            F Seq[X][Y]
    ) = {
        unimplemented
    }

    // Dummy "main"
    ret 0
]}
