#![recursion_limit="128"]
#[macro_use]
extern crate iodyn_lang;

// Examples from the following paper:
// [Refinment types for precisely-named cache locations](https://arxiv.org/pdf/1610.00097.pdf)


#[test]
fn examples() {
    use std::rc::Rc;
    use iodyn_lang::bitype;
    use iodyn_lang::tgt_ast::*;
    use iodyn_lang::tgt_vis::*;
    // use iodyn_lang::tgt_ast::cons::*;
    
    //let ctx : TCtxt = TCtxt::Empty;

    let max : Exp = tgt_exp![
        type Vec = (#T.user(Vec))
        // Seq[X,Y]:
        // Refinement type for a nominal, level-tree data structure,
        // ...      with (unallocated) names in X
        // ... and (allocated) pointer names in Y
        //
        type Seq = (
            // Ordering here is important: The recursive type name T
            // should refer to the type that is parameteric in X and
            // Y; the version below has a fixed choice for X and Y for
            // all recursive unrollings.
            // (See my other version of type Seq, for filter, below).
            rec Seq. #X.#Y.#T.
            (+ Vec T
             + (exists (X1,X2,X3)   :NmSet | (X1%X2%X3=X).
                exists (Y1,Y2,Y3,Y4):NmSet | (Y1%Y2%Y3%Y4=Y).
                x Nm[X1] x Nat
                // Seq vs T ??
                x Ref[Y1](Seq[X2][Y2] T)
                // Seq vs T ??
                x Ref[Y3](Seq[X3][Y4] T))
            )
        )
        let nums:(Seq[X][Y] Nat) = { unimplemented }        
        let vec_max:(Thk[0] Vec Nat -> (F Nat |> {0;0}) |> {0;0}) = {
            unimplemented
        }
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
                    //
                    // Left recursion:
                    // sugar version #1 (most sugared)
                    let (unused, ml) = { memo{n,(@1)}{ {force max} {!l} } }
                    // sugar version #2 (name construction first; then memo construct)
                    let n1 = {n,(@1)}
                    let (unused, ml) = { memo(n1){ {force max} {!l} } }
                    //
                    // Right recursion:
                    // non-sugar version (all sub-expressions are explicit)
                    let nf = { ret nmfn #n.#v.n,v }
                    let n2 = { [nf] n (@2) }
                    let mr = {
                        let t = { thk n2
                            let rv = {get r}
                            {force max} rv
                        }
                        {force t}
                    }
                    if { mr < ml } {ret ml} else {ret mr}
                }
            }
        }
        {force max} nums
    ];
    println!("{:?}", max);


    let filter : Exp = tgt_exp![
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

        // Syntax for idiomatic recursive types
        // (avoid double-naming, as with `let rec`)?
        //
        //   type rec T = (A)  ==>  type T = (rec T. A)
        //
        // Using RHS below (not LHS yet, but maybe?)
        //
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
    
    println!("{:?}", label_exp(filter, &mut 0));

}

/* 

All listings from paper (in LaTeX source markup):
===========================================================

max : $\All{X:\namesetsort}$
      $\SeqNat{X} -> \Nat$
    $|>~ \big( \lam{x:\namesort} \{ x@@1 \} \disj \{ x@@2 \} \big)  [[ X ]]$

max seq = match seq with
| SeqLf(vec) => vec_max vec
| SeqBin(n,_,l,r) =>
 let (_,ml) = memo[n@1](max !l)
 let (_,mr) = memo[n@2](max !r)
 if ml > mr then ml else mr

----------------------------------

vec_max   : $\VecNat -> \Nat$
vec_filter: $\VecNat -> (\Nat -> \Bool) -> \VecNat$

----------------------------------

filter : $\All{X:\namesetsort}$
         $\SeqNat{X} -> (\Nat -> \Bool) -> \SeqNat{X}$
       $|>~ \big( \lam{x:\namesort} \{ x@@1 \} \disj \{ x@@2 \} \big)  [[ X ]]$

filter seq pred = match seq with
| SeqLf(vec) => SeqLf(vec_filter vec pred)
| SeqBin(n, lev, l, r) =>
 let (rl,sl) = memo[n@1](filter !l pred)
 let (rr,sr) = memo[n@2](filter !r pred)
 match (is_empty sl, is_empty sr)
 | (false,false) => SeqBin(n, lev, rl, rr)
 | (_,true) => sl 
 | (true,_) => sr

------------------------------------------

trie :
  $\All{X:\namesetsort}$
    $\SeqNat{X} -> \SetNat{X}$
 $|>~ \big( \lam{x{:}\namesort} ( \lam{y{:}\namesort} \{ x@@y \} ) [[ \widehat{\textsf{join}}(X)]] \big) [[ X ]]$

trie seq = match seq with
| SeqLf(vec) => trie_lf vec
| SeqBin(n,_,l,r) =>
 let (tl,_) = memo[n@1](trie !l)
 let (tr,_) = memo[n@2](trie !r)
 let trie =[n] join n tl tr
 trie

$\textrm{where:}$
 $\widehat{\textsf{join}}(X) :\equiv \big( \lam{x{:}\namesort}\{x@@1\} \disj \{x@@2\} \big)^\ast [[ X ]]$

------------------------------------------------

join : $\All{X{\disj}Y:\namesetsort}$
       $\SetNat{X} -> \SetNat{Y} -> \SetNat{\widehat{\textsf{join}}(X{\disj}Y)}$
    $|>~\widehat{\textsf{join}}(X{\disj}Y)$

join n l r = match (l,r) with
| SetLf(l), SetLf(r) => join_vecs n l r
| SetBin(_,_,_), SetLf(r) =>
             join n@1 l (split_vec n@2 r)
| SetLf(l), SetBin(_,_,_) =>
             join n@1 (split_vec n@2 l) r
| SetBin(ln,l0,l1), SetBin(rn,r0,r1) => 
 let (_,j0) = memo[ln@1](join ln@2 l0 r0)
 let (_,j1) = memo[rn@1](join rn@2 l1 r1)
 SetBin(n, j0, j1)

------------------------------------------------------


qh1 :
  $\All{X{\disj}Y{\disj}Z:\namesetsort}$
    $\Line{X} -> \SeqNat{Y} -> \SeqNat{Z} -> \SeqNat{Y{\disj}Z}$
  $|>~ \big( \lam{x{:}\namesort} ( \lam{y{:}\namesort} \{ x@@y \} ) [[ \widehat{\textsf{qh}_1}(X)]] \big) [[ X ]]$

qh1 ln pts h = 
 let p =[ln@1] max_pt ln pts
 let l =[ln@2] filter (ln.0,p) pts
 let r =[ln@3] filter (p,ln.1) pts
 let h = memo[ln@1](qh1 (p,ln.1) r h)
 let h = push[ln@2](p,h)
 let h = memo[ln@3](qh1 (ln.0,p) l h)
 h

$\widehat{\textsf{qh}_1}(X) :\equiv
\arrayenvl{
~~\big( \lam{a} \{1@@a, 2@@a, 3@@a\} \big)
[[ \widehat{\textsf{bin}}[[ X ]] ]]
\\ \disj  \{1,2,3\}
}

--------------------------------------------------

qh2 :
  $\All{X{\disj}Y{\disj}Z:\namesetsort}$
    $ \Line{X} -> \SeqNat{Y} -> \SeqNat{Z} -> \SeqNat{Y{\disj}Z}$
  $|>~ \big( \lam{y{:}\namesort} \{ 1@@y \} \disj \{ 2@@y \} \big)^\ast [[ \widehat{\textsf{qh}_2}(Y{\disj}Z) ]]$

qh2 ln pts h = 
 let p =[3@1] max_pt ln pts
 let l =[3@2] filter (ln.0,p) pts
 let r =[3@3] filter (p,ln.1) pts
 let h = memo[1]([1](qh2 (p,ln.1) r h))
 let h = push[2](p,h)
 let h = memo[3]([2](qh2 (ln.0,p) l h))
 h

$\widehat{\textsf{qh}_2}(X) :\equiv
\arrayenvl{
~~\big( \lam{a} \{3@@1@@a, 3@@2@@a, 3@@3@@a\} \big)
[[ \widehat{\textsf{bin}} [[ X ]] ]]
\\ \disj \{1,2,3\}
}

-----------------------------------------------------------

*/
