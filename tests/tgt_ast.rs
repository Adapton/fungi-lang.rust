#[macro_use]
extern crate iodyn_lang;

// Examples from the following paper:
// [Refinment types for precisely-named cache locations](https://arxiv.org/pdf/1610.00097.pdf)


#[test]
fn examples() {

  use std::rc::Rc;
  use iodyn_lang::bitype;
  use iodyn_lang::tgt_ast::*;
  // use iodyn_lang::tgt_ast::cons::*;

  let ctx : TCtxt = TCtxt::Empty;

  let max : Exp = tgt_exp![
    type Vec = {}
    type Seq[X] = { (+ Vec + (x Nm x Nat x Ref[X] Seq[X] x Ref[X] Seq[X])) }
    let nums:(Seq[X]) = { unimplemented }
    let vec_max:(Vec -> F Nat) = { unimplemented }
    let max:(
      All X:NmSet.
      Seq[X] -> F Nat
      |> (#x:Nm.[x.1] % [x.2])[X]
    ) = {
      fix max.#seq.
      match seq {
        vec => { vec_max vec },
        bin => {
          let (n,_,l,r) = { ret bin }
          let (_,ml) = { memo[n.1](max !l) }
          let (_,mr) = { memo[n.2](max !r) }
          if (ml > mr) then {ret ml} else {ret mr}
        }
      }
    }
    {force max} nums
  ];
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
