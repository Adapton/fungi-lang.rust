#![recursion_limit="128"]
#[macro_use]
extern crate fungi_lang;

mod fungi_stdlib_examples {
    fn seq_nat2() {
        use std::rc::Rc;
        use fungi_lang::ast::*;
        use fungi_lang::bitype::*;
        use fungi_lang::vis::*;
        use fungi_lang::eval::*;
        use fungi_lang::stdlib::seq::{seq_nat};
        
        let bundle : Bundle = fgi_bundle![            
            use seq_nat::*;
            ret 0
        ];
        write_bundle("target/seq_nat.fgb", &bundle);
    }

    #[test]
    fn seq_nat () {
        use std::thread;
        let child =
            thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || { 
                seq_nat2()
            });
        let _ = child.unwrap().join();
    }
}
    
#[test]
fn bitype () {
  use std::thread;
  let child =
    thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || { 
      bitype_short()
    });
  let _ = child.unwrap().join();
}
fn bitype_short() {
    use std::rc::Rc;
    use fungi_lang::ast::*;
    use fungi_lang::bitype::*;
    use fungi_lang::vis::*;
    use fungi_lang::eval::*;

    let bundle : Bundle = fgi_bundle![

        type Lev = ( Nat )
        type Seq = (
            rec seq. foralli (X,Y):NmSet.
            (+ (+ Unit + Nat)
             + (exists (X1,X2,X3)   :NmSet | ((X1%X2%X3)=(X):NmSet).
                exists (Y1,Y2,Y3,Y4):NmSet | ((Y1%Y2%Y3%Y4)=(Y):NmSet).
                x Nm[X1] x Lev
                x Ref[Y1](seq[X2][Y2])
                x Ref[Y3](seq[X3][Y4]))
            )
        )
            
        let nums:(Seq[X][Y]) = { unimplemented }

        let filter:(
            Thk[0] foralli (X,Y):NmSet.
                0 (Seq[X][Y]) ->
                0 (Thk[0] 0 Nat -> 0 F Bool) ->
            { (seq_sr) X; Y }
            F (Seq[X][X])
        ) = {
            ret thunk fix filter. #seq. #f. unroll match seq {
                opnat => {
                    match opnat {
                        _u => {
                            // no number to filter
                            ret roll inj1 (inj1 ())
                        }
                        n => {
                            // apply user-supplied predicate
                            if {{force f} n} {
                                // keep the number n
                                ret roll inj1 (inj2 n )
                            } else {
                                // filter out the number n
                                ret roll inj1 (inj1 ())
                            }
                        }
                    }
                }
                bin => {
                    unpack (X1,X2,X3,Y1,Y2,Y3,Y4) bin = bin
                    let (n,lev,l,r) = {ret bin}
                    let (rsl, sl) = { memo{n,(@1)}{ {force filter}[X2][Y2] {!l} f } }
                    let (rsr, sr) = { memo{n,(@2)}{ {force filter}[X3][Y4] {!r} f } }
                    if {{force is_empty} sl} { ret sr }
                    else { if {{force is_empty} sr} { ret sl }
                           else {
                               ret pack (X1,X2,X3, Z1,Z2,Z3,Z4)
                                   roll inj2 (n,lev,rsl,rsr)
                           }
                    }
                }
            }
        }    

        let pred : (Thk[0] 0 Nat -> 0 F Bool) = {ret thunk #x. unimplemented}
        let nums_out = {{force filter} pred nums}
        ret (nums, nums_out)
    ];
    write_bundle("target/bitype_filter.fgb", &bundle);
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
