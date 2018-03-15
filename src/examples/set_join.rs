#[test]
pub fn listing () { fgi_listing_expect![[Expect::Failure]
    decls {
        /// Optional natural numbers:
        type OpNat = (+ Unit + Nat );
        
        /// Levels (as numbers), for level trees.
        type Lev = ( Nat )
            
        /// Sequences (balanced binary level trees), whose leaves
        /// are optional natural numbers:
        type Seq = (
            rec seq. foralli (X,Y):NmSet.
                (+ (+ Unit + Nat)
                 + (exists (X1,X2,X3)   :NmSet | ((X1%X2%X3)=X:NmSet).
                    exists (Y1,Y2,Y3,Y4):NmSet | ((Y1%Y2%Y3%Y4)=Y:NmSet).
                    x Nm[X1] x Lev
                    x Ref[Y1](seq[X2][Y2])
                    x Ref[Y3](seq[X3][Y4]))
                )
        );                
            
        /// Sets (balanced binary hash tries), whose leaves are
        /// optional natural numbers:
        type Set = (
            rec set. foralli (X,Y):NmSet.
                (+ (+ Unit + Nat)
                 + (exists (X1,X2,X3)   :NmSet | ((X1%X2%X3)=X:NmSet).
                    exists (Y1,Y2,Y3,Y4):NmSet | ((Y1%Y2%Y3%Y4)=Y:NmSet).
                    x Nm[X1]
                    x Ref[Y1](set[X2][Y2])
                    x Ref[Y3](set[X3][Y4]))
                )
        );                

        /// Structural recursion over a binary tree (output names and pointers):
        idxtm    Bin   = (#x:Nm.         {x,@1} % {x,@2}  );
        idxtm    Bin1  = (#x:Nm.         {x,@1}           );
        idxtm    Bin2  = (#x:Nm.                  {x,@2}  );
        idxtm WS_Bin   = (#x:NmSet.{@!}( (Bin)  x         ));
        idxtm WS_Bin1  = (#x:NmSet.{@!}( (Bin1) x         ));
        idxtm WS_Bin2  = (#x:NmSet.{@!}( (Bin2) x         ));

        /// Trie_join: Index functions for output names and pointers:
        idxtm    Join  = (#x:NmSet.    ( (Bin)((Bin)^* x)));
        idxtm WS_Join  = (#x:NmSet.{@!}( {Join}  x       ));
    }

    // Create a named binary node, with two leaves
    let bin_leaf_leaf:(
        Thk[0] foralli X:NmSet.
            0 Nm[X] ->
            0 OpNat ->
            0 OpNat ->
        { {WS_Bin}X ; 0 }
        F Set[X][{WS_Bin}X]
    ) = {
        ret thunk #n.#x.#y.
        let l :(Ref[{WS_Bin1} X]Set[0][0]) = {
            ref{n,(@1)}(roll inj1 x)
        }
        let r :(Ref[{WS_Bin2} X]Set[0][0]) = {
            ref{n,(@2)}(roll inj1 y)
        }
        ret roll inj2 pack (
            X, 0, 0,
            ({WS_Bin1} X), 0,
            ({WS_Bin2} X), 0,
        )(n, l, r)
    }

    // Create a named binary node, with two leaves
    let join_leaves:(
        Thk[0] foralli X:NmSet.
            0 Nm[X] ->
            0 OpNat ->
            0 OpNat ->
        { {WS_Bin}X ; 0 }
        F Set[X][{WS_Join}X]
    ) = {
        //ret thunk #n.#x.#y.
        //{force bin_leaf_leaf}[X] n x y
        unimplemented
    }
    
    let join:(
        Thk[0] foralli (X0, X1, X2, Y1, Y2):NmSet.
            0 Nm[X0] ->
            0 Set[X1][Y1] ->
            0 Set[X2][Y2] ->
        {
            {WS_Join}(X0%X1%X2)
                ;
            Y1 % ( Y2 % (
                ( {WS_Join}(X0%X1%X2) )))
        }
        F Set
            [{   Join}(X0 % X1 % X2)]
            [{WS_Join}(X0 % X1 % X2)]
    ) = {
        ret thunk fix join.
            #n. #set1. #set2.
        match set1 {
            on1 => { match set2 {
                on2  => {
                    {force join_leaves}[X0] n on1 on2
                }
                bin2 => {
                    unimplemented
                }
            }}
            bin1 => { match set2 {
                on2  => {
                    unimplemented
                }
                bin2 => {
                    // XXX
                    unimplemented
                }
            }}
        }    
    }

    ret 0
]}
/*
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
*/
