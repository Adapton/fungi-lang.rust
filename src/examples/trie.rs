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
        idxtm WS_Bin   = (#x:NmSet.{@!}( (Bin) x         ));

        /// Trie_of_seq: Index functions for output names and pointers:
        idxtm    Join  = (#x:NmSet.    ( (Bin)^* x       ));
        idxtm    Join1 = (#x:NmSet.    ( (Bin)((Bin)^* x)));        
        idxtm WS_Join  = (#x:NmSet.{@!}( {Join}  x       ));
        idxtm WS_Join1 = (#x:NmSet.{@!}( {Join1} x       ));

        /// Trie_of_seq: Index functions for output names and pointers:
        idxtm    Trie  = (#x:NmSet.{@!}( {Join} x        ));
        idxtm WS_Trie  = (#x:NmSet.{@!}(( (Bin) x        )
                                        % (x * ({Join}x))));
    }
    
    let join:(
        Thk[0] foralli (X1, X2, Y1, Y2):NmSet.
            0 Set[X1][Y1] ->
            0 Set[X2][Y2] ->
        { {WS_Join} (X1%X2); Y1%Y2 }
        F Set
            [(Join)(X1 % X2)]
            [{WS_Join}(X1 % X2)]
    ) = {
        ret thunk fix join. #set1. #set2. match set1 {
            on1 => { match set2 {
                on2  => { unimplemented }
                bin2 => { unimplemented }
            }}
            bin1 => { match set2 {
                on2  => { unimplemented }
                bin2 => {
                    // XXX
                    unimplemented
                }
            }}
        }
    }

    let trie:(
        Thk[0] foralli (X,Y):NmSet.
            0 Seq[X][Y] ->
        { {WS_Trie} X ; Y }
        F Set[X][{WS_Trie} X]
    ) = {
        ret thunk fix trie. #seq. match seq {
            on => { ret roll inj1 on }
            bin => {
                unpack (X1,X2,X3,Y1,Y2,Y3,Y4) bin = bin
                let (n,lev,l,r) = {ret bin}
                let (rsl, _l) = { memo{n,(@1)}{ {force trie}[X2][Y2]{!l} } }
                let (rsr, _r) = { memo{n,(@2)}{ {force trie}[X3][Y4]{!r} } }
                let trie      = { ws (nmfn [#x:Nm. ~n * x]) {
                    {force join}
                    [({Trie}X1)][({Trie}X2)][({WS_Trie}X1)][({WS_Trie}X2)]
                    {!rsl} {!rsr}
                }}
                /* TODO --- Macro for this (common) use case of `ws` with a surrounding `let`:
                let trie      =(n){
                    {force join}[0][0][0][0]
                    {!rsl} {!rsr}
                }*/
                ret trie
            }
        }
    }

    ret 0
]}
