#![recursion_limit="128"]
#[macro_use]
extern crate fungi_lang;

#[test]
pub fn trie () {
  use std::thread;
  let child =
    thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || { 
      trie2()
    });
  let _ = child.unwrap().join();
}
pub fn trie2() {
    use std::rc::Rc;
    use fungi_lang::ast::*;
    use fungi_lang::bitype::*;
    use fungi_lang::vis::*;


    let bundle : Bundle = fgi_bundle![
    //let trie_ast = fgi_exp![
        decls {
            /// Optional natural numbers:
            type OpNat = (+ Unit + Nat );
            
            /// Levels (as numbers), for level trees.
            type Lev = ( Nat )

            /// Abstracted vector, represents an array of Nats
            type NatVec = ( Unit )
                
            /// Sequences (balanced binary level trees), whose leaves
            /// are optional vectors of natural numbers:
            type Seq = (
                rec seq. foralli (X,Y):NmSet.
                    (+ (+ Unit + NatVec)
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
                    (+ (+ Unit + NatVec)
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

            /// Same as above but only one side
            idxtm WS_Bin_1 = ( #x:NmSet.{@!}(x * {@1}))
            idxtm WS_Bin_2 = ( #x:NmSet.{@!}(x * {@2}))

            /// Trie_join: Index functions for output names and pointers:
            idxtm    Join  = (#x:NmSet.    ( (Bin)((Bin)^* x))); // one app minimum
            idxtm WS_Join  = (#x:NmSet.{@!}( {Join}  x       ));

            /// Trie_of_seq: Index functions for output names and pointers:
            idxtm    Trie  = (#x:NmSet.    ( {Join} x        ));
            idxtm WS_Trie  = (#x:NmSet.{@!}( {Join} x        ));
        }

        let join_vecs:( Thk[0] foralli (X,Y):NmSet.
            0 Nm[X] -> 0 NatVec -> 0 NatVec ->
            {{WS_Bin} X; 0} F Set[X][{WS_Bin} X]
        ) = {
            ret thunk #nm. #v1. #v2.
            let lr:(Ref[{WS_Bin_1}X] Set[0][0]) = { ref {nm, (@1)} inj1 inj2 v1 }
            let rr:(Ref[{WS_Bin_2}X] Set[0][0]) = { ref {nm, (@2)} inj1 inj2 v2 }
            ret inj2 pack (X,0,0,{WS_Bin_1}X,0,{WS_Bin_2}X,0)
                (nm,0,lr,rr)
        }
        
        let split_vec:( Thk[0] foralli (X,Y):NmSet.
            0 Nm[X] -> 0 NatVec ->
            {{WS_Bin} X; 0} F Set[X][{WS_Bin} X]
        ) = {
            ret thunk #nm. #vec.
            let vs : (x NatVec x NatVec) = {
                // vector ops with `vec`
                // split `vec` appropriate to trie
                unimplemented
            }
            let (v1,v2) = {ret vs}
            let bin = { {force join_vecs} nm v1 v2 }
            ret bin
        }
        
        // let join:(
        //     Thk[0] foralli (X0, X1, X2, Y1, Y2):NmSet.
        //         0 Nm[X0] ->
        //         0 Set[X1][Y1] ->
        //         0 Set[X2][Y2] ->
        //     {
        //         ({WS_Bin} X0)
        //         % ({WS_Join} (X1%X2))
        //     ;
        //         Y1 % Y2
        //         % ({WS_Bin} X0)
        //         % ({WS_Join} (X1%X2))
        //     }
        //     F Set
        //         [(Join)(X1 % X2)]
        //         [{WS_Join}(X1 % X2)]
        // ) = {
        //     ret thunk fix join. #nm. #set1. #set2. match set1 {
        //         on1 => { match set2 {
        //             on2  => { unimplemented }
        //             bin2 => { unimplemented }
        //         }}
        //         bin1 => { match set2 {
        //             on2  => { unimplemented }
        //             bin2 => {
        //                 // XXX
        //                 unimplemented
        //             }
        //         }}
        //     }
        // }

        // let trie:(
        //     Thk[0] foralli (X,Y):NmSet.
        //         0 Seq[X][Y] ->
        //     {
        //         {WS_Trie} X
        //             ;
        //         Y % ( {WS_Trie} X )
        //     }
        //     F Set[X][{WS_Trie} X]
        // ) = {
        //     ret thunk fix trie. #seq. match seq {
        //         on => { ret roll inj1 on }
        //         bin => {
        //             unpack (X1,X2,X3,Y1,Y2,Y3,Y4) bin = bin
        //             let (n,lev,l,r) = {ret bin}
        //             let (rsl, _l) = { memo{n,(@1)}{ {force trie}[X2][Y2]{!l} } }
        //             let (rsr, _r) = { memo{n,(@2)}{ {force trie}[X3][Y4]{!r} } }
        //             let trie      = { ws (nmfn [#x:Nm. ~n * x]) {
        //                 {force join}
        //                 [({Trie}X2)][({Trie}X3)][({WS_Trie}X2)][({WS_Trie}X3)]
        //                 {!rsl} {!rsr}
        //             }}
        //             ret trie
        //         }
        //     }
        // }

        ret 0
    ];

    // println!("trie AST");
    // println!("-------------");
    // println!("{:?}", trie_ast);
    // let typed = synth_exp(&Ext::empty(), &Ctx::Empty, &trie_ast);
    // println!("trie typing derivation");
    // println!("----------------------");
    // println!("typing success: {:?}", typed.clas.is_ok());
    // println!("{:?}", typed);

    write_bundle("target/trie.fgb", &bundle);
}
