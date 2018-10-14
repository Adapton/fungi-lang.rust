pub mod dynamic_tests {
    /* 
     * Try the following at the command line:
     * 
     *  $ export FUNGI_VERBOSE_REDUCE=1
     *
     *  $ cargo test examples::list_nat_dedup::dynamic_tests::short -- --nocapture | less -R
     *
     */
    #[test]
    pub fn short_10_2() { use examples::{list_nat, list_nat_edit, list_nat_convert}; fgi_dynamic_trace!{
        [Expect::SuccessXXX]
        use super::*;
        use list_nat::*;
        use list_nat_edit::*;
        use list_nat_convert::*;
        
        /// Generate input (use old list type, and a conversion function into our newer list type)
        let list1  = {ws(@@inp1) {force gen} 10 }

        /// Allocate nil ref cell
        let refnil = {ref (@@nil) roll inj1 ()}
        
        /// Allocate emp trie
        let emp = {ref (@@emp) roll inj1 ()}

        /// Allocate archivist thunk: 
        /// when forced, it deduplicates the input list.
        let t = {ws (@@archivist) thk (@@comp) {
            let list2  = {ws(@@convert) {force convert} {!list1} }
            let list3 = { ref 0 list2 }
            let (_out, out) = {memo(@@dedup){{force dedup} list3 emp}}
            let count = {{force list_len} {!out}}
            let _x = {{force nat_print} count}
            ret (out, count)
        }}
 
        /// Initial run
        let outs_1 = {force t}

        /// First change: Insert element
        let b1 = {
            {force insert_after}[?] (@7) (@666) 2 {!list1}
        }

        /// Re-force archivist; Precipitates change propagation
        let outs_2 = {force t}

        /// Second change: Remove inserted element
        let b2 = {
            {force remove_after}[?] (@7) {!list1}
        }

        /// Re-force archivist; Precipitates change propagation
        let outs_3 = {force t}

        /// All sizes should be 10
        ret (outs_1, outs_2, outs_3)
    }}

    // Be careful: Without --release, this version overflows my stack.
    //#[test]
    pub fn big() { fgi_dynamic_trace!{
        [Expect::SuccessXXX]
        use super::*;
        use crate::examples::list_nat::*;
        use crate::examples::list_nat_convert::*;
        
        /// Generate input
        let list1  = {ws(@@inp) {force gen} 64 }

        /// Allocate nil ref cell
        let refnil = {ref (@@nil) roll inj1 ()}
        
        /// Allocate emp trie
        let emp = {ref (@@emp) roll inj1 ()}

        /// Allocate archivist thunk: 
        /// when forced, it deduplicates the input list.
        let t = {ws (@@archivist) thk (@@comp) {
            let out = {{force dedup} list1 emp}
            let count = {{force len} {!out}}
            let _x = {{force nat_print} count}
            ret (out, count)
        }}
 
        /// Initial run
        let outs_1 = {force t}

        /// First change: Insert element
        let b1 = {
            {force insert_after}[?] (@62) (@666) 2 {!list1}
        }

        /// Re-force archivist; Precipitates change propagation
        let outs_2 = {force t}

        /// Second change: Remove inserted element
        let b2 = {
            {force remove_after}[?] (@62) {!list1}
        }
        
        /// Re-force archivist; Precipitates change propagation
        let outs_3 = {force t}

        /// All sizes should be the same
        ret (outs_1, outs_2, outs_3)
    }}
}

pub mod static_tests {
    #[test]
    pub fn typing() { fgi_listing_test!{
        use super::*;
        ret 0
    }}
}

//
// Fungi module: hash tries with names, holding natural numbers
//
fgi_mod!{
    // Linked lists, with names; similar definition to list_nat.rs,
    // but index Y treated differently here.
    type List = (
        rec list.
            foralli (X,Y):NmSet.
            ( + Unit + (exists (X1,X2):NmSet|((X1%X2)=X:NmSet).
                        (x Nm[X1] x Nat x Ref[Y](list[X2][Y]))))
    );
    type RefList = (
        foralli (X,Y):NmSet.
            Ref[Y] (List[X][Y])
    );

    /// Compute the length of the list; does not use memoization.
    fn list_len:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 List[X][Y] -> {0;Y} F Nat
    ) = {
        #l. unroll match l {
            _u => {ret 0}
            c => {
                unpack (X1,X2) c = c
                let (x,y,ys) = {ret c}
                let lenys = {{force list_len}[X2][Y] {!ys}}
                lenys + 1
            }
        }
    }

    /// Hash trie of natural numbers, each associated with a (unique) name.
    ///
    /// Note: The hash structure uses the hashes of the natural number
    /// elements, not the hashes of the names.
    ///
    type Trie  = (
        rec trie. 
            foralli (X,Y):NmSet.
            ( + Unit 
                + (x Nm[X] x Nat)
                + (exists (X1,X2):NmSet| ((X1%X2)=X:NmSet).
                   (x (Ref[Y](trie[X1][Y]))
                    x (Ref[Y](trie[X2][Y])))
                )
            )
    );
    type RefTrie = (
        foralli (X,Y):NmSet.
            Ref[Y] (Trie[X][Y])
    );            

    // Names as natural numbers
    nmtm  Zero = ([]);
    idxtm Succ = (#x:Nm.{[] * x});
    idxtm Gte  = (#x:Nm. (Succ)^* {x});
    idxtm Nat  = ({Gte} (nmtm []));

    // Names for trie (path) insertion
    idxtm Ins = (#X:NmSet. X * Nat);
    
    // Write sets for Trie and Dedup:
    idxtm WS_Trie  = (#X:NmSet. {@!} ({Ins} X));
    idxtm Out_Dedup = (#X:NmSet. {@@r} * X);
    idxtm WS_Dedup = (#X:NmSet. 
                      ({WS_Trie} X)   % 
                      ({@@dd}*X)      % 
                      ({Out_Dedup} X) ) ;

    fn nat_hash_bit:(
        Thk[0] 0 Nat -> 0 Nat -> 0 F Bool
    ) = {
        unsafe (2) trapdoor::nat_hash_bit
    }
    
    fn nat_print:(
        Thk[0] 0 Nat -> 0 F Unit
    ) = {
        unsafe (1) trapdoor::nat_print
    }
    
    fn nat_print2:(
        Thk[0] 0 Nat -> 0 Nat -> 0 F Unit
    ) = {
        unsafe (2) trapdoor::nat_print2
    }

    fn print_found_duplicate:(
        Thk[0] 0 Nat -> 0 F Unit
    ) = {
        unsafe (1) trapdoor::print_found_duplicate
    }
    
    /// Like child fn, but returns both children, and the fact that
    /// the names in the pair of children are apart.
    fn children:(
        Thk[0] foralli (X,Y):NmSet. 
            0 RefTrie[X][Y] ->
        {0;Y} F exists (X1,X2):NmSet|((X1%X2)=X:NmSet).
            (x RefTrie[X1][Y] 
             x RefTrie[X2][Y]
            )
    ) = { 
        #t.
        let emp : (RefTrie[0][0]) = {ref 0 roll inj1 ()}        
        let tt = {get t}
        unroll match tt {
            _emp => { ret pack (0,0) (emp, emp) }
            leaf => { ret pack (0,0) (emp, emp) }
            bin  => { ret bin }
        }
    }

    /// True if the given trie is a leaf holding the given nat
    fn is_leaf_with_nat:(
        Thk[0] foralli (X,Y):NmSet. 
            0 RefTrie[X][Y] -> 0 Nat -> {0;Y} F Bool
    ) = {
        #t. #n.
        let tt = {get t}
        unroll match tt {
            _emp => { ret false }
            leaf => { 
                let (_x, y) = {ret leaf}
                let b = {n == y}
                // let _x = {
                //     if (b) {
                //         let _x = {{force print_found_duplicate} y}
                //         ret ()
                //     } else { 
                //         let (a, b) = {ret (n,y)}
                //         Error: HASH COLLISION
                //     }
                // }
                ret b
            }
            bin => { ret false }
        }
    }
            
    fn trie_replrec:(
        Thk[0] foralli (X1,X2,Y):NmSet | ((X1%X2)=X:NmSet).
            foralli Z:Nm.
            0 RefTrie[X1][Y] -> 
            0 Nm[X2] -> 
            0 Nat -> 
            0 Nat -> 
            0 Nm[{Z}] -> 
        {{WS_Trie} X2; Y}
        F (x RefTrie[X1 % X2][Y U ({WS_Trie} X2)]
           x Bool)
    ) = {
        #t. #x. #y. #i. #ni.
        if {i == 12} {
            // base case: create trie leaf node
            let b = {{force is_leaf_with_nat}[X1][Y] t y}
            let r : (RefTrie[X2][{WS_Trie} X2]) = {
                ref {x,ni} roll inj2 inj1 (x, y)
            }
            ret (r, b)
        } else {
            // recursive case
            let j   = {i + 1}
            let nj  = {(name []), ni}
            let tc = {{force children}[X1][Y] t}
            unpack (X1l, X1r) tc = tc
            let (lc,rc) = {ret tc}
            let bit = {{force nat_hash_bit} y i}
            if ( bit ) {
                let (tx, b) = {{force trie_replrec}[X1l][X2][Y][{(@@leaf)*Z}] lc x y j nj}
                let r : (RefTrie[X1 % X2][Y U ({WS_Trie} X2)]) = {
                    ref {x,ni} roll inj2 inj2 pack (X1l % X2, X1r) (tx, rc)
                }
                ret (r, b)
            } else {
                let (tx, b) = {{force trie_replrec}[X1r][X2][Y][{(@@leaf)*Z}] rc x y j nj}
                let r : (RefTrie[X1 % X2][Y U ({WS_Trie} X2)]) = {
                    ref {x,ni} roll inj2 inj2 pack (X1l, X1r % X2) (lc, tx)
                }
                ret (r, b)
            }
        }
    }

    // TODO: Fix alpha conversation for foralli-bound variables (e.g.,
    // change Z1 and Z2 to X1 and X2 below to witness an error).

    fn trie_replace:(
        Thk[0] foralli (Z1,Z2,YZ):NmSet | ((Z1%Z2)=Z:NmSet).
            0 RefTrie[Z1][YZ] -> 
            0 Nm[Z2] -> 
            0 Nat -> 
        {{WS_Trie} Z2; YZ}
        F (x RefTrie[Z1 % Z2][YZ U ({WS_Trie} Z2)] 
           x Bool)
    ) = {
        #t.#x.#y. {force trie_replrec}[Z1][Z2][YZ][{[]}] t x y 0 (name [])
    }

    fn dedup:(
        Thk[0] foralli (X1,X2,Y):NmSet.
            0 RefList[X1][Y] -> 
            0 RefTrie[X2][Y] ->
            {{WS_Dedup} X1; Y}
        F RefList[X1][{Out_Dedup}X1]
    ) = {
        #l. #t. let ln = {get l} unroll match ln {
            _u => { ref 0 roll inj1 () }
            c => {
                unpack (X1a, X1b) c = c
                let (x, y, ys) = {ret c}
                //let _x = {{force nat_print} y}
                let (tx, b) = { ws(nmfn #x:Nm.@@t * x){ {force trie_replace}[X2][X1a][Y] t x y }}
                let (_r,r) = { memo{(@@dd),x}{ {force dedup}[X1b][(X1a%X2)][Y] ys tx} }
                if ( b ) { 
                    ret r 
                } else {
                    ref {(@@r),x} 
                    roll inj2 
                        pack (X1a, X1b)
                        (x, y, r)
                }
            }
        }
    }
}

pub mod trapdoor {
    // This code essentially extends the Fungi evaluator
    //use ast::{Name};
    use crate::dynamics::{RtVal,ExpTerm};
    //use adapton::engine;

    pub fn hash_usize(x:usize) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash,Hasher};
        let mut hasher = DefaultHasher::new();
        x.hash(&mut hasher);
        hasher.finish()
    }

    pub fn nat_hash_bit(args:Vec<RtVal>) -> ExpTerm {
        match (&args[0], &args[1])  {
            (RtVal::Nat(ref n1), RtVal::Nat(ref n2))  => { 
                ExpTerm::Ret(RtVal::Bool( hash_usize(*n1) & (1 << *n2) != 0))
            }
            (v1, v2) => panic!("expected two natural numbers, not: {:?} and {:?}", 
                               v1, v2)
        }
    }
    
    pub fn nat_print(args:Vec<RtVal>) -> ExpTerm {
        match &args[0]  {
            RtVal::Nat(ref n)  => { 
                println!("nat_print: {:?}", n);
                ExpTerm::Ret(RtVal::Unit)
            }
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }
    
    pub fn nat_print2(args:Vec<RtVal>) -> ExpTerm {
        match (&args[0], &args[1])  {
            (RtVal::Nat(ref n1), RtVal::Nat(ref n2))  => { 
                println!("nat_print2: {:?} {:?}", n1, n2);
                ExpTerm::Ret(RtVal::Unit)
            }
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }

    pub fn print_found_duplicate(args:Vec<RtVal>) -> ExpTerm {
        match &args[0]  {
            RtVal::Nat(ref n)  => { 
                println!("Found duplicate: {:?}", n);
                ExpTerm::Ret(RtVal::Unit)
            }
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }
}
