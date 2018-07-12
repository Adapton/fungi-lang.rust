pub mod dynamic_tests {

    /* 
     * Try the following at the command line:
     * 
     *  $ export FUNGI_VERBOSE_REDUCE=1
     *
     *  $ cargo test examples::trie_nat::dynamic_tests::short -- --nocapture | less -R
     *
     */
    #[test]
    pub fn short() { use examples::list_nat; fgi_dynamic_trace!{
        [Expect::SuccessxXXX]
        use super::*;
        use list_nat::*;
        
        /// Generate input
        let list1  = {{force gen} 20}

        /// Allocate nil ref cell
        let refnil = {ref (@@nil) roll inj1 ()}
        
        /// Allocate emp trie
        let emp = {ref (@@emp) roll inj1 ()}

        /// Allocate archivist thunk: when forced, it builds a trie from the input list
        let t = {ws (@@archivist) thk (@@comp) {
            let list2 = {{force dedup} {!list1} emp}
            ret (list1, list2)
        }}
 
        /// Initial run
        let outs_1 = {force t}

        /// First change: Insert element
        let b1 = {
            {force insert_after}[?] (@19) (@666) 2 {!list1}
        }

        /// Re-force archivist; Precipitates change propagation
        let outs_2 = {force t}

        /// Second change: Remove inserted element
        let b2 = {
            {force remove_after}[?] (@19) {!list1}
        }

        /// Re-force archivist; Precipitates change propagation
        let outs_3 = {force t}
        ret (b1, b2)
    }}
}

//
// Fungi module: hash tries with names, holding natural numbers
//
fgi_mod!{
    /// Hash trie of natural numbers, each associated with a (unique) name.
    ///
    /// Note: The hash structure uses the hashes of the natural number
    /// elements, not the hashes of the names.
    ///
    type Trie  = (
        rec trie. forall (X,Y):NmSet. 
            Ref[Y]( + Unit 
                    + (x Nm[X] x Nat)
                    + (exists (X1,X2):NmSet| ((X1%X2)=X:NmSet).
                       (x trie[X1][Y] x trie[X2][Y])
                    )
            )
    );

    // let emp : Trie[0][{@@trie_emp}] = { 
    //     ref (@@trie_emp) inj1 ()
    // }

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

    /// Get the left or right child of a trie, giving back the empty
    /// trie (reference cell) when no such child exists.
    fn child:(
        Thk[0] forall (X,Y):NmSet. 
            0 Trie[X][Y] -> 0 Bool -> {0;Y} F Trie[X][Y]
    ) = {
        #t. #b.
        let tt = {get t}
        unroll match tt {
            _emp => { ret t }
            leaf => { ret emp }
            bin => {
                unpack (X1,X2) bin = bin
                let (tl,tr) = { ret bin }
                if ( b ) {
                    ret tl
                } else {
                    ret tr
                }
            }
        }
    }
    
    /// Like child fn, but returns both children, and the fact that
    /// the names in the pair of children are apart.
    fn children:(
        Thk[0] forall (X,Y):NmSet. 
            0 Trie[X][Y] ->
        {0;Y} F exists (X1,X2):NmSet|((X1%X2):NmSet). 
            (x Trie[X1][Y] 
             x Trie[X1][Y]
            )
    ) = { 
        let emp = {ref (@@trie_emp) roll inj1 ()}
        #t.
        let tt = {get t}
        unroll match tt {
            _emp => { ret pack (0,0) (emp, emp) }
            leaf => { ret pack (0,0) (emp, emp) }
            bin  => { ret bin }
        }
    }

    /// True if the given trie is a leaf holding the given nat
    fn is_leaf_with_nat:(
        Thk[0] forall (X,Y):NmSet. 
            0 Trie[X][Y] -> 0 Nat -> {0;Y} F Bool
    ) = {
        #t. #n.
        let tt = {get t}
        unroll match tt {
            _emp => { ret false }
            leaf => { 
                let (_x, y) = {ret leaf}
                let b = {n == y}
                let _x = {
                    if (b) {
                        {force nat_print} y
                        ret ()
                    } else { 
                        ret () 
                    }
                }
                ret b
            }
            bin => { IMPOSSIBLE }
        }
    }
            
    fn trie_insrec:(
        Thk[0] forall (X1,X2,Y):NmSet | ((X1%X2)=X:NmSet).
            forall ni:Nm.
            0 Trie[X1][Y] -> 
            0 Nm[X2] -> 
            0 Nat -> 
            0 Nat -> 
            0 Nm[{ni}] -> 
        {?; ?}
        F Trie[X1 % X2][Y U ({Trie} X1)]
    ) = {
        #t. #x. #y. #i. #ni.
        if {i == 8} {
            // Insrec: base case: trie leaf node
            ref {x,ni} roll inj2 inj1 (x, y)
        } else {
            // Insrec: recursive case
            let j  = {i + 1}
            let nj = {(name []),ni}
            let tc = {{force children} t}
            unpack (Xl, Xr) tc = tc
            let (lc,rc) = {ret tc}
            let b  = {{force nat_hash_bit} y i}
            let lx = {                
                if ( b ) {
                    let tx = {{force trie_insrec}[?][?][?] lc x y j nj}
                    ret pack (Xl % X2, Xr) (tx, rc)
                } else {
                    let tx = {{force trie_insrec}[?][?][?] rc x y j nj}
                    ret pack (Xl, Xr % X2) (tx, rc)
                }
            }            
            // Insrec: introduce binary trie constructor
            ref {x,ni} roll inj2 inj2 pack (X1 % X2, ?) lx
        }
    }

    fn trie_insert:(
        Thk[0] forall (X1,X2,Y):NmSet | ((X1%X2)=X:NmSet).
            forall ni:Nm.
            0 Trie[X1][Y] -> 
            0 Nm[X2] -> 
            0 Nat -> 
        {?; ?}
        F Trie[X1 % X2][Y U ({WS_Trie} X1)]
    ) = {
        #t.#x.#y. {force trie_insrec} t x y 0 (name [])
    }

    fn build:(
        Thk[0] forall (X,Y):NmSet.
            0 List[X][Y] -> 
            {?; ?}
        F Trie[X][{Trie} X]
    ) = {
        let emp = {ref (@@trie_emp) roll inj1 ()}
        #l. unroll match l {
            _u => {ret emp}
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (x, y, ys) = {ret c}
                //let (_t,t) = { memo{(@@build),x}{ {force build}[?][?] {!ys} } }
                let (_t,t) = { {force build}[?][?] {!ys} }
                {force trie_insert}[?][?] t x y
            }
        }
    }

    fn trie_replrec:(
        Thk[0] forall (X1,X2,Y):NmSet | ((X1%X2)=X:NmSet).
            forall ni:Nm.
            0 Trie[X1][Y] -> 
            0 Nm[X2] -> 
            0 Nat -> 
            0 Nat -> 
            0 Nm[{ni}] -> 
        {{WS_Trie} X1; Y}
        F (x Trie[X1 % X2][Y U ({WS_Trie} X1)]
           x Bool)
    ) = {
        #t. #x. #y. #i. #ni.
        if {i == 8} {
            // base case: create trie leaf node
            let b = {{force is_leaf_with_nat} t y}
            let r = {ref {x,ni} roll inj2 inj1 (x, y)}
            ret (r, b)
        } else {
            // recursive case
            let j   = {i + 1}
            let nj  = {(name []),ni}
            let tc = {{force children} t}
            unpack (Xl, Xr) tc = tc
            let (lc,rc) = {ret tc}
            let bit = {{force nat_hash_bit} y i}
            let (lr, b) = {
                if ( bit ) {
                    let (tx, b) = {{force trie_replrec}[?][?][?] lc x y j nj}
                    ret (pack (Xl % X2, Xr) (tx, rc), b)
                } else {
                    let (tx, b) = {{force trie_replrec}[?][?][?] rc x y j nj}
                    ret (pack (Xl, Xr % X2) (tx, rc), b)
                }
            }
            let r = { ref {x,ni} roll inj2 inj2 lr }
            ret (r, b)
        }
    }

    fn trie_replace:(
        Thk[0] forall (X1,X2,Y):NmSet | ((X1%X2)=X:NmSet).
            forall ni:Nm.
            0 Trie[X1][Y] -> 
            0 Nm[X2] -> 
            0 Nat -> 
        {{WS_Trie} X; Y}
        F (x Trie[X1 % X2][Y U ({WS_Trie} X1)] 
           x Bool)
    ) = {
        #t.#x.#y. {force trie_replrec} t x y 0 (name [])
    }

    fn dedup:(
        Thk[0] forall (X1,X2,Y):NmSet.
            0 List[X1][Y] -> 
            0 Trie[X2][Y] ->
            {{WS_Dedup} X; Y}
        F List[X1][{@!}X1] [{@!}X1]
    ) = {
        #l. #t. unroll match l {
            _u => { ret l }
            c => {
                unpack (X1a,X1b,Y1,Y2) c = c
                let (x, y, ys) = {ret c}
                //let _x = {{force nat_print} y}
                let _x = {{force nat_print} y}
                let (tx, b) = { ws(@@t){ {force trie_replace}[X1a][Y] t x y }}
                let (_r,r) = { memo{(@@dd),x}{ {force dedup}[X1b][Y2] {!ys} tx} }
                if ( b ) { 
                    ret r 
                } else {
                    ref {(@@r),x} roll inj2 pack (X1a,X1b,?,?) (x, y, r)
                }
            }
        }
    }
}

pub mod trapdoor {
    // This code essentially extends the Fungi evaluator
    //use ast::{Name};
    use dynamics::{RtVal,ExpTerm};
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
}
