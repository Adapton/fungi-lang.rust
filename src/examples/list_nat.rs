//
// Fungi module: linked lists with names, holding natural numbers
//
fgi_mod!{
    /// Lists of natural numbers
    type List  = (
        rec list. foralli (X,Y):NmSet.
            (+ Unit +
             (exists (X1,X2):NmSet | ((X1%X2)=X:NmSet).
              exists (Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
              x Nm[X1] x Nat x Ref[Y1](list[X2][Y2])
             )
            )
    );

    /// Imperatively update a reference cell's content
    // XXX: Technically, this operation is only permitted by the editor (?)
    fn ref_update:(
        Thk[0] foralli X:NmSet. forall A.
            0 Ref[X]A ->
            0 A ->
        {X; 0} // <-- TODO: An editor-level operation only; we don't
        // have effect notation for this yet, but should.
        F Unit
    ) = {
        unsafe (2) trapdoor::ref_update
    }

    /// Test if two names are equal
    fn name_eq:(
        Thk[0] 
            foralli (X,Y):NmSet.
            0 Nm[X] -> 0 Nm[Y] -> 0 F Bool
    ) = {
        unsafe (2) trapdoor::name_eq
    }
        
    /// Allocate a Ref cell, holding a Cons cell, pointing at a list:
    ///
    /// ref         cons       ref     list
    /// |{@!}X1|--->|X1|_|*|-->|Y1|--> |...[X2][Y2]...|
    ///
    /// : Ref[{@!}X1](List[X1%X2][Y1%Y2])
    ///
    fn ref_cons:(
        Thk[0]
            foralli (X,X1,X2):NmSet | ((X1%X2)=X:NmSet).
            foralli (Y,Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
            0 Nm[X1] ->
            0 Nat ->
            0 Ref[Y1](List[X2][Y2]) ->
        {{@!}X1;0} F Ref[{@!}X1](List[X1%X2][Y1%Y2])
    ) = {            
        #n.#h.#t. ref n
        roll inj2 pack (X1,X2,Y1,Y2) (n, h, t)
    }
    
    /// Create a cons cell with a new ref cell tail, holding the given list.
    fn cons_ref:(
        Thk[0]
            foralli (X,X1,X2):NmSet | ((X1%X2)=X:NmSet).
            foralli (Y2):NmSet.
            0 Nm[X1] ->
            0 Nat ->
            0 List[X2][Y2] ->
        {{@!}X1;0} F (List[X1%X2][({@!}X1)%Y2])
    ) = {            
        #n.#h.#t.
        let rt = {ref n t}
        ret roll inj2 pack (X1,X2,({@!}X1),Y2) (n, h, rt)
    }
    
    /// Insert a Cons cell into a list, at the given Ref cell.
    //
    // XXX: Technically, this operation is only permitted by the editor:
    fn insert:(
        Thk[0]
            foralli (X1,X2,Y1,Y2):NmSet.
            0 Nm[X1] ->
            0 Nat ->
            0 Ref[Y1](List[X1%X2][Y2]) ->
        {Y1; Y1} // <-- XXX/TODO: An editor-level operation only
        F Unit
    ) = {
        #n.#h.#r.
        let l1 = {get r}
        let l2 = {{force cons_ref} [?][?][?][?] n h l1}
        {force ref_update} r l2
    }

    /// Remove the Cons cell within a Ref cell.  Return true if this
    /// Cons cell was removed, and false otherwise, if the Ref cell
    /// holds an empty list.
    //
    // XXX: Technically, this operation is only permitted by the editor:
    fn remove:(
        Thk[0]
            foralli (X1,X2,Y1,Y2):NmSet.
            0 Ref[Y1](List[X1%X2][Y2]) ->
        {Y1; Y1} // <-- XXX/TODO: An editor-level operation only
        F Bool
    ) = {
        #r.
        let l1 = {get r}
        unroll match l1 {
            _u => { ret false }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let l2 = {get t}
                let _u = {{force ref_update} r l2}
                ret true
            }
        }
    }

    /// Insert a Cons cell after a given name in a given list.
    /// Return true if successful, and false otherwise.
    fn insert_after:(
        Thk[0]
            foralli (X):NmSet.
            0 Nm[X1] ->
            0 Nm[X2] ->
            0 Nat ->
            0 List[X2%X3][Y] ->
        {Y;Y} // <-- XXX/TODO: An editor-level operation only
        F Bool
    ) = {
        #n1.#n2.#h.#l.
        unroll match l {
            _u => { ret false }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                if {{force name_eq} n n1 } {
                    let _u = {{force insert}[?][?][?][?] n2 h t}
                    ret true
                } else {
                    {force insert_after}[?] n1 n2 h {!t}
                }
            }
        }
    }

    /// Remove the Cons cell after a given name in a given list.
    /// Return true if successful, and false otherwise.
    fn remove_after:(
        Thk[0]
            foralli (X):NmSet.
            0 Nm[X1] ->
            0 List[X2%X3][Y] ->
        {Y;Y} // <-- XXX/TODO: An editor-level operation only
        F Bool
    ) = {
        #n1.#l.
        unroll match l {
            _u => { ret false }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                if {{force name_eq} n n1 } {
                    {force remove}[?][?][?][?] t
                } else {
                    {force remove_after}[?] n1 {!t}
                }
            }
        }
    }

    /// Return true if the given natural number is zero, false otherwise.
    fn nat_is_zero:(Thk[0] 0 Nat -> 0 F Bool)
        = { unsafe (1) trapdoor::nat_is_zero }

    /// Return true if the given natural number is odd, false otherwise.
    fn nat_is_odd:(Thk[0] 0 Nat -> 0 F Bool)
        = { unsafe (1) trapdoor::nat_is_odd }

    /// Return the difference of two natural numbers, as a natural number.
    fn nat_sub:(Thk[0] 0 Nat -> 0 Nat -> 0 F Nat)
        = { unsafe (2) trapdoor::nat_sub }

    /// Convert a natural number into a name
    //
    // XXX -- This type is wrong.  TODO -- figure out how to
    // ecode this type correctly, with existentials.
    fn name_of_nat:(
        Thk[0] 
            foralli X:NmSet.
            0 Nat -> 0 F Nm[X]
    ) = {
        unsafe (1) trapdoor::name_of_nat
    }

    /// Generate a list of naturals [n - 1, n - 2, ..., 0]
    //
    // XXX -- This type is wrong.  TODO -- figure out how to
    // ecode this type correctly, with existentials.  
    fn gen:(
        Thk[0]
            foralli (Y1,X1,Y2):NmSet.
            0 Nat -> 0 F Ref[Y1](List[X1][Y2])
    ) = {
        #n. if {{force nat_is_zero} n} {
            ref (@0) roll inj1 ()
        } else {
            let nm = {{force name_of_nat} n}
            let p  = {{force nat_sub} n 1}
            let l  = {{force gen} p}
            {{force ref_cons}
             [X1][X1][X1][(Y1%Y2)][Y1][Y2]
             nm p l}
        }
    }

    /// Map a list of natural numbers, using a given function from
    /// naturals to naturals.
    fn map:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 (Thk[0] 0 Nat -> 0 F Nat) ->
            0 List[X][Y] ->
        {{@!}X; Y%({@!}X)} F List[X][{@!}X]
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let h2 = {{force f} h}
                let (rt2,_t2) = {
                    memo(n){{force map} [X2][Y2] f {!t}}
                }
                ret roll inj2
                    pack (X1,X2,{@!}X1,{@!}X2) (n, h2, rt2)
            }
        }
    }

    /// Reverse a list of natural numbers, using the given accumulator
    /// value (a Ref cell holding a reversed list prefix).
    fn reverse:(
        Thk[0]
            foralli (X,Xa,Xb,Xc):NmSet | ((Xa%Xb%Xc)=X:NmSet).
            foralli (Y,Ya,Yb1,Yb2):NmSet | ((Ya%Yb1%Yb2)=Y:NmSet).
            0 List[Xa][Ya] ->
            0 Ref[Yb1](List[Xb][Yb2]) ->
            0 Nm[Xc] ->
        //
        // TODO: Fix parse error here:
        //        { {@!}(Xa % (Xa*({@1}))) ;
        //               {@!}(Xa*({@1})) % Y }
            0
            F Ref[{@!}Xc] List[Xa%Xb][Y]
    ) = {
        #l.#r.#rn. unroll match l {
            _u => { let r = {get r}
                    ref rn r }
            c => {
                unpack (Xa1,Xa2,Ya1,Ya2) c = c
                let (n, h, t) = { ret c }
                let r2 = { {force ref_cons}
                            [(Xa%Xb)][Xa][Xb][(Yb1%Yb2)][Yb1][Yb2]
                            n h t}
                let (_r,r) = {memo{n,(@1)}{{force reverse} {!t} r2 rn}}
                ret r
            }
        }
    }

    /// Filter a list of naturals by a given predicate
    fn filter:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 (Thk[0] 0 Nat -> 0 F Bool) ->
            0 List[X][Y] ->
        {{@!}X; Y%({@!}X)} F List[X][{@!}X]
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let (rt2, t2) = {
                    memo(n){{force filter} [X2][Y2] f {!t}}
                }
                if {{force f} h} {
                    ret roll inj2
                        pack (X1,X2,{@!}X1,{@!}X2) (n, h, rt2)
                }
                else {
                    ret t2
                }
            }
        }
    }

    /// Optional natural numbers
    type OpNat  = (+ Unit + Nat );

    /// If the given number is even, return its successor
    fn nat_succ_even:(
        Thk[0]
            0 Thk[0] 0 Nat -> 0 F OpNat
    ) = {
        #n. if {{force nat_is_odd} n} {
            let m = {n + 1}
            ret inj2 m
        } else {
            ret inj1 ()
        }
    }

    /// Map a list of naturals by a given partial mapping function   
    fn map_filter:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 (Thk[0] 0 Nat -> 0 F OpNat) ->
            0 List[X][Y] ->
        {{@!}X; Y%({@!}X)} F List[X][{@!}X]
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let (rt2, t2) = {
                    memo(n){{force map_filter} [X2][Y2] f {!t}}
                }
                let oh2 = {{force f} h}
                match oh2 {
                    _u => { ret t2 }
                    h2 => {
                        ret roll inj2
                            pack (X1,X2,{@!}X1,{@!}X2) (n, h, rt2)
                    }
                }
            }
        }
    }
}


pub mod dynamic_tests {

    #[test]
    pub fn short() { fgi_dynamic_trace!{ [Expect::SuccessxXXX]
        use super::*;
        
        let list1  = {{force gen} 10}
        let refnil = {ref (@@nil) roll inj1 ()}
        let t = {ws (@@archivst) thk (@@comp) {
            let list2 = {{force reverse} {!list1} refnil (@@revres)}
            ret (list1, list2)
        }}
        let outs_1 = {force t}
        let b1 = {
            {force insert_after}[?] (@5) (@666) 666 {!list1}
        }
        let outs_2 = {force t}
        let b2 = {
            {force remove_after}[?] (@5) {!list1}
        }
        let outs_3 = {force t}
        ret (b1, b2)
    }}
    
    #[test]    
    pub fn long() { fgi_dynamic_trace!{ [Expect::SuccessxXXX]
        use super::*;
        
        let list1  = {{force gen} 10}
        let refnil = {ref (@@nil) roll inj1 ()}
        let t = { thk (@@archivist) {
            let list2 = {ws (@@map1)   {memo (@@map1)   {{force map} (thunk #x. x + 1) {!list1}}}}
            let list3 = {ws (@@map2)   {memo (@@map2)   {{force map} (thunk #x. x + 2) {!list1}}}}
            let list4 = {ws (@@rev)    {memo (@@rev)    {{{force reverse} {!list1} refnil (@@revres)}}}}
            let list5 = {ws (@@filter) {memo (@@filter) {{force filter} nat_is_odd {!list1}}}}
            let list6 = {ws (@@mapftr) {memo (@@mapftr) {{force map_filter} nat_succ_even {!list1}}}}
            ret (list1, list2, list3, list4, list5, list6)
        }}
        let outs_1 = {force t}
        let b1 = {
            {force insert_after}[?] (@5) (@666) 666 {!list1}
        }
        let outs_2 = {force t}
        let b2 = {
            {force remove_after}[?] (@5) {!list1}
        }
        let outs_3 = {force t}
        ret (b1, b2)
    }}
}

///////////////////////////////////////////////////////////////////////////
//
// TODO (Hammer): 
//
// Once we have a fuller story for the module system, move these
// primmitives into an appropriate module for them.
//
pub mod trapdoor {
    // This code essentially extends the Fungi evaluator
    use ast::{Name};
    use dynamics::{RtVal,ExpTerm};
    use adapton::engine;

    pub fn ref_update(args:Vec<RtVal>) -> ExpTerm {
        match (&args[0], &args[1]) {
            (RtVal::Ref(r), v) => {
                //println!("ref_update: {:?} <-- {:?}", r, v);
                engine::set(r, v.clone());
                ExpTerm::Ret(RtVal::Unit)
            },
            (r, v) => panic!("expected a reference cell and value, not: {:?} and {:?}", r, v)
        }
    }
    
    pub fn name_of_nat(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => { 
                ExpTerm::Ret(RtVal::Name(Name::Num(*n)))
            }
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }

    pub fn name_eq(args:Vec<RtVal>) -> ExpTerm {
        match (&args[0],&args[1]) {
            (RtVal::Name(n1), RtVal::Name(n2)) => {
                ExpTerm::Ret(RtVal::Bool(n1 == n2))
            }
            (v1, v2) => panic!("expected two names, not: {:?} and {:?}", v1, v2)
        }
    }
    
    pub fn nat_is_zero(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => { 
                ExpTerm::Ret(RtVal::Bool(n == &0)) 
            },
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }
    
    pub fn nat_is_odd(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => { 
                ExpTerm::Ret(RtVal::Bool(n.checked_rem(2) == Some(1)))
            },
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }
    
    pub fn nat_is_even(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => { 
                ExpTerm::Ret(RtVal::Bool(n.checked_rem(2) == None))
            },
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }
    
    pub fn nat_sub(args:Vec<RtVal>) -> ExpTerm {
        match (&args[0], &args[1]) {
            (RtVal::Nat(n), RtVal::Nat(m)) => {
                assert!(n >= m);
                //println!("{:?} - {:?} = {:?}", n, m, n - m);
                ExpTerm::Ret(RtVal::Nat(n - m))
            },
            (v1, v2) => 
                panic!("expected two natural numbers, not: {:?} and {:?}", v1, v2)
                
        }
    }
}


///////////////////////////////////////////////////////////////////////////////////////////////////////
#[test]
pub fn listing1 () { fgi_listing_expect![
    [Expect::FailurexXXX]
        
        decls {
            /// Lists of natural numbers
            type List  = (
                rec list. foralli (X,Y):NmSet.
                    (+ Unit +
                     (exists (X1,X2):NmSet | ((X1%X2)=X:NmSet).
                      exists (Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
                      x Nm[X1] x Nat x Ref[Y1](list[X2][Y2])
                     ))
            );
        }
    
    let cons:(
        Thk[0]
            foralli (X1,X2):NmSet. // <-- forgot to insist that X1%X2
            foralli (Y1,Y2):NmSet. // <-- forgot to insist that Y1%Y2
            0 Nm[X1] ->
            0 Nat ->
            0 Ref[Y1](List[X2][Y2]) ->
            0 F List[X1%X2][Y1%Y2]
    ) = {            
        ret thunk #n.#h.#t. ret roll inj2
            pack (X1,X2,Y1,Y2) (n, h, t)
    }
    
    ret 0
]}

///////////////////////////////////////////////////////////////////////////////////////////////////////
// OLD STUFF -- The following is stale, as of Friday, 2018.05.18
///////////////////////////////////////////////////////////////////////////////////////////////////////
/*

#[test]
pub fn listing0 () { fgi_listing_expect![
    [Expect::SuccessxXXX]
    
    decls {
        /// Lists of natural numbers
        type List  = (
            rec list. foralli (X,Y):NmSet.
            (+ Unit +
             (exists (X1,X2):NmSet | ((X1%X2)=X:NmSet).
              exists (Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
              x Nm[X1] x Nat x Ref[Y1](list[X2][Y2])
             ))
        );

        /// Optional natural numbers
        type OpNat  = (+ Unit + Nat );
    }

    // let nil:(
    //     Thk[0] foralli (X,Y):NmSet. 0 Unit -> 0 F List[X][Y]
    // ) = {            
    //     ret thunk #_u. ret roll inj1 ()
    // }
    
    let cons:(
        Thk[0]
            foralli (X,X1,X2):NmSet | ((X1%X2)=X:NmSet).
            foralli (Y,Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
            0 Nm[X1] ->
            0 Nat ->
            0 Ref[Y1](List[X2][Y2]) ->
            0 F List[X1%X2][Y1%Y2]
    ) = {            
        ret thunk #n.#h.#t. ret roll inj2
            pack (X1,X2,Y1,Y2) (n, h, t)
    }

    //
    // Allocates a ref cell, holding a cons cell, pointing at a list:
    //
    // ref         cons       ref     list
    // |{@!}X1|--->|X1|_|*|-->|Y1|--> |...[X2][Y2]...|
    //
    // : Ref[{@!}X1](List[X1%X2][Y1%Y2])
    //
    let ref_cons:(
        Thk[0]
            foralli (X,X1,X2):NmSet | ((X1%X2)=X:NmSet).
            foralli (Y,Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
            0 Nm[X1] ->
            0 Nat ->
            0 Ref[Y1](List[X2][Y2]) ->
            {{@!}X;0} F Ref[{@!}X1](List[X1%X2][Y1%Y2])
    ) = {            
        ret thunk #n.#h.#t. ref n
            roll inj2 pack (X1,X2,Y1,Y2) (n, h, t)
    }
   
    let rec map:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 (Thk[0] 0 Nat -> 0 F Nat) ->
            0 List[X][Y] ->
        {{@!}X; Y%({@!}X)} F List[X][{@!}X]
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let h2 = {{force f} h}
                let (rt2,_t2) = {
                    memo(n){{force map} [X2][Y2] f {!t}}
                }
                ret roll inj2
                    pack (X1,X2,{@!}X1,{@!}X2) (n, h2, rt2)
            }
        }
    }

    let rec filter:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 (Thk[0] 0 Nat -> 0 F Bool) ->
            0 List[X][Y] ->
        {{@!}X; Y%({@!}X)} F List[X][{@!}X]
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let (rt2, t2) = {
                    memo(n){{force filter} [X2][Y2] f {!t}}
                }
                if {{force f} h} {
                    ret roll inj2
                        pack (X1,X2,{@!}X1,{@!}X2) (n, h, rt2)
                }
                else {
                    ret t2
                }
            }
        }
    }

    let rec map_filter:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 (Thk[0] 0 Nat -> 0 F OpNat) ->
            0 List[X][Y] ->
        {{@!}X; Y%({@!}X)} F List[X][{@!}X]
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let (rt2, t2) = {
                    memo(n){{force map_filter} [X2][Y2] f {!t}}
                }
                let oh2 = {{force f} h}
                match oh2 {
                    _u => { ret t2 }
                    h2 => {
                        ret roll inj2
                            pack (X1,X2,{@!}X1,{@!}X2) (n, h, rt2)
                    }
                }
            }
        }
    }

    let rec reverse:(
        Thk[0]
            foralli (X,Xa,Xb,Xc):NmSet | ((Xa%Xb%Xc)=X:NmSet).
            foralli (Y,Ya,Yb1,Yb2):NmSet | ((Ya%Yb1%Yb2)=Y:NmSet).
            0 List[Xa][Ya] ->
            0 Ref[Yb1](List[Xb][Yb2]) ->
            0 Nm[Xc] ->
        //
        // TODO: Fix parse error here:
        //        { {@!}(Xa % (Xa*({@1}))) ;
        //               {@!}(Xa*({@1})) % Y }
            0
            F Ref[{@!}Xc] List[Xa%Xb][Y]
    ) = {
        #l.#r.#n. unroll match l {
            _u => { let r = {get r}
                    ref n r }
            c => {
                unpack (Xa1,Xa2,Ya1,Ya2) c = c
                let (n, h, t) = { ret c }
                let r2 = { {force ref_cons}
                            [(Xa%Xb)][Xa][Xb][(Yb1%Yb2)][Yb1][Yb2]
                            n h t}
                let (_r,r) = {memo{n,(@1)}{{force reverse} {!t} r2}}
                ret r
            }
        }
    }

    // let rec fold:(
    //     Thk[0]
    //         0 List ->
    //         0 Nat ->
    //         0 (Thk[0] 0 Nat -> 0 Nat -> 0 F Nat) ->
    //         0 F Nat
    // ) = {
    //     #l.#a.#f. unroll match l {
    //         _u => { ret a }
    //         c => {
    //             let (h, t) = { ret c }
    //             let a2 = {{force f} a h}
    //             {{force fold} t a2 f}
    //         }
    //     }
    // }
        
    ret 0
]}

*/
