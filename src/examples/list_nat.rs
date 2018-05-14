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
