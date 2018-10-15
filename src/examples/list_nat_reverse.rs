fgi_mod!{
    open crate::examples::list_nat;
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
                let r2 = { ws(@@r) {force ref_cons}
                            [(Xa%Xb)][Xa][Xb][(Yb1%Yb2)][Yb1][Yb2]
                            n h t}
                let (_r,r) = {memo{(@@rev),n}{ {force reverse} 
                                                [?][?][?][?]
                                                [?][?][?][?] {!t} r2 rn}
                }
                ret r
            }
        }
    }
}
