fgi_mod!{

    type OpNat = (+ Unit + Nat );

    fn opnat_max:(
        Thk[0] 0 OpNat -> 0 OpNat -> 0 F OpNat
    ) = {
        #xo.#yo.
        match (x_o) {
            _u  => { ret yo }
            x => { match (yo) {
                _u => { ret yo }
                y => {
                    if { x < y } {ret y}
                    else {ret x}
                }
            }}
        }                            
    }

    // - - - - - - - - - - - - - - - - - - - - - - -
    
    type Lev = ( Nat );
    type Seq = (
        rec Seq. foralli (X,Y):NmSet.
            (+ OpNat
             + (exists (X1,X2,X3)   :NmSet | (X1%X2%X3=X).
                exists (Y1,Y2,Y3,Y4):NmSet | (Y1%Y2%Y3%Y4=Y).
                x Nm[X1] x Lev
                x Ref[Y1](Seq[X2][Y2])
                x Ref[Y3](Seq[X3][Y4]))
            )
    );
        
    // name set function for naming structural recursion over binary
    // trees
    idxtm bin = ( #x:Nm.{x,@1} % {x,@2} );

    fn is_empty:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
        { 0; Y }
        F Bool
    ) = {
        #seq. unroll match seq {
            opnat => {
                match opnat {
                    _u => {ret true}
                    _u => {ret false}
                }
            }
            bin => {
                // TODO: unpack
                let (n,lev,l,r) = {ret bin}
                if {{force is_empty} {!l}} {
                    {{force is_empty} {!r}}
                } else {
                    ret false
                }
            }
        }
    }
    
    fn max:(
        Thk[0] foralli (X,Y):NmSet.
            0 Seq[X][Y] ->
        { (bin) X; 0 }
        F OpNat
    ) = {
        #seq. unroll seq seq.
        match seq {
            opelm => {ret opelm}
            bin => {
                // TODO: unpack
                let (n,_x,l,r) = {ret bin}
                let (_l, ml) = { memo{n,(@1)}{ {force max} {!l} } }
                let (_r, mr) = { memo{n,(@2)}{ {force max} {!r} } }
                {{force max_opnat} ml mr}
            }
        }
    }

    fn monoid:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
            0 (Thk[0] 0 OpNat -> 0 OpNat -> 0 F OpNat) ->
        { (bin) X; 0 }
        F OpNat
    ) = {
        #seq. #binop. unroll match seq {
            vec => { {force vec_monoid} vec }
            bin => {
                // TODO: unpack
                let (n,_x,l,r) = {ret bin}
                let (_l, ml) = { memo{n,(@1)}{ {force monoid} {!l} } }
                let (_r, mr) = { memo{n,(@2)}{ {force monoid} {!r} } }
                {{force binop} ml mr}
            }
        }
    }
    
    fn map:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
            0 (Thk[0] 0 OpNat -> 0 F OpNat) ->
        { (bin) X; Y }
        F (Seq[X][X])
    ) = {
        #seq. #f. unroll match seq {
            opnat => {
                let opnat2 = {{force f} opnat}
                ret roll inj1 opnat2
            }
            bin => {
                // TODO: unpack
                let (n,lev,l,r) = {ret bin}
                let (rsl, sl) = { memo{n,(@1)}{ {force map} f {!l} } }
                let (rsr, sr) = { memo{n,(@2)}{ {force map} f {!r} } }
                // TODO: repack
                ret roll inj2 (n,lev,rsl,rsr)
            }
        }
    }
    
    fn filter:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
            0 (Thk[0] 0 Nat -> 0 F Bool) ->
        { (bin) X; Y }
        F (Seq[X][X])
    ) = {
        #seq. #f. unroll match seq {
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
                let (n,lev,l,r) = {ret bin}
                // TODO: unpack
                let (rsl, sl) = { memo{n,(@1)}{ {force filter} f {!l} } }
                let (rsr, sr) = { memo{n,(@2)}{ {force filter} f {!r} } }
                if {{force is_empty} sl} { ret sr }
                else { if {{force is_empty} sr} { ret sl }
                       else {
                           // TODO: repack
                           ret roll inj2 (n,lev,rsl,rsr)
                       }
                }
            }
        }
    }    
}
