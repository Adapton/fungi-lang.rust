fgi_mod!{
    // In this variation, sequences are parameterized by two name
    // sets, X and Y, but not by any types.  We assume the sequences
    // consist of naturals.

    type Lev = ( Nat );
    type Seq = (
        rec Seq. foralli (X,Y):NmSet.
            (+ Nat 
             + (exists (X1,X2,X3)   :NmSet | (X1%X2%X3=X).
                exists (Y1,Y2,Y3,Y4):NmSet | (Y1%Y2%Y3%Y4=Y).
                x Nm[X1] x Lev
                x Ref[Y1](Seq[X2][Y2])
                x Ref[Y3](Seq[X3][Y4]))
            )
    )
        
    // name set function for naming structural recursion over binary
    // trees
    idxtm bin = #x:Nm.{x,@1} % {x,@2};

    fn max:(
        Thk[0] foralli (X,Y):NmSet.
            0 Seq[X][Y] ->
        { bin X; 0 }
        F Nat
    ) = {
        #seq. unroll seq seq. match seq {
            vec => { {force vec_max} vec }
            bin => {
                let (n,_x,l,r) = {ret bin}
                let (_l, ml) = { memo{n,(@1)}{ {force max} {!l} } }
                let (_r, mr) = { memo{n,(@2)}{ {force max} {!r} } }
                if { mr < ml } {ret ml} else {ret mr}
            }
        }
    }

    fn is_empty:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
        { 0; Y }
        F Bool
    ) = {
        #seq. unroll match seq {
            vec => { {force vec_is_empty} vec }
            bin => {
                let (n,lev,l,r) = {ret bin}
                if {{force is_empty} {!l}} {
                    {{force is_empty} {!r}}
                } else {
                    ret false
                }
            }
        }
    }

    fn is_empty_shallow:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
        { 0; 0 }
        F Bool
    ) = {
        #seq. unroll match seq {
            vec => { {force vec_is_empty} vec }
            bin => { ret false }
        }
    }

    fn is_singleton:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
            0 F Bool
    ) = {
        #seq. unroll match seq {
            vec => { {force vec_is_singleton} vec }
            bin => { ret false }
        }
    }
    
    fn monoid:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
            0 (Thk[0] 0 Nat -> 0 Nat -> 0 F Nat) ->
        { bin X; 0 }
        F Nat
    ) = {
        #seq. #binop. unroll match seq {
            vec => { {force vec_monoid} vec }
            bin => {
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
            0 (Thk[0] 0 Nat -> 0 F Nat)
        { bin X; Y }
        F (Seq[X][X])
    ) = {
        #seq. #f. unroll match seq {
            vec => { {force vec_map } f vec }
            bin => {
                let (n,lev,l,r) = {ret bin}
                let (rsl, sl) = { memo{n,(@1)}{ {force map} f {!l} } }
                let (rsr, sr) = { memo{n,(@2)}{ {force map} f {!r} } }
                ret roll inj2 (n,lev,rsl,rsr)
            }
        }
    }
    
    fn filter:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
            0 (Thk[0] 0 Nat -> (0 F Bool)) ->
        { bin X; Y }
        F (Seq[X][X])
    ) = {
        #seq. #f. unroll match seq {
            vec => { {force vec_filter} f vec }
            bin => {
                let (n,lev,l,r) = {ret bin}
                let (rsl, sl) = { memo{n,(@1)}{ {force filter} f {!l} } }
                let (rsr, sr) = { memo{n,(@2)}{ {force filter} f {!r} } }
                if {{force is_empty} sl} { ret sr }
                else { if {{force is_empty} sr} { ret sl }
                       else { ret roll inj2 (n,lev,rsl,rsr) }
                }
            }
        }
    }
    
    fn map_filter:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
            0 (Thk[0] 0 Nat -> 0 F (+ Unit + Nat)) ->
        { bin X; Y }
        F Nat
    ) = {
        #seq. #f. unroll match seq {
            vec => { {force vec_map_filter} f vec }
            bin => {
                let (n,lev,l,r) = {ret bin}
                let (rsl, sl) = { memo{n,(@1)}{ {force map_filter} f {!l} } }
                let (rsr, sr) = { memo{n,(@2)}{ {force map_filter} f {!r} } }
                if {{force is_empty} sl} { ret sr }
                else { if {{force is_empty} sr} { ret sl }
                       else { ret roll inj2 (n,lev,rsl,rsr) }
                }
            }
        }
    }
}
