fgi_mod!{
    // Optional natural numbers; the "leaves" of the binary tree
    // holding the sequence of natural numbers.
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

    // Level tree holding (optional) natural numbers at the leaves.
    // Each level is a number; along each path, levels are descending.    
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
        
    // Names **structural recursion** over binary trees; this function
    // is used below to define the effects of such functions in more
    // concise, abstract way.
    idxtm seq_sr = ( #x:Nm.{x,@1} % {x,@2} );

    // potentially reads all pointers of sequence, but writes no names.
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

    // Reads all pointers of input using structural recursion,
    // producing an optional natural number (and no output structure);
    // the only named structure here is the recursive computation.
    fn max:(
        Thk[0] foralli (X,Y):NmSet.
            0 Seq[X][Y] ->
        { (seq_sr) X; Y }
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

    // generic version of `max` above, where the operation need not be
    // "natural number maximum".
    fn monoid:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
            0 (Thk[0] 0 OpNat -> 0 OpNat -> 0 F OpNat) ->
        { (seq_sr) X; 0 }
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

    // generic mapping function.  reads all pointers of the input
    // using structural recursion to name and produce the output tree.
    // In terms of the named dependence graph, the output tree and the
    // computation that produce it coincide exactly, and both are
    // named with set `(seq_sr) X`.
    fn map:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
            0 (Thk[0] 0 OpNat -> 0 F OpNat) ->
        { (seq_sr) X; Y }
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

    // generic filtering function.  reads all pointers of the input
    // using structural recursion to name and produce the output tree.
    // In terms of the named dependence graph, the output tree and the
    // computation that produce it coincide, except where the filtered
    // output tree is empty; the set `(seq_sr) X` over approximates
    // the named output structure.
    fn filter:(
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y]) ->
            0 (Thk[0] 0 Nat -> 0 F Bool) ->
        { (seq_sr) X; Y }
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
