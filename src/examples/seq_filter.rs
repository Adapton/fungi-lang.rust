#[test]
pub fn listing () { fgi_listing_expect![
    [Expect::Success]
 
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

        /// ## Pointer names -------------------------------------------------------
        
        /// Name pointers written for each name in a structural
        /// recursion (-`_SR`) over a sequence:
        idxtm Seq_SR = ( #x:Nm.({x * @1})%({x * @2}) );
        
        /// ... prefixed with the current write scope (`WS`-)
        idxtm WS_Seq_SR  = ( #x:NmSet.{@!}((Seq_SR) x) );

        /// ... same, but just the first recursive call
        idxtm WS_Seq_SR1 = ( #x:NmSet.{@!}(x * {@1}));

        /// ... second recursive call
        idxtm WS_Seq_SR2 = ( #x:NmSet.{@!}(x * {@2}));

        /// ## Helper functions ---------------------------------------------------
       
        /// Filter an optional natural number, using a natural number predicate
        fn opnat_filter_nat:(
            Thk[0] 0 OpNat ->
                0 (Thk[0] 0 Nat -> 0 F Bool) ->
                0 F OpNat
        ) = {
            #opnat.#pred.
            match opnat {
                _u => {
                    // no number to filter
                    ret inj1 ()
                }
                n => {
                    // apply user-supplied predicate
                    if {{force pred} n} {
                        // keep the number n
                        ret inj2 n
                    } else {
                        // filter out the number n
                        ret inj1 ()
                    }
                }
            }
        }

        /// Empty sequence predicate
        fn is_empty:(
            Thk[0] foralli (X,Y):NmSet.
                0 (Seq[X][Y]) -> { 0; Y } F Bool
        ) = {
            #seq. unroll match seq {
                on => { match on {
                    _u => { ret true }
                    _n => { ret false }
                }}
                _bin => { ret false }
            }
        }
    }
    
    // -----------------------------------------------------------
    
    // Filter a sequence (of optional natural numbers) using a
    // predicate over natural numbers
    let filter:(
        Thk[0] foralli (X,Y):NmSet.
            0 Seq[X][Y] ->
            0 (Thk[0] 0 Nat -> 0 F Bool) ->
        { {WS_Seq_SR} X;
           Y % ( {WS_Seq_SR} X )
        }
        F Seq[X][{WS_Seq_SR} X]
    ) = {
        ret thunk fix filter. #seq. #f. unroll match seq {
            on => {
                let on = {{force opnat_filter_nat} on f}
                ret roll inj1 on
            }
            bin => {
                unpack (X1,X2,X3,Y1,Y2,Y3,Y4) bin = bin
                    let (n,lev,l,r) = {ret bin}
                let (rsl, sl) = { memo{n,(@1)}{ {force filter}[X2][Y2]{!l} f } }
                let (rsr, sr) = { memo{n,(@2)}{ {force filter}[X3][Y4]{!r} f } }
                if {{force is_empty}[X2][({WS_Seq_SR} X2)] sl} {
                    ret sr
                } else {if {{force is_empty}[X3][({WS_Seq_SR} X3)] sr} {
                    ret sl
                } else {
                    ret roll inj2 pack (
                        X1, X2, X3,
                        {WS_Seq_SR1} X1, {WS_Seq_SR} X2,
                        {WS_Seq_SR2} X1, {WS_Seq_SR} X3
                    )(n,lev,rsl,rsr)
                }}
            }
        }
    }
    ret 0
]}
