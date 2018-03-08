fgi_mod!{
    // Optional natural numbers
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
   
    let opnat_split:(
        Thk[0] 0 Op2Nat -> 0 F (x OpNat x OpNat)
    ) = {            
        ret thunk #xyo. match (xyo) {
            _u => {
                ret (inj1 (), inj1 ())
            }
            xy => {
                let (x,y) = { ret xy }
                ret (inj2 x, inj2 y)
            }}
    }
    
    let opnat_pair:(
        Thk[0] 0 (x OpNat x OpNat) -> 0 F (Op2Nat)
    ) = {
        ret thunk #xoyo. let (xo,yo) = { ret xoyo }
        match (xo) {
            _u => { ret inj1 () }
            x  => { match (yo) {
                _u => { ret inj1 () }
                y  => { ret inj2 (x,y) }
            }}
        }
    }    
}
