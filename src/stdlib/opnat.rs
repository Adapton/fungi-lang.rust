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

    
}
