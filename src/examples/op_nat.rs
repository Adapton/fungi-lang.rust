//
// Fungi module: Optional natural numbers
//
fgi_mod!{
    use crate::examples::nat::*;

    /// Optional natural numbers
    type OpNat  = (+ Unit + Nat );
    
    /// Optional pairs of natural numbers
    type Op2Nat = (+ Unit + (x Nat x Nat));

    // Split an optional pair of natural into a pair of optional naturals
    fn opnat_split:(
        Thk[0] 0 Op2Nat -> 0 F (x OpNat x OpNat)
    ) = {
        #xyo. match (xyo) {
            _u => {
                ret (inj1 (), inj1 ())
            }
            xy => {
                let (x,y) = { ret xy }
                ret (inj2 x, inj2 y)
            }}
    }

    // Pair two optional naturals into an optional pair of naturals
    fn opnat_pair:(
        Thk[0] 0 (x OpNat x OpNat) -> 0 F (Op2Nat)
    ) = {
        #xoyo. let (xo,yo) = { ret xoyo }
        match (xo) {
            _u => { ret inj1 () }
            x  => { match (yo) {
                _u => { ret inj1 () }
                y  => { ret inj2 (x,y) }
            }}
        }
    }

    // Filter an optional natural number, using a natural number predicate
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


    // Compute the maximum optional natural number (among a pair)
    fn opnat_max:(
        Thk[0] 0 OpNat -> 0 OpNat -> 0 F OpNat
    ) = {
        #xo.#yo.
        match (xo) {
            _u  => { ret yo }
            x => { match (yo) {
                _u => { ret yo }
                y => {
                    if { x < y } {ret yo}
                    else {ret xo}
                }
            }}
        }
    }

    /// If the given number is even, return its successor
    fn nat_succ_even:(
        Thk[0]
            0 Nat -> 0 F OpNat
    ) = {
        #n. if {{force nat_is_odd} n} {
            let m = {n + 1}
            ret inj2 m
        } else {
            ret inj1 ()
        }
    }
}

pub mod static_tests {
    #[test]
    pub fn typing() { fgi_listing_test!{
        use super::*;
        ret 0
    }}
}
