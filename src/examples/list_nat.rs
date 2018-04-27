#[test]
pub fn listing0 () { fgi_listing_test![
    decls {
        /// Lists of natural numbers
        type List  = (+ Unit + (x Nat x List));

        /// Optional natural numbers
        type OpNat  = (+ Unit + Nat );
    }

    let nil:(
        Thk[0] 0 F List
    ) = {            
        ret thunk ret roll inj1 ()
    }
    
    let cons:(
        Thk[0] 0 Nat -> 0 List -> 0 F List
    ) = {            
        ret thunk #h.#t. ret roll inj2 (h, t)
    }

    let rec map:(
        Thk[0] 0 (Thk[0] 0 Nat -> 0 F Nat) -> 0 List -> 0 F List
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                let (h, t) = { ret c }
                let h2 = {{force f} h}
                let t2 = {{force map} f t}
                {{force cons} h2 t2}
            }
        }
    }

    let rec filter:(
        Thk[0] 0 (Thk[0] 0 Nat -> 0 F Bool) -> 0 List -> 0 F List
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                let (h, t) = { ret c }
                let t2 = {{force filter} f t}
                if {{force f} h} {
                    {{force cons} h t2}
                } else {
                    ret t2
                }
            }
        }
    }

    let rec map_filter:(
        Thk[0] 0 (Thk[0] 0 Nat -> 0 F OpNat) -> 0 List -> 0 F List
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                let (h, t) = { ret c }
                let t2 = {{force map_filter} f t}
                let oh2 = {{force f} h}
                match oh2 {
                    _u => { ret t2 }
                    h2 => {{force cons} h t2}
                }
            }
        }
    }

    ret 0
]}
