#[test]
pub fn listing0 () { fgi_listing_test![
    decls {
        //Nat stream
        type Stream = (+ Unit + (x Nat x Thk Stream));

        //Optional natural numbers
        type OpNat = (+ Unit + Nat);
    }

    let nil:(
        Thk[0] 0 F Stream
    ) = {
        ret thunk ret roll inj1 ()
    }

    let cons:(
        Thk[0] 0 Nat -> 0 Thk Stream -> 0 F Stream
    ) = {
        ret thunk #h.#t. ret roll inj2 (h, t)
    }

    /*let rec map:(
        Thk[0]
            0 (Thk[0] 0 Nat -> 0 F Nat) ->
            0 Stream ->
            0 F Stream
    ) = {
        #f.#s. unroll match s {
            _u => { ret roll inj1 () }
            c => {
                let (h, tt) = { ret c }
                // tt is a Thk Stream, must force to get out Stream
                let ft = {force tt}
                let h2 = {{force f} h}
                let t2 = {{force map} f ft}
                {{force cons} h2 t2}
            }
        }
    }*/

    ret 0
]}
