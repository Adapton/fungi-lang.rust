#[test]
pub fn listing0 () { fgi_listing_test![
    decls {
        //Nat stream
        type Stream = (+ Unit + (x Nat x (Thk[0] 0 Unit -> 0 F Stream)));
        //type Stream = ( rec stream. (+ Unit + (x Nat x Thk stream)) );

        //Optional natural numbers
        type OpNat = (+ Unit + Nat);
    }

    let nil:(
        Thk[0] 0 F Stream
    ) = {
        ret thunk ret roll inj1 ()
    }

    let cons:(
        Thk[0] 0 Nat -> 0 Stream -> 0 F Stream
    ) = {
        ret thunk #h.#t. ret roll inj2 (h, thunk #u. ret t)
    }

    let rec map:(
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
                let ft = {{force tt} ()}
                let h2 = {{force f} h}
                let t2 : Stream = {{force map} f ft}
                {{force cons} h2 t2}
            }
        }
    }

    let rec filter:(
        Thk[0]
            0 (Thk[0] 0 Nat -> 0 F Bool) ->
            0 Stream ->
            0 F Stream
    ) = {
        #f.#s. unroll match s {
            _u => { ret roll inj1 () }
            c => {
                let (h, tt) = { ret c }
                let ft = {{force tt} ()}
                let t2 = {{force filter} f ft}
                if {{force f} h} {
                    {{force cons} h t2}
                } else {
                    ret t2
                }
            }
        }
    }

    let rec map_filter:(
        Thk[0]
            0 (Thk[0] 0 Nat -> 0 F OpNat) ->
            0 Stream ->
            0 F Stream
    ) = {
        #f.#s. unroll match s {
            _u => { ret roll inj1 () }
            c => {
                let (h, tt) = { ret c }
                let ft = {{force tt} ()}
                let t2 = {{force map_filter} f ft}
                let oh2 = {{force f} h}
                match oh2 {
                    _u => { ret t2 }
                    h2 => {{force cons} h2 t2}
                }
            }
        }
    }

    let rec reverse:(
        Thk[0]
            0 Stream ->
            0 Stream ->
            0 F Stream
    ) = {
        #s.#r. unroll match s {
            _u => { ret r }
            c => {
                let (h, tt) = { ret c }
                let r2 = {{force cons} h r}
                let ft = {{force tt} ()}
                {{force reverse} ft r2}
            }
        }
    }

    let rec fold:(
        Thk[0]
            0 Stream ->
            0 Nat ->
            0 (Thk[0] 0 Nat -> 0 Nat -> 0 F Nat) ->
            0 F Nat
    ) = {
        #s.#a.#f. unroll match s {
            _u => { ret a }
            c => {
                let (h, tt) = { ret c }
                let a2 = {{force f} a h}
                let ft = {{force tt} ()}
                {{force fold} ft a2 f}
            }
        }
    }

    ret 0
]}

pub mod dynamic_tests {

    #[test]
    fn listing1() {
        use reduce;
        use dynamics;
        use std::rc::Rc;
        use ast::*;


    }
}
