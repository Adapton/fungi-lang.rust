#[test]
pub fn listing0 () { fgi_listing_test![
    decls {
        /// Lists of natural numbers
        type List  = (+ Unit + (x Nat x List));

        type LazyList = (Thk[0] 0 F (+ Unit + (x Nat x LazyList)));
        //uses explicit LazyList type b/c of force bug docced earlier
        type Queue = (x (Thk[0] 0 F (+ Unit + (x Nat x LazyList))) x List x LazyList);

        type OpNat = (+ Unit + Nat );

        type OpQueue = (+ Unit + Queue );
    }

    let cons_ll:(
        Thk[0]
            0 Nat ->
            0 LazyList ->
            0 F LazyList
    ) = {
        ret thunk #h.#l. ret thunk ret roll inj2 (h, l)
    }

    let cons:(
        Thk[0] 0 Nat -> 0 List -> 0 F List
    ) = {
        ret thunk #h.#t. ret roll inj2 (h, t)
    }

    let lazynil:(
        Thk[0] 0 F LazyList
    ) = {
        ret thunk ret thunk ret roll inj1 ()
    }

    let nil:(
        Thk[0] 0 F List
    ) = {
        ret thunk ret roll inj1 ()
    }

    let empty:(
        Thk[0] 0 F Queue
    ) = {
        //ret thunk ret (ret roll inj1 ret thunk (), ret roll inj1 (), ret roll inj1 ret thunk ())
        //ret thunk ret (ret thunk ret roll inj1 (), ret roll inj1 (), ret thunk ret roll inj1 ())
        let ll = {force lazynil}
        let l = {force nil}
        ret thunk ret (ll, l, ll) //TODO: what's up with this?
    }

    let is_empty_lazylist:(
        Thk[0]
            0 (Thk[0] 0 F (+ Unit + (x Nat x LazyList))) ->
            0 F Bool
    ) = {
        ret thunk #ll.
        let fl = {force ll}
        unroll match fl {
            _u => { ret true }
            c => { ret false }
        }
    }

    let is_empty:(
        Thk[0]
            0 Queue ->
            0 F Bool
    ) = {
        ret thunk #q.
        let (front, back, sched) = q
        {{force is_empty_lazylist} front}
    }

    let peek:(
        Thk[0]
            0 Queue ->
            0 F OpNat
    ) = {
        ret thunk #q.
        let (front, back, sched) = q
        let ffront = {force front}
        unroll match ffront {
            _u => {ret inj1 ()}
            c => {
                let (h, tl) = { ret c }
                ret inj2 h
            }
        }
    }

    let rec rotate:(
        Thk[0]
            0 (Thk[0] 0 F (+ Unit + (x Nat x LazyList))) ->
            0 List ->
            0 LazyList ->
            0 F LazyList
    ) = {
        #f.#b.#s.
        unroll match b {
            _u => { {force lazynil} } //ERROR CASE: SHOULD NOT HAPPEN
            c => {
                let (y, ys) = { ret c }
                let scons = {{force cons_ll} y s}
                let ff = { force f }
                unroll match ff {
                    _u => { ret scons } //base case
                    d => {
                        let (x, xs) = { ret d }
                        ret scons
                        //TODO: this is stack overflowing
                        /*let rtl = {{force rotate} xs ys scons}
                        {{force cons_ll} x rtl}*/
                    }
                }
            }
        }
    }

    let exec:(
        Thk[0]
            //f needs to be explicit b/c rotate's first arg is?
            0 (Thk[0] 0 F (+ Unit + (x Nat x LazyList))) ->
            0 List ->
            0 (Thk[0] 0 F (+ Unit + (x Nat x LazyList))) ->
            0 F Queue
    ) = {
        ret thunk #f.#b.#s.
        let fs = { force s }
        unroll match fs {
            _u => {
                let ln = {force lazynil}
                let fr = {{force rotate} f b ln}
                let n = {force nil}
                ret (fr, n, fr)
            }
            c => {
                let (w, ss) = { ret c }
                ret (f, b, ss)
            }
        }
    }

    let enqueue:(
        Thk[0]
            0 Nat ->
            0 Queue ->
            0 F Queue
    ) = {
        ret thunk #n.#q.
        let (front, back, sched) = q
        let aback = {{force cons} n back}
        {{force exec} front aback sched}
    }

    //TODO: why does OpQueue version not work?
    let dequeue:(
        Thk[0]
            0 Queue ->
            0 F Queue
    ) = {
        ret thunk #q.
        let (front, back, sched) = q
        let ff = {force front}
        unroll match ff {
            _u => { {force empty} }
            c => {
                let (h, tl) = { ret c }
                {{force exec} tl back sched}
            }
        }
    }

    ret 0
]}
