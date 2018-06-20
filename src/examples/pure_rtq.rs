#[test]
pub fn listing0 () { fgi_listing_test![
    decls {
        /// Lists of natural numbers
        type List  = (+ Unit + (x Nat x List));

        type LazyList = (Thk[0] 0 F (+ Unit + (x Nat x LazyList)));

        type Queue = (x LazyList x List x LazyList);
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

    let is_empty:(
        Thk[0]
            0 Queue ->
            0 F Bool
    ) = {
        #q. match q {
            c => {
                let (front, back, sched) = { ret c } //TODO: correct match syntax?
                ret true
            }
        }
    }

    ret 0
]}
