#[test]
pub fn listing0 () { fgi_listing_test![
    decls {
        //LazyLists, matching Elm type
        type LazyList = Thk[0] 0 F (+ Unit + (x Nat x LazyList))

        //Optional natural numbers
        type OpNat = (+ Unit + Nat)
    }

    let nil:(
        Thk[0] 0 F LazyList
    ) = {
        ret thunk ret thunk ret roll inj1 ()
    }


    ret 0
]}
