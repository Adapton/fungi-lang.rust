/*#[test]
pub fn listing0 () { fgi_listing_expect![
    [Expect::SuccessxXXX]

    decls {
        /// Lists of natural numbers
        type List  = (+ Unit + (x Nat x List));

        type LazyList = (+ Thk Unit + (Thk (x Nat x LazyList)));

        type Queue = (x LazyList x List x LazyList);
    }

    let empty:(
        Thk[0] 0 F Queue
    ) = {
        ret thunk ret (ret roll inj1 ret thunk (), ret roll inj1 (), ret roll inj1 ret thunk ())
    }

]}
*/
