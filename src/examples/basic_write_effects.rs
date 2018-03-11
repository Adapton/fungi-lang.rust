#[test]
pub fn listing0 () { fgi_listing_test![

    let set:(
        Thk[0] foralli X:NmSet.
            0 Nm[X] -> 0 Nat ->
        { {@!} X ; 0 }
        F Ref[{@!} X] Nat
    ) = {
        ret thunk #n.#x.
            ref n x
    }
    ret 0
]}


#[test]
pub fn listing0_fail0 () { fgi_listing_expect![
    [Expect::Failure]

    let set:(
        Thk[0] foralli X:NmSet.
            0 Nm[X] -> 0 Nat ->
        { 0 ; 0 }  // <------- Forgot `{@!} X`
        F Ref[{@!} X] Nat
    ) = {
        ret thunk #n.#x.
            ref n x
    }
    ret 0
]}

#[test]
pub fn listing0_fail1 () { fgi_listing_expect![
    [Expect::Failure]

    let set:(
        Thk[0] foralli X:NmSet.
            0 Nm[X] -> 0 Nat ->
        { {@!} X ; 0 }
        F Ref[X] Nat   // <------- Forgot `{@!} _`
    ) = {
        ret thunk #n.#x.
            ref n x
    }
    ret 0
]}

#[test]
pub fn listing0_fail2 () { fgi_listing_expect![
    [Expect::Failure]

    let set:(
        Thk[0] foralli X:NmSet.
            0 Nm[X] -> 0 Nat ->
        { {@!} X ; 0 }
        F Ref[{@!} X] Nat
    ) = {
        ret thunk #n.#x.
            let r = { ref n x }
            ref n x  // <------------ double-write to `n`
    }
    ret 0
]}
