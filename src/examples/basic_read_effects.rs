#[test]
pub fn listing0_ok () { fgi_listing_test![

    let get:(
        Thk[0] foralli X:NmSet.
            0 Ref[X] Nat ->
        { 0 ; X }
        F Nat
    ) = {
        ret thunk #r.
            let x = {get r}
            ret x
    }
    ret 0
]}

#[test]
pub fn listing0_err () { fgi_listing_expect![
    [Expect::Failure]
        
    let get:(
        Thk[0] foralli X:NmSet.
            0 Ref[X] Nat ->
        { 0 ; 0 }  // <----------- Should be `{0 ; X}`
        F Nat
    ) = {
        ret thunk #r.
            let x = {get r}
            ret x
    }
    ret 0
]}

#[test]
pub fn listing1_ok () { fgi_listing_test![
        
    let get:(
        Thk[0] foralli (X,Y):NmSet.
            0 Ref[X] Nat ->
            0 Ref[Y] Nat ->
        { 0 ; X % Y }
        F Nat
    ) = {
        ret thunk #rx. #ry.
            let x = {get rx}
            let y = {get ry}
            ret 0
    }
    ret 0
]}

