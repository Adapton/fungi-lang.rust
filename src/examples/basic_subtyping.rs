#[test]
pub fn listing0_check2 () { fgi_listing_test![

    let put_one:(
        Thk[0] foralli (X,Y,Z):NmSet.
            0 Bool ->
            0 Nm[X%Z] ->
            0 Nm[Y%Z] ->
        { {@!}(X%Y%Z) ; 0 }
        F Ref[{@!}(X%Y%Z)] Nat
    ) = {
        ret thunk #b. #nxz. #nyz.
            if (b) { ref nxz 0 } else { ref nyz 1 }
    }
    ret 0
]}

#[test]
pub fn listing0_synth2 () { fgi_listing_test![

    let put_one:(
        Thk[0] foralli (X,Y,Z):NmSet.
            0 Bool ->
            0 Nm[X%Z] ->
            0 Nm[Y%Z] ->
        { {@!}(X%Y%Z) ; 0 }
        F Ref[{@!}(X%Y%Z)] Nat
    ) = {
        ret thunk #b. #nxz. #nyz.
            if (b) {
                let r1 = { ref nxz 0 }
                ret r1
            } else {
                let r2 = { ref nyz 0 }
                ret r2
            }
    }
    ret 0
]}
