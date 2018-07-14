#[test]
pub fn listing0 () { fgi_listing_expect![ [Expect::SuccessxXXX]

    let foo:(
        Thk[0] foralli (X,Y):NmSet.
            0 Bool ->
            0 Nm[X] ->
            0 Nm[Y] ->
        { {@!}(X%Y) ; 0 }
        F (exists (Z):NmSet | (Z=(X%Y):NmSet).
           (x Nm[Z] x Ref[{@!}(Z)] Nat))
    ) = {
        ret thunk #b. #nx. #ny.
            if (b) {
                let r = {ref nx 1}
                ret pack X (nx, r)
            } else {
                let r = {ref ny 2}
                ret pack Y (ny, r)
            }
    }
    ret 0
]}


#[test]
pub fn listing1 () { fgi_listing_expect![ [Expect::SuccessxXXX]
    let foo:(
        Thk[0] foralli (X,Y,Z):NmSet.
            0 Bool ->
            0 Nm[X] ->
            0 Nm[Y] ->
            0 Nm[Z] ->
        { {@!}(X%Y) ; 0 }
        F (exists (ZZ):NmSet | (ZZ=(X%Y):NmSet).
           (x Nm[ZZ%Z] x Ref[{@!}(ZZ)] Nat))
    ) = {
        ret thunk #b. #nx. #ny. #nz.
            if (b) {
                let r = {ref nx 1}
                ret pack X (nx, r)
            } else {
                let r = {ref ny 2}
                ret pack Y (nz, r) // <------- Note that 'nz : Nm[Z]'
            }
    }
    ret 0
]}

#[test]
pub fn listing1_fail0 () { fgi_listing_expect![[Expect::Failure]

    let foo:(
        Thk[0] foralli (X,Y,Z):NmSet.
            0 Bool ->
            0 Nm[X] ->
            0 Nm[Y] ->
            0 Nm[Z] ->
        { {@!}(X%Y) ; 0 }
        F (exists (ZZ):NmSet | (ZZ=(X%Y):NmSet).
           (x Nm[ZZ] x Ref[{@!}(ZZ)] Nat))
    ) = {
        ret thunk #b. #nx. #ny. #nz.
            if (b) {
                let r = {ref nz 1} // <------ Should be 'nx'
                ret pack X (nx, r)
            } else {
                let r = {ref ny 2}
                ret pack Y (ny, r)
            }
    }
    ret 0
]}

#[test]
pub fn listing1_fail1 () { fgi_listing_expect![[Expect::Failure]

    let foo:(
        Thk[0] foralli (X,Y,Z):NmSet.
            0 Bool ->
            0 Nm[X] ->
            0 Nm[Y] ->
            0 Nm[Z] ->
        { {@!}(X%Y) ; 0 }
        F (exists (ZZ):NmSet | (ZZ=(X%Y):NmSet).
           (x Nm[ZZ] x Ref[{@!}(ZZ)] Nat))
    ) = {
        ret thunk #b. #nx. #ny. #nz.
            if (b) {
                let r = {ref nx 1}
                ret pack X (nx, r)
            } else {
                let r = {ref ny 2}
                ret pack X (ny, r) // <--- Should be 'pack Y ...'
            }
    }
    ret 0
]}
