#[test]
pub fn listing () { fgi_listing_test![

    let foo:(
        Thk[0] 
        { {@!}( ({@666} % {@777}) * ({@1} % {@2}) );
          {@!}( ({@666} % {@777}) * ({@1} % {@2}) ) }
        F Nat
    ) = {
        ret thunk
        let bar = {
            ws (nmfn (#x:Nm. (@666) * x)) {
                let (a1,b1) = { memo(name @1){ ret 111 } }
                let (a2,b2) = { memo(name @2){ ret 222 } }
                ret 0
            }
        }
        let baz = {
            ws (nmfn (#x:Nm. (@777) * x)) {
                let (a1,b1) = { memo(name @1){ ret 111 } }
                let (a2,b2) = { memo(name @2){ ret 222 } }
                ret 0
            }
        }
        ret 0
    }

    ret 0
]}
