/*
Errors found (or at least thought to be found):
1. When I need to force a LazyList in the body of a function,
I can't call it a LazyList, I have to substitute the full typedef
(presumably so system recognizes the presence of a Thunk).
Test: change annotation of e.g. reverse to have LazyList in first
line.
Expected: identical result (passes tests).
Result: fails tests with error returning on {force l}
*/
#[test]
pub fn listing0 () { fgi_listing_test![
    decls {
        //LazyLists, matching Elm type
        //type LazyList = Thk[0] 0 F (+ Unit + (x Nat x LazyList));
        type LazyList = (Thk[0] 0 F (+ Unit + (x Nat x LazyList)));

        type Stream = (+ Unit + (x Nat x (Thk[0] 0 F Stream)));

        //Optional natural numbers
        type OpNat = (+ Unit + Nat);
    }

    let nil:(
        Thk[0] 0 F LazyList
    ) = {
        ret thunk ret thunk ret roll inj1 ()
    }

    let cons:(
        Thk[0]
            0 Nat ->
            0 LazyList ->
            0 F LazyList
    ) = {
        ret thunk #h.#l. ret thunk ret roll inj2 (h, l)
    }

    let unlazy:(
        Thk[0]
            0 (Thk[0] 0 F (+ Unit + (x Nat x LazyList)))     ->
            0 F (+ Unit + (x Nat x LazyList))
    ) = {
        ret thunk #l. { force l }
    }

    let rec map:(
        Thk[0]
            0 (Thk[0] 0 Nat -> 0 F Nat) ->
            0 (Thk[0] 0 F (+ Unit + (x Nat x LazyList))) ->
            0 F LazyList
    ) = {
        #f.#l.
            let rl = { force l }
            unroll match rl {
            _u => { {force nil} }
            c => {
                let (h, tl) = { ret c }
                let h2 = {{force f} h}
                let t2 = {{force map} f tl}
                {{force cons} h2 t2}
                //TODO: should be lazy - cons wrong?
            }
        }
    }

    let rec filter:(
        Thk[0]
            0 (Thk[0] 0 Nat -> 0 F Bool) ->
            0 (Thk[0] 0 F (+ Unit + (x Nat x LazyList))) ->
            0 F LazyList
    ) = {
        #f.#l.
            let rl = { force l }
            unroll match rl {
                _u => { {force nil} }
                c => {
                    let (h, tl) = { ret c }
                    let t2 = {{force filter} f tl}
                    if {{force f} h} {
                        {{force cons} h t2}
                    } else {
                        ret t2 //TODO: lazy? doesn't feel like it. Cons wrong?
                    }
                }
            }
    }


    let rec reverse:(
        Thk[0]
            0 (Thk[0] 0 F (+ Unit + (x Nat x LazyList))) ->
            0 LazyList ->
            0 F LazyList
    ) = {
        #l.#r.
            let rl = { force l }
            unroll match rl {
                _u => { ret r }
                c => {
                    let (h, tl) = { ret c }
                    let r2 = {{force cons} h r}
                    {{force reverse} tl r2}
                }
            }
    }

    let rec fold:(
        Thk[0]
            0 (Thk[0] 0 F (+ Unit + (x Nat x LazyList))) ->
            0 Nat ->
            0 (Thk[0] 0 Nat -> 0 Nat -> 0 F Nat) ->
            0 F Nat
    ) = {
        #l.#a.#f.
            let rl = { force l }
            unroll match rl {
                _u => { ret a }
                c => {
                    let (h, tl) = { ret c }
                    let a2 = {{force f} a h}
                    {{force fold} tl a2 f}
                }
            }
    }


    ret 0
]}
