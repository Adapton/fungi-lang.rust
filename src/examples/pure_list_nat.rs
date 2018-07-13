#[test]
pub fn listing0 () { fgi_listing_expect![
    [Expect::Success]
        
    decls {
        /// Lists of natural numbers
        type List  = ( rec list. (+ Unit + (x Nat x list)) );
        //type List  = (+ Unit + (x Nat x List));

        /// Optional natural numbers
        type OpNat  = (+ Unit + Nat );
    }

    let nat_is_zero:(Thk[0] 0 Nat -> 0 F Bool) = { unsafe (1) trapdoor::nat_is_zero }
    let nat_sub:(Thk[0] 0 Nat -> 0 Nat -> 0 F Nat) = { unsafe (2) trapdoor::nat_sub }

    let nil:(
        Thk[0] 0 F List
    ) = {
        ret thunk ret roll inj1 ()
    }

    let cons:(
        Thk[0] 0 Nat -> 0 List -> 0 F List
    ) = {
        ret thunk #h.#t. ret roll inj2 (h, t)
    }

    let rec gen:(
        Thk[0] 0 Nat -> 0 F List
    ) = {
        #n. if {{force nat_is_zero} n} {
            force nil
        } else {
            let m = {{force nat_sub} n 1}
            let l = {{force gen} m}
            {{force cons} m l}
        }
    }

    let rec map:(
        Thk[0]
            0 (Thk[0] 0 Nat -> 0 F Nat) ->
            0 List ->
            0 F List
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                let (h, t) = { ret c }
                let h2 = {{force f} h}
                let t2 = {{force map} f t}
                {{force cons} h2 t2}
            }
        }
    }

    let rec filter:(
        Thk[0]
            0 (Thk[0] 0 Nat -> 0 F Bool) ->
            0 List ->
            0 F List
    ) = {
        #f. #l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                let (h, t) = { ret c }
                let t2 = {{force filter} f t}
                if {{force f} h} {
                    {{force cons} h t2}
                } else {
                    ret t2
                }
            }
        }
    }

    let rec map_filter:(
        Thk[0]
            0 (Thk[0] 0 Nat -> 0 F OpNat) ->
            0 List ->
            0 F List
    ) = {
        #f. #l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                let (h, t) = { ret c }
                let t2 = {{force map_filter} f t}
                let oh2 = {{force f} h}
                match oh2 {
                    _u => { ret t2 }
                    h2 => {{force cons} h t2}
                }
            }
        }
    }

    let rec reverse:(
        Thk[0]
            0 List ->
            0 List ->
            0 F List
    ) = {
        #l.#r. unroll match l {
            _u => { ret r }
            c => {
                let (h, t) = { ret c }
                let r2 = {{force cons} h r}
                {{force reverse} t r2}
            }
        }
    }

    let rec fold:(
        Thk[0]
            0 List ->
            0 Nat ->
            0 (Thk[0] 0 Nat -> 0 Nat -> 0 F Nat) ->
            0 F Nat
    ) = {
        #l.#a.#f. unroll match l {
            _u => { ret a }
            c => {
                let (h, t) = { ret c }
                let a2 = {{force f} a h}
                {{force fold} t a2 f}
            }
        }
    }

    ret 0
]}

// TODO (Hammer):
//
// Once we have a fuller story for the module system, move these
// natural number primmitives into an appropriate module for them.

pub mod trapdoor {
    // This code essentially extends the Fungi evaluator
    use dynamics::{RtVal,ExpTerm};

    pub fn nat_is_zero(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => {
                ExpTerm::Ret(RtVal::Bool(n == &0))
            },
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }

    pub fn nat_is_odd(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => {
                ExpTerm::Ret(RtVal::Bool(n.checked_rem(2) == Some(1)))
            },
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }

    pub fn nat_is_even(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => {
                ExpTerm::Ret(RtVal::Bool(n.checked_rem(2) == None))
            },
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }

    pub fn nat_sub(args:Vec<RtVal>) -> ExpTerm {
        match (&args[0], &args[1]) {
            (RtVal::Nat(n), RtVal::Nat(m)) => {
                assert!(n >= m);
                //println!("{:?} - {:?} = {:?}", n, m, n - m);
                ExpTerm::Ret(RtVal::Nat(n - m))
            },
            (v1, v2) =>
                panic!("expected two natural numbers, not: {:?} and {:?}", v1, v2)

        }
    }
}

/* Run as (shortened version):
   cargo test examples::pure_list_nat::static 2>&1 | less -R
*/
// pub mod static_tests {
//     #[test]
//     pub fn typing() { fgi_listing_test!{
//         use super::*;
//         ret 0
//     }}
// }

pub mod dynamic_tests {

    #[test]
    fn listing1() {
        use reduce;
        use dynamics;
        use std::rc::Rc;
        use ast::*;
        //use bitype::*;

        // TODO (Hammer):
        //
        // Use the module system to import (or somehow avoid
        // repeating) the definitions from above that are used below.
        //
        let e = fgi_exp![
            // COPY (from above)
            decls {
                /// Lists of natural numbers
                type List  = (+ Unit + (x Nat x List));
            }
            // COPY (from above)
            let nil:(
                Thk[0] 0 F List
            ) = {
                ret thunk ret roll inj1 ()
            }
            // COPY (from above)
            let cons:(
                Thk[0] 0 Nat -> 0 List -> 0 F List
            ) = {
                ret thunk #h.#t. ret roll inj2 (h, t)
            }
            // COPY (from above, adjusted a bit)
            let nat_is_zero:(
                Thk[0]
                    0 Nat -> 0 F Nat
            ) = {
                ret thunk #n.
                    {unsafe (1) super::trapdoor::nat_is_zero} n
            }
            // COPY (from above, adjusted a bit)
            let nat_is_odd:(
                Thk[0]
                    0 Nat -> 0 F Nat
            ) = {
                ret thunk #n.
                    {unsafe (1) super::trapdoor::nat_is_odd} n
            }
            // COPY (from above, adjusted a bit)
            let nat_sub:(
                Thk[0]
                    0 Nat -> 0 Nat -> 0 F Nat
            ) = {
                ret thunk #n.#m.
                    {unsafe (2) super::trapdoor::nat_sub} n m
            }
            // COPY (from above)
            let rec gen:(
                Thk[0]
                    0 Nat -> 0 F List
            ) = {
                #n. if {{force nat_is_zero} n} {
                    force nil
                } else {
                    let m = {{force nat_sub} n 1}
                    let l = {{force gen} m}
                    {{force cons} m l}
                }
            }
            // COPY (from above)
            let rec map:(
                Thk[0]
                    0 (Thk[0] 0 Nat -> 0 F Nat) ->
                    0 List ->
                    0 F List
            ) = {
                #f.#l. unroll match l {
                    _u => { ret roll inj1 () }
                    c => {
                        let (h, t) = { ret c }
                        let h2 = {{force f} h}
                        let t2 = {{force map} f t}
                        {{force cons} h2 t2}
                    }
                }
            }
            // COPY (from above)
            let rec filter:(
                Thk[0]
                    0 (Thk[0] 0 Nat -> 0 F Bool) ->
                    0 List ->
                    0 F List
            ) = {
                #f.#l. unroll match l {
                    _u => { ret roll inj1 () }
                    c => {
                        let (h, t) = { ret c }
                        let t2 = {{force filter} f t}
                        if {{force f} h} {
                            {{force cons} h t2}
                        } else {
                            ret t2
                        }
                    }
                }
            }
            // COPY (from above)
            let rec reverse:(
                Thk[0]
                    0 List ->
                    0 List ->
                    0 F List
            ) = {
                #l.#r. unroll match l {
                    _u => { ret r }
                    c => {
                        let (h, t) = { ret c }
                        let r2 = {{force cons} h r}
                        {{force reverse} t r2}
                    }
                }
            }
            // COPY (from above)
            let rec fold:(
                Thk[0]
                    0 List ->
                    0 Nat ->
                    0 (Thk[0] 0 Nat -> 0 Nat -> 0 F Nat) ->
                    0 F Nat
            ) = {
                #l.#a.#f. unroll match l {
                    _u => { ret a }
                    c => {
                        let (h, t) = { ret c }
                        let a2 = {{force f} a h}
                        {{force fold} t a2 f}
                    }
                }
            }

            // ----------------------------------------
            // the test script to run (via reduce)
            //
            let list1 = {{force gen} 5}
            let list2 = {{force map} (thunk #x. x + 1) list1}
            let list3 = {{force filter} nat_is_odd list2}
            let list4 = {{force reverse} list3 (roll inj1 ())}
            let sumodd = {{force fold} list4 0 (thunk #n.#m. n + m)}
            ret (list1, list2, list3, list4, sumodd)
            //
            // Produces the tuple:
            /*
                ([4,3,2,1,0],
                 [5,4,3,2,1],
                 [5,3,1],
                 [1,3,5],
                 9)
             */
        ];
        let t = reduce::reduce(vec![], dynamics::env_emp(), e);
        println!("{:?}", t);
        drop(t)
    }
}
