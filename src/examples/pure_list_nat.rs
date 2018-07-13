//
// Fungi module: linked lists (_without_ names/references), holding natural numbers
//               Compare to list_nat module, with names/references.
//
fgi_mod!{
    /// Lists of natural numbers
    type List  = ( rec list. (+ Unit + (x Nat x list)) );
    //type List  = (+ Unit + (x Nat x List));
    
    /// Optional natural numbers
    type OpNat  = (+ Unit + Nat );

    fn nat_is_zero:(Thk[0] 0 Nat -> 0 F Bool) = { unsafe (1) trapdoor::nat_is_zero }
    fn nat_is_odd:(Thk[0] 0 Nat -> 0 F Bool) = { unsafe (1) trapdoor::nat_is_odd }
    fn nat_sub:(Thk[0] 0 Nat -> 0 Nat -> 0 F Nat) = { unsafe (2) trapdoor::nat_sub }

    fn nil:(
        Thk[0] 0 F List
    ) = {
        ret roll inj1 ()
    }

    fn cons:(
        Thk[0] 0 Nat -> 0 List -> 0 F List
    ) = {
        #h.#t. ret roll inj2 (h, t)
    }

    fn gen:(
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

    fn map:(
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

    fn filter:(
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

    fn map_filter:(
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

    fn reverse:(
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

    fn fold:(
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
}

/* Try running as (using the shortened version):
 *
 *  $ cargo test examples::pure_list_nat::static -- --nocapture 2>&1 | less -R
 */
pub mod static_tests {
    #[test]
    pub fn typing() { fgi_listing_test!{
        use super::*;
        ret 0
    }}
}

/* 
 * Try the following at the command line:
 * 
 *  $ export FUNGI_VERBOSE_REDUCE=1
 *
 *  $ cargo test examples::pure_list_nat::dynamic -- --nocapture 2>&1 | less -R
 *
 */
pub mod dynamic_tests {
    #[test]
    pub fn reduction() { fgi_dynamic_trace!{ [Expect::Success]
        use super::*;
        let list1 = {{force gen} 5}
        let list2 = {{force map} (thunk #x. x + 1) list1}
        let list3 = {{force filter} nat_is_odd list2}
        let list4 = {{force reverse} list3 (roll inj1 ())}
        let sumodd = {{force fold} list4 0 (thunk #n.#m. n + m)}
        ret (list1, list2, list3, list4, sumodd)
    }}
    // TODO: Assert that the output of the listing above is correct.
}

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
