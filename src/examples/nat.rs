fgi_mod!{
    /// Return true if the given natural number is zero, false otherwise.
    fn nat_is_zero:(Thk[0] 0 Nat -> 0 F Bool)
        = { unsafe (1) trapdoor::nat_is_zero }

    /// Return true if the given natural number is odd, false otherwise.
    fn nat_is_odd:(Thk[0] 0 Nat -> 0 F Bool)
        = { unsafe (1) trapdoor::nat_is_odd }

    /// Return the difference of two natural numbers, as a natural number.
    fn nat_sub:(Thk[0] 0 Nat -> 0 Nat -> 0 F Nat)
        = { unsafe (2) trapdoor::nat_sub }

    /// Optional natural numbers
    type OpNat  = (+ Unit + Nat );

    /// If the given number is even, return its successor
    fn nat_succ_even:(Thk[0] 0 Nat -> 0 F OpNat) = {
        #n. if {{force nat_is_odd} n} {
            let m = {n + 1}
            ret inj2 m
        } else {
            ret inj1 ()
        }
    }
}

pub mod trapdoor {
    // This code essentially extends the Fungi evaluator
    use crate::dynamics::{RtVal,ExpTerm};
    
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

pub mod static_tests {
    #[test]
    pub fn typing() { fgi_listing_test!{
        use super::*;
        ret 0
    }}
}
