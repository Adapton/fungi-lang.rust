//
// Fungi module: linked lists with names, holding natural numbers
//
fgi_mod!{

    /// Convert a natural number into a name
    //
    // XXX -- This type is wrong.  TODO -- figure out how to
    // ecode this type correctly, with existentials.
    fn name_of_nat:(
        Thk[0] 
            foralli X:NmSet.
            0 Nat -> 0 F Nm[X]
    ) = {
        unsafe (1) trapdoor::name_of_nat
    }

    /// Test if two names are equal
    fn name_eq:(
        Thk[0] 
            foralli (X,Y):NmSet.
            0 Nm[X] -> 0 Nm[Y] -> 0 F Bool
    ) = {
        unsafe (2) trapdoor::name_eq
    }
}

pub mod trapdoor {
    // This code essentially extends the Fungi evaluator
    use crate::ast::{Name};
    use crate::dynamics::{RtVal,ExpTerm};
    
    pub fn name_of_nat(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => { 
                ExpTerm::Ret(RtVal::Name(Name::Num(*n)))
            }
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }

    pub fn name_eq(args:Vec<RtVal>) -> ExpTerm {
        match (&args[0],&args[1]) {
            (RtVal::Name(n1), RtVal::Name(n2)) => {
                ExpTerm::Ret(RtVal::Bool(n1 == n2))
            }
            (v1, v2) => panic!("expected two names, not: {:?} and {:?}", v1, v2)
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
