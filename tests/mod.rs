#![recursion_limit="128"]
#[macro_use]
extern crate fungi_lang;
use fungi_lang::ast::*;
use std::rc::Rc;


use fungi_lang::stdlib::{vec,seq};
use fungi_lang::stdlib::seq::seq_nat;

fgi_inner_mod!{
    pub (nums)
    type Len = ( Nat );
    type Cnt = ( Nat );
    val zero : ( Len ) = ( 0 );
    val one  : ( Len ) = ( 1 );
    val two  : ( Len ) = ( 2 );;;;;;
}
pub fn fgi_module_test () -> Module {
    fgi_module!{
        // import vec module, defined in fungi_lang::stdlib::{vec};
        use vec::*;
        //use (seq::seq_nat)::*;
        use seq_nat::*;

        // import nums module, defined above
        use nums::*;
        // now, we can use anything in either module, as if they were
        // defined here:        
        val test_nums_vec : (Thk[0] 0 F (Nat x Vec Nat)) = (
            thunk {
                let x = {one + two}
                let v = {{force vec_gen_range} x}
                ret (x, v)
            }
        )
    }
}

#[test]
fn module() {
    println!("{:?}", fgi_module_test())
}
