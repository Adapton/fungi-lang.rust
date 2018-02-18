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
        // import modules defined in fungi_lang::stdlib
        use vec::*;
        use seq_nat::*;

        // import nums module, defined above
        use nums::*;

        /// now, we can use anything in either module, as if they were
        /// defined here:        
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
fn module () {
    use std::thread;
    let child =
        thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || { 
            module2()
        });
    let _ = child.unwrap().join();
}

fn module2() {
    use fungi_lang::bitype;

    let m : Rc<Module> = Rc::new(fgi_module_test());
    let md : bitype::ModuleDer = bitype::synth_module(None, &m);
    
    println!("{:?}", m)
}
