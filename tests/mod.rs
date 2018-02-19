#![recursion_limit="128"]
#[macro_use]
extern crate fungi_lang;
use fungi_lang::ast::*;
use std::rc::Rc;

use fungi_lang::stdlib::{vec,seq};
use fungi_lang::stdlib::seq::seq_nat;

fgi_inner_mod!{
    pub (nums)
    /// Len type
    type Len = ( Nat );
    /// Cnt type
    type Cnt = ( Nat );
    /// smallest number
    val zero : ( Len ) = ( 0 );
    /// almost smallest number
    val one  : ( Len ) = ( 1 );
    /// one + one
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
    use fungi_lang::bitype::*;
    use fungi_lang::vis::*;
    
    //let m : Rc<Module> = Rc::new(fgi_module_test());
    //let md : bitype::ModuleDer = bitype::synth_module(None, &m);

    let bundle : Bundle = fgi_bundle![
        use seq_nat::*;
        ret 123
    ];
    use std::fs::File;
    use std::io::Write;        
    let data = format!("{:#?}", bundle);
    let mut f = File::create("target/mod.fgb").expect("Could not create bundle file");
    f.write_all(data.as_bytes()).expect("Could not write bundle data");
}
