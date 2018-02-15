#![recursion_limit="128"]
#[macro_use]
extern crate fungi_lang;
use fungi_lang::ast::*;
use std::rc::Rc;
use fungi_lang::stdlib::{vec};

fgi_inner_mod!{
    pub (nums)
    type Len = ( Nat )
    type Cnt = ( Nat );;;
    val zero : ( Len ) = ( 0 )
    val one  : ( Len ) = ( 1 );
    val two  : ( Len ) = ( 2 );;;    
}
pub fn fgi_module_test () -> Module {
    fgi_module!{ 
        use ( vec ) :: *;
        // import nums module, defined above
        use ( nums ) :: *;        
    }
}

#[test]
fn module() {
    println!("{:?}", fgi_module_test())
}
