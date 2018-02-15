#![recursion_limit="128"]
#[macro_use]
extern crate fungi_lang;
use fungi_lang::ast::*;
use std::rc::Rc;

fgi_inner_mod!{ pub (nums)
    type Len = ( Nat )
    type Cnt = ( Nat );;;
    val zero : ( Len ) = ( 0 )
    val one  : ( Len ) = ( 1 );
    val two  : ( Len ) = ( 2 );;;    
}
pub fn fgi_module_test () {
    let _ = fgi_module!{
        // import nums module, defined above
        use ( nums ) :: *;        
    };
}

#[test]
fn vec() {
    println!("{:?}", fgi_module_test())
}
