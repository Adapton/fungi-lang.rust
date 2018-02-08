#![recursion_limit="1128"]
#[macro_use]
extern crate iodyn_lang;

use std::rc::Rc;
use iodyn_lang::bitype;
use iodyn_lang::tgt_ast::*;


#[test]
fn fungi_seq() {
    let e = iodyn_lang::fungi_stdlib::seq::exp();
    println!("{:?}", e);
}
