use std::rc::Rc;
use ast::*;

// Proposal: implement stdlib vector operations using a general
// trapdoor into Rust.  Example use given below.

// Summary: In this case, and perhaps others, we want a
// primitive-level concept in core Fungi (a vector), but want to avoid
// having special AST forms for the associated vector operations, and
// thus, avoid special evaluation forms.  We made such special PrimApp
// forms for some natural number operations; it was somewhat tedious.
//
// Instead, the "unsafe trapdoor" below permits library-based
// extensions of the Fungi evaluator to be packed with an associated
// type and glue code, both written in concrete Fungi syntax.  Hence,
// Fungi user programs may be written partially in Rust, which
// marshals from and to the Fungi runtime representation to compute
// (exactly like the Fungi evaluator itself).
//
// The one "catch" is that we really need a RtVal representation of
// each value, including vectors.  For "primitives" (such as vectors),
// it makes sense to bake these forms into the make `RtVal`
// representation.
//

mod trapdoor {
    // This code essentially extends the Fungi evaluator
    use eval::{RtVal,ExpTerm};

    fn vec_gen_range(args:Vec<RtVal>) -> ExpTerm {
        // gen_range(count)
        match (&args[0], &args[1]) {
            _ => panic!("TODO")
        }
    }
    
    fn vec_filter(args:Vec<RtVal>) -> ExpTerm {
        // filter(vector, userfun)
        match (&args[0], &args[1]) {
            _ => panic!("TODO")
        }
    }
    
    fn vec_map(args:Vec<RtVal>) -> ExpTerm {
        // map(vector, userfun)
        match (&args[0], &args[1]) {
            _ => panic!("TODO")
        }
    }
    
    fn vec_fold(args:Vec<RtVal>) -> ExpTerm {
        // fold(vector, accum0, userfun)
        match (&args[0], &args[1], &args[2]) {
            _ => panic!("TODO")
        }
    }
    
    fn vec_fold_rev(args:Vec<RtVal>) -> ExpTerm {
        // fold_rev(vector, accum0, userfun)
        match (&args[0], &args[1], &args[2]) {
            _ => panic!("TODO")
        }
    }
}

pub fn fgi_module () -> Module {fgi_module!{
    
    fn vec_gen_range:(
        Thk[0] 0 Nat -> 0 F Vec Nat
    ) = {
        #n.
        unsafe (1) trapdoor::vec_gen_range
            n
    }

    fn vec_fold:(
        Thk[0] forallt a:type.
            0 Vec a -> 0 b ->
            0 (Thk[0] 0 a -> 0 b -> 0 F b) ->
            0 F b
    ) = {
        #v.#b.#f.
        unsafe (3) trapdoor::vec_fold
            v b f
    }

    fn vec_fold_rev:(
        Thk[0] forallt a:type.
            0 Vec a -> 0 b ->
            0 (Thk[0] 0 a -> 0 b -> 0 F b) ->
            0 F b
    ) = {
        #v.#b.#f.
        unsafe (3) trapdoor::vec_fold_rev
            v b f
    }

    fn vec_filter:(
        Thk[0] forallt a:type.
            0 Vec a ->
            0 (Thk[0] 0 a -> 0 F Bool) ->
            0 F Vec a
    ) = {
        #v.#f.
        unsafe (2) trapdoor::vec_filter
            v f
    }
    
    fn vec_map:(
        Thk[0] forallt (a,b):type.
            0 Vec a ->
            0 (Thk[0] 0 a -> 0 F b) ->
            0 F Vec b
    ) = {
        #v.#f.
        unsafe (2) trapdoor::vec_map
            v f
    }
}}


mod nums {
    use std::rc::Rc;
    use ast::*;    
    pub fn fgi_module() -> Module { fgi_module!{
        // parsing example
        type Len = ( Nat )
        type Cnt = ( Nat );;;
        
        // for example
        val zero : ( Len ) = ( 0 )
        val one  : ( Len ) = ( 1 );
        val two  : ( Len ) = ( 2 );;;    
    }}
}

fn fgi_module_test () -> Module {fgi_module!{

    // import vector module
    use ( nums ) :: *;

}}

#[test]
fn vec() {
    println!("{:?}", fgi_module_test())
}
