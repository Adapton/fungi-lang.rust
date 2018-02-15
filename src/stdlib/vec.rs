
fgi_mod!{    
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
}

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

