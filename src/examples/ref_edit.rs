fgi_mod!{
    /// Imperatively update a reference cell's content
    // XXX: Technically, this operation is only permitted by the editor (?)
    fn ref_update:(
        Thk[0] foralli X:NmSet. forall A.
            0 Ref[X]A ->
            0 A ->
        {X; 0} // <-- TODO: An editor-level operation only; we don't
        // have effect notation for this yet, but should.
        F Unit
    ) = {
        unsafe (2) trapdoor::ref_update
    }
}

pub mod trapdoor {
    // This code essentially extends the Fungi evaluator
    use crate::dynamics::{RtVal,ExpTerm};
    use adapton::engine;

    pub fn ref_update(args:Vec<RtVal>) -> ExpTerm {
        match (&args[0], &args[1]) {
            (RtVal::Ref(r), v) => {
                //println!("ref_update: {:?} <-- {:?}", r, v);
                engine::set(r, v.clone());
                ExpTerm::Ret(RtVal::Unit)
            },
            (r, v) => panic!("expected a reference cell and value, not: {:?} and {:?}", r, v)
        }
    }
}


pub mod static_tests {
    #[test]
    pub fn typing() { fgi_listing_test!{
        open crate::examples::ref_edit;
        ret 0
    }}
}
