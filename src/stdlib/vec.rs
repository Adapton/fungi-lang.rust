use std::rc::Rc;
use ast::*;

pub fn exp () -> Exp { fgi_exp![

    type Vec = (forallt a:type. Vec a)
        
    fn vec_filter:(
        Thk[0]
            0 (Vec Nat) ->
            0 (Thk[0] 0 Nat -> 0 F Bool) ->
            0 F Vec Nat
    ) = {
        unimplemented
    }
    
    fn vec_map:(
        Thk[0]
            0 Vec Nat ->
            0 (Thk[0] 0 Nat -> 0 F Nat) ->
            0 F Vec Nat
    ) = {
        unimplemented
    }

    // Dummy "main"
    ret 0
]}
