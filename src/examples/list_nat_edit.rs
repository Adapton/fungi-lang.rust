use examples::{name,ref_edit,list_nat};

//
// Fungi module: Edit linked lists with names, holding natural numbers
//
fgi_mod!{
    use name::*;
    use ref_edit::*;
    use list_nat::*;
    
    /// Insert a Cons cell into a list, at the given Ref cell.
    //
    // XXX: Technically, this operation is only permitted by the editor:
    fn insert:(
        Thk[0]
            foralli (X1,X2,Y1,Y2):NmSet.
            0 Nm[X1] ->
            0 Nat ->
            0 Ref[Y1](List[X1%X2][Y2]) ->
        {Y1; Y1} // <-- XXX/TODO: An editor-level operation only
        F Unit
    ) = {
        #n.#h.#r.
        let l1 = {get r}
        let l2 = {{force cons_ref} [?][?][?][?] n h l1}
        {force ref_update} r l2
    }

    /// Remove the Cons cell within a Ref cell.  Return true if this
    /// Cons cell was removed, and false otherwise, if the Ref cell
    /// holds an empty list.
    //
    // XXX: Technically, this operation is only permitted by the editor:
    fn remove:(
        Thk[0]
            foralli (X1,X2,Y1,Y2):NmSet.
            0 Ref[Y1](List[X1%X2][Y2]) ->
        {Y1; Y1} // <-- XXX/TODO: An editor-level operation only
        F Bool
    ) = {
        #r.
        let l1 = {get r}
        unroll match l1 {
            _u => { ret false }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let l2 = {get t}
                let _u = {{force ref_update} r l2}
                ret true
            }
        }
    }

    /// Insert a Cons cell after a given name in a given list.
    /// Return true if successful, and false otherwise.
    fn insert_after:(
        Thk[0]
            foralli (X):NmSet.
            0 Nm[X1] ->
            0 Nm[X2] ->
            0 Nat ->
            0 List[X2%X3][Y] ->
        {Y;Y} // <-- XXX/TODO: An editor-level operation only
        F Bool
    ) = {
        #n1.#n2.#h.#l.
        unroll match l {
            _u => { ret false }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, _ch, t) = { ret c }
                if {{force name_eq} n n1 } {
                    let _u = {{force insert}[?][?][?][?] n2 h t}
                    ret true
                } else {
                    {force insert_after}[?] n1 n2 h {!t}
                }
            }
        }
    }

    /// Remove the Cons cell after a given name in a given list.
    /// Return true if successful, and false otherwise.
    fn remove_after:(
        Thk[0]
            foralli (X):NmSet.
            0 Nm[X1] ->
            0 List[X2%X3][Y] ->
        {Y;Y} // <-- XXX/TODO: An editor-level operation only
        F Bool
    ) = {
        #n1.#l.
        unroll match l {
            _u => { ret false }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                if {{force name_eq} n n1 } {
                    {force remove}[?][?][?][?] t
                } else {
                    {force remove_after}[?] n1 {!t}
                }
            }
        }
    }

    /// Generate a list of naturals [n - 1, n - 2, ..., 0]
    //
    // XXX -- This type is wrong.  TODO -- figure out how to
    // ecode this type correctly, with existentials.  
    fn gen:(
        Thk[0]
            foralli (Y1,X1,Y2):NmSet.
            0 Nat -> 0 F Ref[Y1](List[X1][Y2])
    ) = {
        #n. if {{force nat_is_zero} n} {
            ref (@0) roll inj1 ()
        } else {
            let nm = {{force name_of_nat} n}
            let p  = {{force nat_sub} n 1}
            let l  = {{force gen} p}
            {{force ref_cons}
             [X1][X1][X1][(Y1%Y2)][Y1][Y2]
             nm p l}
        }
    }
}
