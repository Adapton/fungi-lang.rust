fgi_mod!{
    /// Linked lists, with names; similar definition to list_nat.rs,
    /// but index Y treated differently here.
    type List = (
        rec list.
            foralli (X,Y):NmSet.
            ( + Unit + (exists (X1,X2):NmSet|((X1%X2)=X:NmSet).
                        (x Nm[X1] x Nat x Ref[Y](list[X2][Y]))))
    );
    type RefList = (
        foralli (X,Y):NmSet.
            Ref[Y] (List[X][Y])
    );

    /// Old type that we used for lists of natural numbers.
    /// The new version above is simpler: it doesn't introduce Y1 and Y2.
    type ListOld  = (
        rec list. foralli (X,Y):NmSet.
            (+ Unit +
             (exists (X1,X2):NmSet | ((X1%X2)=X:NmSet).
              exists (Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
              x Nm[X1] x Nat x Ref[Y1](list[X2][Y2])
             )
            )
    );

    // Convert the old list type into the new list type; use the
    // "structural recursion" naming strategy.
    fn convert: (
        Thk[0] foralli (X,Y):NmSet. 
            0 ListOld[X][Y] -> 
        {{@!}X; Y} 
        F List[X][{@!}X]
    ) = {
        #l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                // Eliminate four packs
                unpack (X1,X2,Y1,Y2) c = c
                let (x,y,ys) = {ret c}
                // Recursively convert the tail of the list
                let (ys2, _ys2) = {memo(x){{force convert}[X2][Y2] {!ys}}}
                // Introduce two packs, and drop/forget the indices Y1 and Y2 above
                ret roll inj2 pack (X1,X2) (x,y,ys2)
            }
        }
    }
}
