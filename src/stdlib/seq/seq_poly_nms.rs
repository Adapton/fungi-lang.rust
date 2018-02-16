fgi_mod!{
    // In this variation, sequences are parameterized by a generic
    // element type, T, which itself is parameterized by two name
    // sets, X and Y.  As with other versions, the sequence is also
    // parameterized by these two sets, X and Y.
    type Seq = (
        rec Seq.
            foralli (X,Y): NmSet.
            forallt T: NmSet => NmSet => type.
            (+ T[X][Y]
             + (exists (X1,X2,X3)   :NmSet | (X1%X2%X3=X).
                exists (Y1,Y2,Y3,Y4):NmSet | (Y1%Y2%Y3%Y4=Y).
                x Nm[X1] x Nat // <-- name and level
                x Ref[Y1](Seq[X2][Y2])
                x Ref[Y3](Seq[X3][Y4]))
            )
    );

    // name set function for naming structural recursion over binary
    // trees
    idxtm bin    = #x:Nm.{x,@1} % {x,@2};

    // Max, map and filter use the same patterns of named recursion:
    idxtm max    = #X:NmSet.(bin X) % X;
    idxtm map    = #X:NmSet.(bin X) % X;
    idxtm filter = #X:NmSet.(bin X) % X;
        
    fn is_empty:(
        Thk[0] foralli (X,Y):NmSet.
            forallt T: NmSet => NmSet => type.
            0 (Seq[X][Y] T) ->
        { 0; Y }
        F Bool
    ) = {
        unimplemented
    }

    fn is_empty_shallow:(
        Thk[0] foralli (X,Y):NmSet.
            forallt T: NmSet => NmSet => type.
            0 (Seq[X][Y] T) ->
        { 0; 0 }
        F Bool
    ) = {
        unimplemented
    }

    fn is_singleton:(
        Thk[0] foralli (X,Y):NmSet.
            forallt T: NmSet => NmSet => type.
            0 (Seq[X][Y] T) ->
            0 F Bool
    ) = {
        unimplemented
    }

    // In progress (not sure these types are right yet):
    fn monoid:(
        Thk[0] foralli (X,Y):NmSet.
            forallt (T,S): NmSet => NmSet => type.
            foralli (f,g): NmSet -> NmSet -> NmSet.
            0 (Seq[X][Y] T) ->
        // basecase: transform each T into an S, and transform its
        // name and pointer indices into f 0 x and g 0 X,
        // respectively.
            0 (foralli (X,Y):NmSet.
               Thk[0]
               0 T[X][Y] ->
               0 F S[f X 0][g X 0]
            ) ->
        // bin case: combine two S's, creating a third S.  the indices
        // of the two S's are combined with nameset functions f and g.
        // the summarize the "monoidal closure" of g (or f) over a
        // set, we use the (currently made up) notation `f** X`.  Note
        // that this notion of closure is different from a Kleene
        // closure, `f* X`, where `f` is a unary function (not a
        // binary function).
            0 (foralli (X1,X2,Y1,Y2):NmSet.
               Thk[0]
               0 S[X1][Y1] ->
               0 S[X2][Y2] ->
               0 F S[f X1 X2][g X1 X2]
            ) ->
            0 F S[f** X][g** X]
    ) = {
        unimplemented
    }
}
