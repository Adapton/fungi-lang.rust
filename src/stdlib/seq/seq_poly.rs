fgi_mod!{
    // In this variation, sequences are parameterized by a generic
    // element type, T, which itself is parameterized by two name
    // sets, X and Y.  As with other versions, the sequence is also
    // parameterized by these two sets, X and Y.
    type Seq = (
        rec Seq.
            foralli (X,Y): NmSet.
            forallt T.
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
    idxtm max    = #X:NmSet.(bin X);
    idxtm map    = #X:NmSet.(bin X);
    idxtm filter = #X:NmSet.(bin X);
        
    fn is_empty:(
        Thk[0] foralli (X,Y):NmSet. forallt T:type.
            0 (Seq[X][Y] T) ->
        { 0; Y }
        F Bool
    ) = {
        unimplemented
    }

    fn is_empty_shallow:(
        Thk[0] foralli (X,Y):NmSet. forallt T:type.
            0 (Seq[X][Y] T) ->
        { 0; 0 }
        F Bool
    ) = {
        unimplemented
    }

    fn is_singleton:(
        Thk[0] foralli (X,Y):NmSet. forallt T:type.
            0 (Seq[X][Y] T) ->
        { 0; 0 }
            0 F Bool
    ) = {
        unimplemented
    }

    // In progress (not sure these types are right yet):
    fn monoid:(
        Thk[0] foralli (X,Y):NmSet.
            forallt (T,S):type.
            0 (Seq[X][Y] T) ->
            0 (Thk[0] 0 T -> 0 F S) ->
            0 (Thk[0] 0 S -> 0 S -> 0 F S) ->
        {bin X; Y}
        0 F S
    ) = {
        unimplemented
    }
}
