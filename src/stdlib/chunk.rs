fgi_mod!{
    /// A chunk is a pair of a name and a referenced vector.
    type Chk = (
        forallt a:type.
            foralli (X,Y):NmSet.
            Nm[X] x Ref[Y](Vec a)
    )

    /// reduce a chunk, using a vector-level reduction function.
    fn chk_reduce:(
        Thk[0] forallt (a,b):type.
            foralli (X,Y):NmSet.
            0 (Chk[X][Y] a) ->
            0 (Thk[0] 0 Vec a -> 0 F b) ->
        {X; Y}
        F ((Ref[X] b) x b)
    ) = {
        #c.#f.
        let (n,r) = {ret c}
        memo(n){ {force f} {!r} }
    }

    /// filter a chunk, using an element-level predicate.
    fn chk_filter:(
        Thk[0] forallt a:type.
            0 (Chk[X][Y] a) ->
            0 (Thk[0] 0 a -> 0 F Bool) ->
        {X; Y}
        F (Chk[X][X] a)
    ) = {
        #c.#f.
        let (rout,_) = {
            {force chk_reduce}
            c (thunk #vec. {force vec_filter} f)
        }
        ret (n,rout)
    }

    /// filter a chunk, using an element-level predicate.
    fn chk_filter__inlined_version:(
        Thk[0] forallt a:type.
            0 (Chk[X][Y] a) ->
            0 (Thk[0] 0 a -> 0 F Bool) ->
        {X; Y}
        F (Chk[X][X] a)
    ) = {
        #c.#f.
        let (n,rinp) = { ret c }
        let (rout,_) = { memo(n){
            {force vec_filter} f {!rinp}
        } }
        ret (n,rout)
    }

    /// map a chunk, using an element-level mapping function.
    fn chk_map:(
        Thk[0] forallt (a,b):type.
            foralli (X,Y):NmSet.
            0 Chk[X][Y] a ->
            0 (Thk[0] 0 a -> 0 F b) ->
        {X; Y}
        F (Chk[X][X] b)
    ) = {
        #c.#f.
        let (n,rinp) = {ret c}
        let (rout,_) = { memo(n){
            {force vec_map} f {!rinp}
        } } 
        ret (n,rout)
    }
}
