/*!

## Linked lists in Fungi

In most functional languages, **linked lists** play a central role in
organizing sequential data.  In Fungi, linked lists represent
"iterators", sequences in the midst of being processed or transformed.
To be incrementally efficient, Fungi programs do not use linked list
representations to structure recursive folds; instead, they use a
[balanced tree representation](https://docs.rs/fungi-lang/0/fungi_lang/stdlib/seq/index.html) 
for sequences.

In Fungi, computations induce dependency graphs that the runtime
system traverses during change propagation, and computations over
linked lists produce severely degenerate (unbalanced) recursive
sub-computations.  As a result, we reconsider the role of linked lists
in our incremental functional programs, and use them in fewer contexts
than in our ordinary (non-incremental) programs.

To organize sequences for efficient random accesses, random updates or
incremental folds, Fungi programs use balanced **level trees**.  In
particular, before a Fungi program iterates over a linked list, it
creates a balanced level tree from its elements to better organize
later incremental reuse, via change propagation.

*/

fgi_mod!{    
    type List = (
        rec Seq.#X.#Y.
            (+ Vec // <-- Basecase with no level, name or ref
             + (exists (X1,X2,X3)   :NmSet | (X1%X2%X3=X).
                exists (Y1,Y2,Y3,Y4):NmSet | (Y1%Y2%Y3%Y4=Y).
                x Nm[X1] x Nat // <-- Name and level
                x Vec // <-- elements here (a chunk in a vector)
                x Ref[Y1](Seq[X2][Y2])) // <-- Tail pointer
            )
    )
        
    // Convert sequence to the isomorphic list
    fn list_l2r_rec: (
        Thk[0] foralli (X,X1,X2,X3, Y,Y1,Y2):NmSet | ((X1%X2%X3)=X)and((Y1%Y2%Y3)=Y).
            0 (Seq[X1][Y1] Nat) ->
            0 (x Nm[X3] x Nat x Ref[Y3](List[X2][Y2])) ->
            ~~ X; Y ~~
            F List[X][Y]
    ) = {
        #seq. #rest. unroll match seq {
            vec => { ret roll inj2 (n,lev,vec,rest) }
            bin => {
                let (n,lev,l,r) = {ret bin}
                let (rr, _) = { memo{n,(@2)}{ {force list_l2r_rec} rest       {!r} } }
                let (_, ll) = { memo{n,(@1)}{ {force list_l2r_rec} (n,lev,rr) {!l} } }
                { ret ll }
            }
        }
    }        
    
    // Convert sequence to the isomorphic list
    // -- special rightmost recursion
    // (no accum info)
    fn list_l2r_rmost: (
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y] Nat) ->
            ~~ X; Y ~~
            F List[X][X]
    ) = {
        #seq. #rest. unroll match seq {
            vec => { ret roll inj1 vec }
            bin => {
                let (n,lev,l,r) = {ret bin}
                let (rr, _) = { memo{n,(@1)}{ {force list_l2r_rmost}          {!r} } }
                let (_, ll) = { memo{n,(@2)}{ {force list_l2r_rec} (n,lev,lr) {!l} } }
                { ret ll }
            }
        }
    }
    
    // Convert sequence to the isomorphic list, left-to-right
    fn list_l2r: (
        Thk[0] foralli (X,Y):NmSet.
            0 (Seq[X][Y] Nat) ->
            ~~ X; Y ~~
            F List[X][X]
    ) = { #seq. {force list_l2r_rmost} seq }
    
    
    // Convert a list into a balanced level tree (a sequence), with a single pass
    fn seq_of_list: (
        Thk[0] foralli (X,Y):NmSet.                
            0 List[X][Y] ->
            ~~ X;Y ~~
            F Seq[X][Y]
    ) = {
        unimplemented
    }
}
