use examples::seq_nat;
use examples::stream_nat;

pub mod dynamic_tests {
    /*
     * Try the following at the command line:
     *
     *  $ export FUNGI_VERBOSE_REDUCE=1
     *
     *  $ cargo test examples::seq_nat_dfs -- --nocapture | less -R
     *
     */
    #[test]
    pub fn short() { fgi_dynamic_trace!{
        [Expect::SuccessXXX]
        open crate::examples::seq_nat_dfs_lazy;
        open crate::examples::seq_nat_gen;

        /// Generate the input sequence
        let s = {{force seq_gen} 10}

        /// Perform the DFS
        let nil = {ref (@@nil) inj1 ()}
        let l = { ws(@@dfs){ memo(@@dfs){{force seq_dfs_lazy} s nil} } }

        /// All done
        ret (s, l)
    }}
}

fgi_mod!{
    open crate::examples::stream_nat;
    open crate::examples::seq_nat;

    fn seq_dfs_lazy:(
        Thk[0]
            0 Ref[?](Seq[?][?]) ->
            0 (Stream[?][?]) ->
        {?;?}
        F (Stream[?][?])
    ) = {
        #seq. #res.
        let s = {get seq}
        unroll match s {
            _nil => {
                /// Enter NIL
                ret res
            }
            leaf => {
                /// Enter Leaf
                let (nm, x) = leaf
                /// FUBAR
                {force cons_stream} [?][?][?][?] nm x res
            }
            bin => {
                /// Enter BIN
                unpack (X1,X2,Y) bin = bin
                let (nm, lev, left, right) = bin
                let res = { thk nm {
                    let intres = {{force seq_dfs_lazy} right res}
                    force intres
                } }
                {{force seq_dfs_lazy} left res}
                //need thunk force here to ensure laziness
            }
        }
    }
}
