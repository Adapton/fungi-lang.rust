use examples::seq_nat;
use examples::list_nat;

fgi_mod!{
    use list_nat::*;
    use seq_nat::*;

    fn seq_dfs:(
        Thk[0]
            0 Ref[?](Seq[?][?]) ->
            0 Ref[?](Stream[?][?]) ->
        {?;?}
        F Ref[?](List[?][?])
    ) = {
        #seq. #res.
        let s = {get seq}
        unroll match s {
            _nil => { ret res }
            leaf => {
                let (nm, x) = leaf
                {force ref_cons} [?][?][?][?] nm x res
            }
            bin => {
                unpack (X1,X2,Y) bin = bin
                let (nm, lev, left, right) = bin
                let res = {{force seq_dfs} right res}
                {{force seq_dfs} left res}
            }
        }
    }
}

pub mod dynamic_tests {
    use examples::seq_nat_gen;

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
        [Expect::SuccessxXXX]
        use super::*;
        use seq_nat_gen::*;

        /// Generate the input sequence
        let s = {{force seq_gen} 10}

        /// Perform the DFS
        let nil = {ref (@@nil) inj1 ()}
        let l = {{force seq_dfs} s nil}

        /// All done
        ret (s, l)
    }}
}
