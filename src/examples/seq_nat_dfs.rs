use examples::seq_nat;
use examples::list_nat;

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
    pub fn short() { use examples::*; fgi_dynamic_trace!{
        [Expect::SuccessxXXX]
        use super::*;
        use seq_nat_gen::*;

        /// Generate the input sequence
        let s = {{force seq_gen} 10}

        /// Perform the DFS
        let nil = {ref (@@nil) inj1 ()}
        let dfs = {thk (@@seq_dfs)
            ws(@@seq_dfs){ {force seq_dfs_m} s nil }
        }
        let res1 = {force dfs}
        
        /// Insert element into sequence
        /// TODO

        /// Re-demand output of DFS
        let res2 = {force dfs}

        /// Remove element from sequence
        /// TODO

        /// Re-demand output of DFS
        let res3 = {force dfs}

        /// All done
        ret ()
    }}
}

fgi_mod!{
    use list_nat::*;
    use seq_nat::*;

    // before/without memoization
    fn seq_dfs:(
        Thk[0]
            0 Ref[?](Seq[?][?]) ->
            0 Ref[?](List[?][?]) ->
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

    // use memoization on recursive calls
    fn seq_dfs_m:(
        Thk[0]
            0 Ref[?](Seq[?][?]) ->
            0 Ref[?](List[?][?]) ->
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
                let (res, _res) = {memo{nm,(@1)}{ {force seq_dfs_m} right res }}
                let (res, _res) = {memo{nm,(@2)}{ {force seq_dfs_m} left res  }}
                ret res
            }
        }
    }
}

    
