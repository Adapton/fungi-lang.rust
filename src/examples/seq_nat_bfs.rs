use examples::seq_nat;
use examples::list_nat;
use examples::fifo;
use examples::stream_nat;

fgi_mod!{
    use list_nat::*;
    use seq_nat::*;
    use fifo::*;
    use stream_nat::*;


    fn seq_bfs:(
        Thk[0]
            0 Ref[?](Queue) ->
            0 Stream ->
        {?;?}
        F Ref[?](List[?][?])
    ) = {
        #queue. #res.
        let q = {get queue}
        ret ()
    }
}

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

        /// Perform the BFS
        let nil = {ref (@@nil) inj1 ()}
        let l = {{force seq_bfs} s nil}

        /// All done
        ret (s, l)
    }}
}
