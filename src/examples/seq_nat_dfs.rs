use examples::seq_nat;

fgi_mod!{
    use seq_nat::*;
    
    fn seq_dfs:(
        Thk[0] Seq[?][?] -> {?;?} F List[?][?]
    ) = {
        /// TODO
        #s. ret ()
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
        let l = {{force seq_dfs} s}

        /// All done
        ret (s, l)
    }}
}
    
