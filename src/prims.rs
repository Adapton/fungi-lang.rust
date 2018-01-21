use ast::{Exp,Val,SeqObj,StackObj,QueueObj,HashmapObj,KvlogObj};
use eval::Env;

pub mod seq {
    use super::*;
    
    impl SeqObj for Vec<Val> {
        fn dup(&self) -> Box<SeqObj> {
            Box::new(self.clone())
        }
        fn fold_seq(&self, _v_nil:Val, _env:&Env, _exp_cons:&Exp) -> Val {
            unimplemented!()
        }
        fn fold_up(&self, _v_nil:Val, _env:&Env, _exp_leaf:&Exp, _exp_bin:&Exp) -> Val {
            unimplemented!()
        }
        fn empty(&self) -> Box<SeqObj> {
            unimplemented!()           
        }
        fn append(&self, _other:Val) -> Box<SeqObj> {
            unimplemented!()
        }
        fn map(&self, _env:&Env, _exp:&Exp) -> Box<SeqObj> {
            unimplemented!()
        }
        fn reverse(&mut self) {
            unimplemented!()
        }
        fn filter(&self, _env:&Env, _exp:&Exp) -> Box<SeqObj> {
            unimplemented!()
        }
        fn into_stack(&self, _rev:bool) -> Box<StackObj> {
            unimplemented!()
        }
        fn into_queue(&self, _rev:bool) -> Box<QueueObj> {
            unimplemented!()
        }
        fn into_hashmap(&self) -> Box<HashmapObj> {
            unimplemented!()
        }
        fn into_kvlog(&self) -> Box<KvlogObj> {
            unimplemented!()
        }
    }
}

pub mod stack {
    use super::*;

    impl StackObj for Vec<Val> {
        fn dup(&self) -> Box<SeqObj> {
            Box::new(self.clone())
        }
        fn push(&mut self, v:Val) {
            self.push(v)
        }
        fn pop(&mut self) -> Option<Val> {
            self.pop()
        }
        fn empty(&self) -> Box<SeqObj> {
            unimplemented!()
        }
        fn is_empty(&self) -> bool {
            unimplemented!()
        }
        fn peek(&self) -> Option<Val> {
            unimplemented!()
        }
        fn into_seq(&self) -> Box<SeqObj> {
            unimplemented!()
        }
    }

}
