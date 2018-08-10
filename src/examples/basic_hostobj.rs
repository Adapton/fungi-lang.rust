pub mod color {
    use std::any::Any;
    use std::rc::Rc;
    use ast;
    use hostobj;
    
    #[derive(Eq,PartialEq,Clone,Debug,Hash)]
    pub enum Color {
        Red, Green, Gold,
    }

    pub fn val_of_color(c:Color) -> ast::Val {
        hostobj::val_of_obj(c)
    }
    
    pub fn color_of_any (x:&Rc<Any>) -> Option<Color> {
        hostobj::obj_of_any(x)
    }    
}
   
/*
pub mod general {
    use std::any::Any;
    use std::fmt;
    use std::hash::Hash;
    use std::fmt::Debug;
    use std::fmt::Formatter;
    use std::rc::Rc;
    use ast;
    use ast::Val;
    use std::marker::PhantomData;
    
    pub struct Ops<X> {
        phantom:PhantomData<X>
    }
    
    pub fn val_of_obj<X:'static+Debug+Hash+Eq+PartialEq+Clone>(x:X) -> ast::Val {
        ast::Val::HostObj( ast::HostObj{
            ops: Rc::new(Ops::<X>{phantom:PhantomData}),
            any: Rc::new(x)
        })
    }

    pub fn obj_of_any<X:'static+Debug+Hash+Eq+PartialEq+Clone> (x:&Rc<Any>) -> Option<X> {
        let r : Result<Rc<X>, Rc<Any>> = (x.clone()).downcast::<X>();
        match r {
            Err(_) => None,
            Ok(rc) => Some((*rc).clone())
        }
    }

    pub fn obj_of_val<X:'static+Debug+Hash+Eq+PartialEq+Clone> (x:&Val) -> Option<X> {
        match x {
            &Val::HostObj(ref o) => obj_of_any::<X>( &o.any ),
            _ => None,
        }
    }
    
    impl<X:'static+Debug+Hash+Eq+PartialEq+Clone> ast::HostObjOps for Ops<X> {
        fn eq(&self, x:&Rc<Any>, y:&Rc<Any>) -> bool {
            match (obj_of_any::<X>(x), obj_of_any::<X>(y)) {
                (Some(c1), Some(c2)) => c1 == c2,
                _ => false,
            }
        }
        fn hash(&self, x:&Rc<Any>) -> u64 {
            match obj_of_any::<X>(x) {
                Some(_x) => 1, // TODO
                None    => 0,
            }
        }
        fn fmt(&self, f:&mut Formatter, x:&Rc<Any> ) -> fmt::Result {
            obj_of_any::<X>(x).unwrap().fmt(f)
        }
    }
}
*/
