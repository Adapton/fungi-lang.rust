pub mod color {
    use std::any::Any;
    use std::fmt;
    use std::fmt::Formatter;
    use std::rc::Rc;
    use ast;
    
    #[derive(Eq,PartialEq,Clone,Debug,Hash)]
    pub enum Color {
        Red, Green, Gold,
    }
    
    pub struct Ops;
    
    pub fn val_of_color(c:Color) -> ast::Val {
        ast::Val::HostObj( ast::HostObj{
            ops: Rc::new( Ops{} ),
            any: Rc::new( c )
        })
    }
    
    pub fn color_of_any (x:&Rc<Any>) -> Option<Color> {
        let r : Result<Rc<Color>, Rc<Any>> = (x.clone()).downcast::<Color>();
        match r {
            Err(_) => None,
            Ok(rc) => Some((*rc).clone())
        }
    }
    
    impl ast::HostObjOps for Ops {
        fn eq(&self, x:&Rc<Any>, y:&Rc<Any>) -> bool {
            match (color_of_any(x), color_of_any(y)) {
                (Some(c1), Some(c2)) => c1 == c2,
                _ => false,
            }
        }
        fn hash(&self, x:&Rc<Any>) -> u64 {
            match color_of_any(x) {
                Some(Color::Red)   => 0,
                Some(Color::Green) => 1,
                Some(Color::Gold)  => 2,
                None               => 3,
            }
        }
        fn fmt(&self, f:&mut Formatter, x:&Rc<Any> ) -> fmt::Result {
            match color_of_any(x) {
                Some(Color::Red)   => write!(f, "red"),
                Some(Color::Green) => write!(f, "green"),
                Some(Color::Gold)  => write!(f, "gold"),
                None               => unreachable!(),
            }        
        }
    }
}
   

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
