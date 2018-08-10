//! Host-level (Rust-level) values as Fungi values

use std::any::Any;
use std::fmt;
use std::hash::Hash;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::rc::Rc;
use ast;
use ast::Val;
use dynamics::RtVal;
use std::marker::PhantomData;

/// zero-sized struct to implement the `ast::HostObjOps` trait
pub struct Ops<X> {
    phantom:PhantomData<X>
}

/// Inject a host-level object into a Fungi value.
pub fn val_of_obj<X:'static+Debug+Hash+Eq+PartialEq+Clone>(x:X) -> Val {
    Val::HostObj( ast::HostObj{
        ops: Rc::new(Ops::<X>{phantom:PhantomData}),
        any: Rc::new(x)
    })
}

/// Un-inject a host-level object from a Fungi value.
pub fn obj_of_val<X:'static+Debug+Hash+Eq+PartialEq+Clone> (x:&Val) -> Option<X> {
    match x {
        &Val::HostObj(ref o) => obj_of_any::<X>( &o.any ),
        _ => None,
    }
}

/// Inject a host-level object into a Fungi runtime value.
pub fn rtval_of_obj<X:'static+Debug+Hash+Eq+PartialEq+Clone>(x:X) -> RtVal {
    RtVal::HostObj( ast::HostObj{
        ops: Rc::new(Ops::<X>{phantom:PhantomData}),
        any: Rc::new(x)
    })
}

/// Un-inject a host-level object from a Fungi runtime value.
pub fn obj_of_rtval<X:'static+Debug+Hash+Eq+PartialEq+Clone> (x:&RtVal) -> Option<X> {
    match x {
        &RtVal::HostObj(ref o) => obj_of_any::<X>( &o.any ),
        _ => None,
    }
}

/// Un-inject a host-level object from a Rust 'Rc<Any>' reference.
pub fn obj_of_any<X:'static+Debug+Hash+Eq+PartialEq+Clone> (x:&Rc<Any>) -> Option<X> {
    let r : Result<Rc<X>, Rc<Any>> = (x.clone()).downcast::<X>();
    match r {
        Err(_) => None,
        Ok(rc) => Some((*rc).clone())
    }
}

/// Use the `PartialEq`, `Hash` and `Debug` implementations of the type `X`.
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
