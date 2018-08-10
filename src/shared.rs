//! a sharing serializes once, not once per reference (c.f. the `Rc` type).

use std::rc::Rc;
use std::fmt::{self,Debug};
use std::ops::Deref;
use serde::de::*;
use serde::ser::*;
use std::hash::{Hash,Hasher};
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::cell::RefCell;
use core::any::Any;

pub type Id = u64;

/// A shared instance of T that serializes once, not once per reference.
///
/// Unlike a "bare" Rc<T>, a Shared<T> enjoys the practical property
/// that, when a structure holding multiple (shared) instances of T is
/// serialized, this serialized output holds only _one_ occurrence of
/// a T's serialized representation; the other occurrences merely
/// consist of the T's unique identifier (the serialization of an
/// `Id`, single machine word on modern machines).
///
/// In particular, a shared T has a unique ID permitting table-based
/// indirection, via temporary storage used by serialization and
/// serialization logic; by contrast, a bare Rc<T> lacks this
/// indirection, and thus, it lacks a compact serialized
/// representation for structures with abundant sharing. Generally,
/// abundant sharing via many shared Rc<_>s leads to exponential "blow
/// up" in terms of serialized space and time.
///
#[derive(Clone)]
pub struct Shared<T> {
    ptr:SharedPtr<T>
}

#[derive(Serialize, Deserialize, Clone)]
enum SharedPtr<T> {
    /// Outside of serialized representations of a Shared<T>, the
    /// constructor Rc is the only valid inhabitant of this type.
    Rc(Id, Rc<T>),

    /// The Copy constructor only appears in the _serialized
    /// representations_ of a Shared<T> instance; it _never_ occurs in
    /// the deserialized, in-memory versions of this type.  We rely on
    /// this invariant to avoid keeping around a lookup table after
    /// deserialization, and to avoid doing table lookups for any
    /// deref of a SharedPtr<_>.
    Copy(Id),
}

impl<T:Hash+'static> Shared<T> {
    pub fn id(&self) -> Id {
        match self.ptr {
            SharedPtr::Rc(id, _) => id.clone(),
            SharedPtr::Copy(id)  => id.clone(),
        }
    }
    pub fn new(t:T) -> Shared<T> {
        let mut hasher = DefaultHasher::new();
        t.hash(&mut hasher);
        let id = hasher.finish();
        Shared{ptr:SharedPtr::Rc(id, Rc::new(t))}
    }
    pub fn from_rc(rc:Rc<T>) -> Shared<T> {
        let mut hasher = DefaultHasher::new();
        rc.hash(&mut hasher);
        let id = hasher.finish();
        Shared{ptr:SharedPtr::Rc(id, rc)}
    }
}

impl<T:PartialEq+'static> PartialEq for Shared<T> {
    fn eq(&self, other:&Self) -> bool {
        match (&self.ptr, &other.ptr) {
            (&SharedPtr::Rc(ref id1, ref rc1),
             &SharedPtr::Rc(ref id2, ref rc2)) => {
                if true {
                    // Shallow O(1) comparison, via unique IDs.  This
                    // is "sound" to the extent that hashing avoids
                    // collisions.  If you feel paranoid, follow the
                    // other implementation, which compares the
                    // content of the two Rc<_>s.
                    id1 == id2
                } else {
                    rc1 == rc2
                }
            },
            _ => unreachable!()
        }
    }
}
impl<T:PartialEq+'static> Eq for Shared<T> { }

impl<T:'static+Hash> Hash for Shared<T> {
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        // The Merkle-tree-like structure of a SharedPtr<T> avoids
        // "deep" hashing operations; instead, hashing merely
        // re-hashes the pre-computed (unique) Id of this deep
        // structure.
        self.id().hash(state)
    }
}

impl<T:Debug> fmt::Debug for Shared<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.ptr {
            SharedPtr::Rc(_, ref rc) => rc.fmt(f),
            SharedPtr::Copy(_) => unreachable!()
        }        
    }
}

/// We may deference a (deserialized) Shared<T> just like an Rc<T>;
/// below, rely on the invariant that all deserialized Shared<T>'s
/// consist of an Rc<T> (along with a unique ID).
impl<T> Deref for Shared<T> {
    type Target = T;
    fn deref(&self) -> &T {
        match self.ptr {
            SharedPtr::Rc(_, ref rc) => &*rc,
            SharedPtr::Copy(_) => unreachable!(),
        }
    }
}

impl<T:Serialize+Hash+'static> Serialize for Shared<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Check to see if self.id has already been serialized; if so,
        // do not serialize yet another copy; instead, serialize a
        // Copy<T> with the same ID.
        let orc : Option<Rc<T>> = table_get(&self.id());
        match (&self.ptr, orc) {
            (&SharedPtr::Copy(_), _) => unreachable!(),
            (&SharedPtr::Rc(ref id, ref rc), None) => {
                table_put(id.clone(), rc.clone());
                self.ptr.serialize(serializer)
            }
            (&SharedPtr::Rc(ref id, ref _rc1), Some(ref _rc2)) => {
                table_inc_copy_count();
                let ptr_copy:SharedPtr<T> = SharedPtr::Copy(id.clone());
                ptr_copy.serialize(serializer)
            }
        }
    }
}
impl<'de,T:Deserialize<'de>+Hash+'static> Deserialize<'de> for Shared<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        match SharedPtr::<T>::deserialize(deserializer) {
            Ok(SharedPtr::Copy(id)) => {
                match table_get(&id) {
                    None => unreachable!(),
                    Some(rc) => {
                        table_inc_copy_count();
                        Ok(Shared{ptr:SharedPtr::Rc(id, rc)})
                    }
                }
            }
            Ok(SharedPtr::Rc(id, rc)) => {
                table_put(id.clone(), rc.clone());
                Ok(Shared{ptr:SharedPtr::Rc(id, rc)})
            },
            Err(err) => Err(err),
        }
    }
}

/////////////////////////////////////////////////////////////////////////////////////

struct Table {
    copy_count:usize,
    table:HashMap<Id,Box<Rc<Any>>>
}

/// Global table of serialized objects; permits us to avoid multiple
/// serialized copies of a single, shared object.
thread_local!(static TABLE:
              RefCell<Table> =
              RefCell::new(Table{
                  copy_count:0,
                  table:HashMap::new()
              }));

/// Put a reference-counted object into the table of serialized objects
fn table_put<T:Any+'static>(id:Id, x:Rc<T>) {
    TABLE.with(|t| {
        drop(t.borrow_mut().table.insert(id, Box::new(x)))
    })
}

/// Increment the copy count associated with the table; used by
/// regression tests and other diagnostics.
fn table_inc_copy_count() {
    TABLE.with(|t| {
        t.borrow_mut().copy_count += 1;
    })    
}

/// Get a reference-counted object from the table of serialized objects
///
/// For documentation for rc_downcast feature, see this:
/// https://github.com/rust-lang/rust/blob/71d3dac4a86d192c2c80948621859da3b363fa50/src/liballoc/rc.rs#L621
///
fn table_get<T:'static>(id:&Id) -> Option<Rc<T>> {
    TABLE.with(|t| {
        match t.borrow().table.get(id) {
            Some(ref brc) => {
                let x : &Rc<Any> = &**brc;
                let y : Result<Rc<T>, Rc<Any>> = (x.clone()).downcast::<T>();
                match y {
                    Err(_) => {
                        panic!("downcast failed for id {:?}", id)
                    }
                    Ok(ref rc) => Some((*rc).clone())
                }
            }
            None => None,
        }
    })
}

/// Reclaim the space used to serialize large structures.  Returns the
/// "copy count" of the table.
///
/// We use this "copy count" for regression tests, to ensure that we
/// get the compactness that we expect in these tests.
///
/// This `clear` operation is essential for memory-sensitive programs
/// that dump their structures to external storage: when these
/// serialized structures are no longer needed by the Rust program,
/// their reference count will not drop to zero without first using
/// this operation.
///
pub fn clear() -> usize {
    let copy_count = 
        TABLE.with(|t| {
            let c = t.borrow().copy_count;
            t.borrow_mut().table.clear();
            t.borrow_mut().copy_count = 0;
            c
        });
    copy_count
}


//////////////////////////////////////////////////////////////////////////////

mod list_example {
    use super::Shared;
   
    #[derive(Hash,Clone,Debug,PartialEq,Eq,Serialize,Deserialize)]
    enum List {
        Nil,
        Cons(usize, Shared<List>)
    }
    
    fn nil() -> List {
        List::Nil
    }

    fn cons(h:usize, t:List) -> List {
        List::Cons(h, Shared::new(t))
    }

    #[allow(unused)]
    fn sum(l:&List) -> usize {
        match *l {
            List::Nil => 0,
            List::Cons(ref h, ref t) => {
                h + sum(&*t)
            }
        }
    }

    #[allow(unused)]
    fn from_vec(v:&Vec<usize>) -> List {
        let mut l = nil();
        for x in v.iter() {
            l = cons(*x, l);
        }
        return l
    }

    #[test]
    fn test_elim_forms() {
        let x = from_vec(&vec![1,2,3]);
        assert_eq!(1+2+3, sum(&x))
    }
    
    #[test]
    fn test_intro_forms() {
        let x = nil();
        let x = cons(1, x);
        let y = cons(2, x.clone());
        let z = cons(3, x.clone());
        drop((x,y,z))
    }

    #[test]
    fn test_serde() {
        use serde_json;
        let (value, expected_copy_count) = {
            let x = nil();
            let x = cons(1, x);
            let y = cons(2, x.clone());
            let z = cons(3, x.clone());
            ((x,y,z), 2)
        };
               
        let serialized = serde_json::to_string(&value).unwrap();
        let copy_count1 = super::clear();
            
        println!("serialized = {}", serialized);
        println!("copy_count1 = {}", copy_count1);        
        assert_eq!(copy_count1, expected_copy_count);
        
        let deserialized: (List,List,List) =
            serde_json::from_str(&serialized[..]).unwrap();
        let copy_count2 = super::clear();
        
        println!("copy_count2 = {}", copy_count2);
        assert_eq!(copy_count2, expected_copy_count);
        
        assert_eq!(deserialized, value);
    }
}
