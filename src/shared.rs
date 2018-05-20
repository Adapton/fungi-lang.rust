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
/// consist of the T's unique identifier (a single machine word).
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
    /// deserialization, and to avoid doing table lookups any deref of
    /// the shared pointer.
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
                if false {
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

/// Global table of serialized objects; permits us to avoid multiple
/// serialized copies of a single, shared object.
thread_local!(static TABLE:
              RefCell<HashMap<Id,Box<Rc<Any>>>> =
              RefCell::new(HashMap::new()));

/// Put a reference-counted object into the table of serialized objects
fn table_put<T:Any+'static>(id:Id, x:Rc<T>) {
    TABLE.with(|t| {
        match t.borrow_mut().insert(id, Box::new(x)) {
            None => (),
            Some(_) => ()
                //panic!("expected at most one copy of each Shared object")
        }
    })
}

/// Get a reference-counted object from the table of serialized objects
fn table_get<T:'static>(id:&Id) -> Option<Rc<T>> {
    TABLE.with(|t| {
        match t.borrow().get(id) {
            Some(ref brc) => {
                let orct : Option<&Rc<T>> = brc.downcast_ref();
                match orct {
                    None => None,
                    Some(ref rct) => Some((*rct).clone())
                }
            }
            None => None,
        }
    })
}

/// Reclaim the space used to serialize large structures
///
/// This operation is essential for memory-sensitive programs that
/// dump their structures to external storage: when these serialized
/// structures are no longer needed by the Rust program, their
/// reference count will not drop to zero without first using this
/// operation.
pub fn clear() {
    TABLE.with(|t| { t.borrow_mut().clear() })
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
    fn test_elim() {
        let x = from_vec(&vec![1,2,3]);
        assert_eq!(1+2+3, sum(&x))
    }
    
    #[test]
    fn test_intro() {
        let x = nil();
        let x = cons(1, x);
        let y = cons(2, x.clone());
        let z = cons(3, x.clone());
        drop((x,y,z))
    }

    #[test]
    fn test_serde() {
        use serde_json;
        let tuple = {
            let x = nil();
            let x = cons(1, x);
            let y = cons(2, x.clone());
            let z = cons(3, x.clone());
            (x,y,z)
        };
        
        let value = tuple.clone();
        
        let serialized = serde_json::to_string(&value).unwrap();
        super::clear();
            
        println!("{}", serialized);
        let deserialized: (List,List,List) =
            serde_json::from_str(&serialized[..]).unwrap();
        
        assert_eq!(deserialized, value);
        
        drop(tuple)
    }
}
