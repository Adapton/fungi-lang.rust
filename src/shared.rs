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
pub struct Shared<T> {
    ptr:SharedPtr<T>
}

#[derive(Serialize, Deserialize)]
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
            Some(_) => panic!("expected at most one copy of each Shared object")
        }
    })
}

/// Get a reference-counted object from the table of serialized objects
fn table_get<T:'static>(id:&Id) -> Option<Rc<T>> {
    TABLE.with(|t| {
        match t.borrow().get(id) {
            Some(ref brc) => {
                let x  : Option<&Rc<T>> = brc.downcast_ref();
                let rc : Rc<T> = x.unwrap().clone();
                Some(rc)
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
pub fn clear<T:'static>() {
    TABLE.with(|t| { t.borrow_mut().clear() })
}
