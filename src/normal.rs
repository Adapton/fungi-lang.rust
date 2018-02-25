/*! Static (typing-time) term reduction/normalization. */

use std::fmt;
use std::rc::Rc;

use ast::*;

use subst;   
use bitype::{Ctx,Term};

/// XXX
/// Normalize name terms (expand definitions and reduce applications).
pub fn normal_nmtm(ctx:&Ctx, n:&NameTm) -> NameTm {
    /// XXX/TODO
    return n.clone()
}


/// Normalize index terms, by expanding definitions and reducing
/// function applications where possible.
///
///
/// # Example:
///
/// ```text
/// // Unknowns:
/// idxtm X : NmSet 
/// idxtm Y : NmSet
/// nmtm  z : Nm
/// 
/// idxtm bin     : Nm -> NmSet = (#x:Nm. {x * @1} % {x * @2})
/// idxtm set     : NmSet       = (({@3}%Y)%(X%{z}))
/// idxtm example : NmSet       = (bin) set
/// ```
///
/// The `example` term normalizes to the following term
///
/// ```text
/// {@3*@1} % {@3*@2} 
///   % (
///   ((#x:Nm. {x * @1} % {x * @2}) (X))
///   % (
///   {z*@1} % {z*@2}
///   %  (
///   ((#x:Nm. {x * @1} % {x * @2}) (Y))
///   %
///   0 )))
///  : NmSet
/// ```
/// 
/// Notice that the nested binary tree of disjoint unions (`%`) is
/// flattened into a list, where disjoint union (`%`) plays the rule
/// of `Cons`, and where empty set (`0`) plays the role of `Nil`.
///
/// Further, the flat-mapped function (`bin`) has been applied to the
/// set structure:
///
/// 1. The mapping function has been applied to the singleton sets of
/// name constant `@3` and name variable `z`, respectively.
///
/// 2. Meanwhile, as the set variables `X` and `Y` stand for unknown
/// _sets_ of names, the flat map is not reduced over these (unknown)
/// sets, but only distributed across the disjoint union (`%`) that
/// connects them.
///
/// ??? -- Do we need to implement symbolic set subtraction over this
/// final normalized structure ???  (It seems that's what we need to
/// implement the effect-checking logic of the `let` checking rule.)
///
pub fn normal_idxtm(ctx:&Ctx, i:&IdxTm) -> IdxTm {
    /// XXX/TODO
    return i.clone()
}


/// Normalize types (expand definitions and reduce applications).
///
/// To normalize types, we generally need to **expand definitions** of
/// user-defined types, and **apply them** to type or index arguments.
///
/// ### Example:
///
/// Suppose the user defines `NmOp := foralli X:NmSet. 1 + Nm[X]` in
/// the context.  Then, `NmOp [{@1}]` normalizes to `1 + Nm[{@1}]`, by
/// using the body of the definition of `NmOp`, and reducing the
/// type-index application.
///
/// ### Reducible forms (not head normal form)
///
/// The following type forms are **reducible**:
///
///   1. `user(_)` / `Ident(_)`   -- user-defined identifiers (each reduces to its definition)
///   2. `(foralli a:g. A) [i]`   -- type-index application
///   3. `(forallt a:K. A) B`     -- type-type application
///
/// ### Normal forms (irreducible forms)
///
/// The following forms are "normal" (irreducible); they each have
/// intro/elim forms in the core language's program syntax:
///
///  1. Base types, sums, products
///  3. `Ref`, `Thk`, `Nm`, `(Nm->Nm)[_]`,
///  4. `exists`
///  5. `forallt`, `foralli`
///  6. `rec`
///  7. type variables, as introduced by `forallt` and `rec` (note: not the same as user-defined type names, which each have a known definition)
///  8. type applications in head normal form.
/// 
pub fn normal_type(ctx:&Ctx, typ:&Type) -> Type {
    match typ {
        // normal forms:
        &Type::Unit         |
        &Type::Var(_)       |
        &Type::Sum(_, _)    |
        &Type::Prod(_, _)   |
        &Type::Thk(_, _)    |
        &Type::Ref(_, _)    |
        &Type::Rec(_, _)    |
        &Type::Nm(_)        |
        &Type::NmFn(_)      |
        &Type::TypeFn(_,_,_)|
        &Type::IdxFn(_,_,_) |
        &Type::NoParse(_)   |
        &Type::Exists(_,_,_,_)
            =>
            typ.clone(),

        &Type::Ident(ref ident) => { match ident.as_str() {
            // Built-in primitives are normal; they lack a definition in the context:
            "Nat" | "Bool" | "String"
                => { typ.clone() }
            
            // all other identifiers are for defined types; look up the definition
            _ => { match ctx.lookup_type_def(ident) {
                Some(a) => normal_type(ctx, &a),
                _ => {
                    println!("undefined type: {} in\n{:?}", ident, ctx);
                    // Give up:
                    typ.clone()
                }
            }}
        }}
        &Type::TypeApp(ref a, ref b) => {
            let a = normal_type(ctx, a);
            let a = match a {
                Type::Rec(_,_) => unroll_type(&a),
                _ => a,
            };
            let b = normal_type(ctx, b);
            match a {
                Type::TypeFn(ref x, ref _k, ref body) => {
                    let body = subst::subst_type_type(b,x,(**body).clone());
                    normal_type(ctx, &body)
                },
                a => {
                    panic!("sort error: expected TypeFn, not {:?}", a);
                    typ.clone()
                }
            }
        }
        &Type::IdxApp(ref a, ref i) => {
            let a = normal_type(ctx, a);
            let a = match a {
                Type::Rec(_,_) => unroll_type(&a),
                _ => a,
            };
            match a {
                Type::IdxFn(ref x, ref _g, ref body) => {
                    let body = subst::subst_idxtm_type(i.clone(),x,(**body).clone());
                    normal_type(ctx, &body)
                },
                a => {
                    panic!("sort error: expected TypeFn, not {:?}", a);
                    typ.clone()
                }
            }
        }
    }
}

/*

Not head normal:
(#a. (#b. b) 3) 4
-->
(#a. 3) 4
-->
3 4
-/->

Not in normal form: (#b.b) 3) --> 3
(#x. ((#b.b) 3))

Is head normal (with lambda as outside thing)
(#x. ((#b.b) 3))

Head normal (with application as outside thing)
x 1 2 3
^
| variable here

*/


/// Unroll a `rec` type, exposing its recursive body's type structure.
///
/// ### Example 1:  
///
/// `unroll_type(rec a. 1 + a)`  
///  = `1 + (rec a. 1 + (rec a. 1 + a))`
///
/// ### Example 2:
///
/// `unroll_type(rec a. (+ 1 + a + (x a x a)))`  
///  = `(+ 1`  
///      `+ (rec a. 1 + a + (x a x a))`  
///      `+ (x (rec a. 1 + a + (x a x a)) x (rec a. 1 + a + (x a x a)))`  
///     `)`  
///
///
pub fn unroll_type(typ:&Type) -> Type {
    match typ {
        // case: rec x.A =>
        &Type::Rec(ref x, ref a) => {
            // [(rec x.A)/x]A
            subst::subst_type_type(typ.clone(), x, (**a).clone())
        }
        // error
        _ => {
            //println!("error: not a recursive type; did not unroll it: {:?}", typ);
            typ.clone()
        }
    }
}
