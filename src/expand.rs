/*! Expand static definitions (`Ident` cases of types, indices and effects). */

//use std::fmt;
use std::rc::Rc;

use normal;
use ast::*;
use bitype::*;

// TODO-Someday: Use Rc-based lists instead vectors to represent the
// bound variable lisctx, for cheaper O(1) clones.

pub fn expand_ctype(ctx:&Ctx, ct:CType) -> CType {
    match ct {
        CType::Lift(a) => {
            CType::Lift(expand_type(ctx,a))
        }
        CType::Arrow(a, ce) => {
            CType::Arrow(expand_type(ctx,a),
                         expand_ceffect_rec(ctx,ce))
        }
        CType::NoParse(s) => CType::NoParse(s)
    }
}

pub fn expand_effect_rec(ctx:&Ctx, eff:Rc<Effect>) -> Rc<Effect> {
    Rc::new(expand_effect(ctx, (*eff).clone()))
}

pub fn expand_effect(ctx:&Ctx, eff:Effect) -> Effect {
    match eff {
        Effect::WR(i, j) => {
            Effect::WR(expand_idxtm(ctx, i),
                       expand_idxtm(ctx, j))
        },
        Effect::NoParse(s) => Effect::NoParse(s)
    }
}

pub fn expand_ceffect_rec(ctx:&Ctx, ce:Rc<CEffect>) -> Rc<CEffect> {
    Rc::new(expand_ceffect(ctx, (*ce).clone()))
}

pub fn expand_ceffect(ctx:&Ctx, ce:CEffect) -> CEffect {
    match ce {
        CEffect::Cons(ct, eff) => {
            CEffect::Cons(expand_ctype(ctx, ct),
                          expand_effect(ctx, eff))
        }
        CEffect::ForallType(y, k, ce) => {
            CEffect::ForallType(y, k, expand_ceffect_rec(ctx, ce))
        }
        CEffect::ForallIdx(y, g, p, ce) => {
            CEffect::ForallIdx(y, g,
                               expand_prop(ctx, p),
                               expand_ceffect_rec(ctx, ce))
        }
        CEffect::NoParse(s) => CEffect::NoParse(s)
    }
}

pub fn expand_type_rec(ctx:&Ctx, a:Rc<Type>) -> Rc<Type> {
    Rc::new(expand_type(ctx, (*a).clone()))
}

pub fn expand_type(ctx:&Ctx, a:Type) -> Type {
    match a {
        Type::Unit => Type::Unit,
        Type::Ident(ident) => {
            Type::Ident(ident.clone())
        }
        // match ident.as_str() {
        //     // Built-in primitives are normal; they lack a definition in the context:
        //     "Nat" | "Bool" | "String"
        //         => { Type::Ident(ident).clone() }
        //     // all other identifiers are for defined types; look up the definition
        //     _ => { match ctx.lookup_type_def(&ident) {
        //         Some(a) => {
        //             // If the definition is itself an identifier, it's a user type label -- Hack! XXX
        //             if let Type::Ident(_) = a { a.clone() }
        //             else { expand_type(ctx, a) }
        //         },
        //         _ => {
        //             println!("undefined type: {} in\n{:?}", ident, ctx);
        //             // Give up:
        //             Type::Ident(ident.clone())
        //         }
        //     }}
        // }
        // }
        Type::Var(y) => Type::Var(y),
        Type::Sum(a1, a2) => {
            Type::Sum(
                expand_type_rec(ctx, a1),
                expand_type_rec(ctx, a2),
            )
        }
        Type::Prod(a1, a2) => {
            Type::Prod(
                expand_type_rec(ctx, a1),
                expand_type_rec(ctx, a2),
            )
        }
        Type::Ref(i, a0) => {
            Type::Ref(
                expand_idxtm(ctx, i),
                expand_type_rec(ctx, a0),
            )
        }
        Type::Thk(i, ce) => {
            Type::Thk(
                expand_idxtm(ctx, i),
                expand_ceffect_rec(ctx, ce),
            )
        }        
        Type::IdxApp(a0, i) => {
            Type::IdxApp(
                expand_type_rec(ctx, a0),
                expand_idxtm(ctx, i)
            )
        }
        Type::TypeApp(a1, a2) => {
            Type::TypeApp(
                expand_type_rec(ctx, a1),
                expand_type_rec(ctx, a2)
            )
        }
        Type::Nm(i) => {
            Type::Nm(expand_idxtm(ctx, i))
        }
        Type::NmFn(n) => {
            Type::NmFn(expand_nmtm(ctx, n))
        }
        Type::Rec(y, a1) => {
            Type::Rec(y, expand_type_rec(ctx, a1))
        }
        Type::TypeFn(y, k, a1) => {
            Type::TypeFn(y, k, expand_type_rec(ctx, a1))
        }
        Type::IdxFn(y, g, a1) => {
            Type::IdxFn(y, g, expand_type_rec(ctx, a1))
        }
        Type::Exists(y, g, p, a1) => {
            Type::Exists(
                y, g,
                expand_prop(ctx, p),
                expand_type_rec(ctx, a1),
            )
        }
        Type::NoParse(s) => Type::NoParse(s)
    }
}

/// Substitute terms into propositions
pub fn expand_prop(ctx:&Ctx, p:Prop) -> Prop {
    match p {
        Prop::Tt => Prop::Tt,
        Prop::Equiv(i, j, g) => {
            Prop::Equiv(
                expand_idxtm(ctx, i),
                expand_idxtm(ctx, j),
                g)
        },
        Prop::Apart(i, j, g) => {
            Prop::Apart(
                expand_idxtm(ctx, i),
                expand_idxtm(ctx, j),
                g)
        },
        Prop::Conj(p1, p2) => {
            Prop::Conj(
                expand_prop_rec(ctx, p1),
                expand_prop_rec(ctx, p2),
            )
        }
        Prop::NoParse(s) => Prop::NoParse(s)
    }
}

/// Substitute terms into propositions
pub fn expand_prop_rec(ctx:&Ctx, p:Rc<Prop>) -> Rc<Prop> {
    Rc::new(expand_prop(ctx,(*p).clone()))
}

/// Substitute terms into index terms
pub fn expand_idxtm_rec(ctx:&Ctx, i:Rc<IdxTm>) -> Rc<IdxTm> {
    Rc::new(expand_idxtm(ctx, (*i).clone()))
}

/// Substitute terms into index terms
pub fn expand_idxtm(ctx:&Ctx, i:IdxTm) -> IdxTm {
    match i {
        // Variables and identifiers are lexically distinct
        IdxTm::Ident(y) => {
            match ctx.lookup_idxtm_def(&y) {
                Some(i) => expand_idxtm(ctx, i),
                _ => {
                    println!("undefined idxtm: {} in\n{:?}", y, ctx);
                    // Give up:
                    IdxTm::Ident(y)
                }
            }
        }
        IdxTm::WriteScope => {
            IdxTm::WriteScope
        },
        IdxTm::Var(y) => {
            IdxTm::Var(y)
        }
        IdxTm::Sing(n) => {
            IdxTm::Sing(expand_nmtm(ctx,n))
        },
        IdxTm::Unit  => IdxTm::Unit,
        IdxTm::Empty => IdxTm::Empty,
        IdxTm::NmSet(s) => {
            let mut terms = vec![];
            for tm in s.terms {
                let tm = match tm {
                    normal::NmSetTm::Single(n) => {
                        normal::NmSetTm::Single(expand_nmtm(ctx,n))
                    },
                    normal::NmSetTm::Subset(i) => {
                        normal::NmSetTm::Subset(expand_idxtm(ctx,i))
                    }
                };
                terms.push(tm)
            }
            IdxTm::NmSet(normal::NmSet{cons:s.cons, terms:terms})
        }
        IdxTm::Apart(i, j) => {
            IdxTm::Apart(expand_idxtm_rec(ctx,i),
                         expand_idxtm_rec(ctx,j))
        }
        IdxTm::Union(i, j) => {
            IdxTm::Union(expand_idxtm_rec(ctx,i),
                         expand_idxtm_rec(ctx,j))
        }
        IdxTm::Bin(i, j) => {
            IdxTm::Bin(expand_idxtm_rec(ctx,i),
                       expand_idxtm_rec(ctx,j))
        }
        IdxTm::Pair(i, j) => {
            IdxTm::Pair(expand_idxtm_rec(ctx,i),
                        expand_idxtm_rec(ctx,j))
        }
        IdxTm::Proj1(i) => {
            IdxTm::Proj1(expand_idxtm_rec(ctx,i))
        }
        IdxTm::Proj2(i) => {
            IdxTm::Proj2(expand_idxtm_rec(ctx,i))
        }
        IdxTm::Lam(y,g,i) => {
            IdxTm::Lam(y,g,expand_idxtm_rec(ctx,i))
        }
        IdxTm::App(i, j) => {
            IdxTm::App(expand_idxtm_rec(ctx, i),
                       expand_idxtm_rec(ctx, j))
        }
        IdxTm::Map(n, j) => {
            IdxTm::Map(expand_nmtm_rec(ctx, n),
                       expand_idxtm_rec(ctx, j))
        }
        IdxTm::MapStar(n, j) => {
            IdxTm::MapStar(expand_nmtm_rec(ctx, n),
                           expand_idxtm_rec(ctx, j))
        }
        IdxTm::FlatMap(i, j) => {
            IdxTm::FlatMap(expand_idxtm_rec(ctx, i),
                           expand_idxtm_rec(ctx, j))
        }
        IdxTm::FlatMapStar(i, j) => {
            IdxTm::FlatMapStar(expand_idxtm_rec(ctx, i),
                               expand_idxtm_rec(ctx, j))
        }
        IdxTm::NoParse(s) => IdxTm::NoParse(s)
    }
}

/// Substitute terms into name terms
pub fn expand_nmtm_rec(ctx:&Ctx, m:Rc<NameTm>) -> Rc<NameTm> {
    Rc::new(expand_nmtm(ctx,(*m).clone()))
}


/// Substitute name terms into name terms
pub fn expand_nmtm(ctx:&Ctx, m:NameTm) -> NameTm {
    match m {
        NameTm::ValVar(y) => NameTm::ValVar(y),
        NameTm::Ident(x) => {
            match ctx.lookup_nmtm_def(&x) {
                Some(a) => {
                    expand_nmtm(ctx, a)
                },
                _ => {
                    println!("undefined name term: {} in\n{:?}", x, ctx);
                    // Give up:
                    NameTm::Ident(x.clone())
                }
            }}
        NameTm::Var(y) => NameTm::Var(y),
        NameTm::WriteScope => NameTm::WriteScope,
        NameTm::NoParse(s) => NameTm::NoParse(s),
        NameTm::Name(n) => NameTm::Name(n),
        NameTm::App(n1, n2) => {
            NameTm::App(
                expand_nmtm_rec(ctx, n1),
                expand_nmtm_rec(ctx, n2),
            )                
        }
        NameTm::Bin(n1, n2) => {
            NameTm::Bin(
                expand_nmtm_rec(ctx, n1),
                expand_nmtm_rec(ctx, n2),
            )                
        }
        NameTm::Lam(y,yg,m1) => {
            NameTm::Lam(y,yg,
                        expand_nmtm_rec(ctx,m1))
        }
    }
}
