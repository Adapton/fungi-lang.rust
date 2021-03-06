/*! Static (typing-time) term reduction/normalization. */

//use std::fmt;
use std::rc::Rc;
use crate::{ast::*, bitype, bitype::{Ctx,Term}, subst};

macro_rules! fgi_db_normal {
    ( $fmt_string:expr ) => {{
        //fgi_db!( $fmt_string )
    }};
    ( $fmt_string:expr, $( $arg:expr ),* ) => {{
        //fgi_db!( $fmt_string, $( $arg ),* )
    }}
}

/// Name set term. Representation for "apart/union-normal" name set terms.
///
/// A _name set term_ is either a singleton name term `M`, or a
/// (disjoint) subset of the full set, represented by an index term
/// `i`.  The purpose of this form is to expose the union/apart
/// connectives as forming a list/vector of subsets, over which we can
/// distribute set-level functions.
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize,PartialOrd,Ord)]
pub enum NmSetTm {
    /// singleton name term `M`
    Single(NameTm),
    /// subset of the full set, represented by an index term `i`
    Subset(IdxTm),
}
pub type NmSetTms = Vec<NmSetTm>;

/// Name set constructor; the subsets of a `NmSet` are (uniformly) combined as "apart" or "union"
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize,PartialOrd,Ord)]
pub enum NmSetCons {
    Union,
    Apart,
}
/// Canonical form (normal form) for a name set
#[derive(Clone,Debug,Eq,PartialEq,Hash,Serialize,PartialOrd,Ord)]
pub struct NmSet {
    /// None means that the term list is a singleton or empty; for sets with two or more sub-terms, this constructor gives the (uniform) way the terms are connected.
    pub cons: Option<NmSetCons>,
    /// terms connected via the given constructor, if any
    pub terms: Vec<NmSetTm>
}


// Combine two nmset constructors (as options).
pub fn nmset_cons_join(c1:Option<NmSetCons>, 
                       c2:Option<NmSetCons>) -> Option<NmSetCons> {
    match (c1, c2) {
        (None, None)     => None,
        (Some(c), None)  => Some(c),
        (None, Some(c))  => Some(c),
        (Some(NmSetCons::Union),_) => Some(NmSetCons::Union),
        (_,Some(NmSetCons::Union)) => Some(NmSetCons::Union),
        (Some(NmSetCons::Apart),
         Some(NmSetCons::Apart)) => Some(NmSetCons::Apart),
    }
}

// Add the given tm to the name set terms
fn nmset_terms_add(cons:Option<NmSetCons>, terms:&mut Vec<NmSetTm>, tm:NmSetTm) {
    match tm {        
        NmSetTm::Subset(i) => {
            match i {
                IdxTm::NmSet(mut ns) => {
                    assert_eq!(cons, ns.cons);
                    terms.append(&mut ns.terms)
                }
                i => {
                    terms.push(NmSetTm::Subset(i))
                }
            }
        }
        tm => {
            terms.push(tm)
        }
    }
}

/// True when the name term is normal
pub fn is_normal_nmtm(_ctx:&Ctx, n:&NameTm) -> bool {
    match *n {
        //
        // Forms that are normal; no reduction rules apply
        //
        NameTm::Var(_)     |
        NameTm::ValVar(_)  |
        NameTm::Name(_)    |
        NameTm::Lam(_,_,_) => true,
        NameTm::WriteScope => true,        
        //
        // Forms that are not normal (there are reduction rules)
        //
        NameTm::Bin(_,_)   |
        NameTm::App(_,_)  => false,
        NameTm::Ident(_)   => false,
        //
        // Other forms that we dont really need to consider:
        //
        NameTm::NoParse(_) => false,
    }
}

/// True when the index term is normal
pub fn is_normal_idxtm(ctx:&Ctx, i:&IdxTm) -> bool {
    match *i {
        // identifiers are not normal
        IdxTm::Unknown    => true,
        IdxTm::Ident(_)   => false,
        IdxTm::NmTm(ref n) => is_normal_nmtm(ctx, n),
        // namesets are *locally* normal, by the way we construct
        // them; they are not *globally* normal, however: in some
        // (later) contexts, we get extra facts about a variable's
        // decomposition. E.g, suppose that in some arm of a case, we
        // do an unpack and get that X=(X1%X2).  Now any NmSet that
        // mentions X is _not normal_.
        IdxTm::NmSet(_)   => false,
        // variables are normal if there are no decompositions in the context
        IdxTm::Var(ref x) => {
            None == bitype::find_defs_for_idxtm_var(&ctx, &x)
        }        
        // unit has no reduction rule; ditto for functions
        IdxTm::Unit       => true,
        IdxTm::WriteScope => true,
        IdxTm::Lam(_,_,_) => true,
        // Pairs are normal if their sub-terms are normal
        IdxTm::Pair(ref i, ref j) => { is_normal_idxtm(ctx, i) && is_normal_idxtm(ctx, j) }
        // projections are not normal
        IdxTm::Proj1(_) => false,
        IdxTm::Proj2(_) => false,
        // these name set forms are not normal; we have a special
        // (normal) form for (apart) name sub-sets
        IdxTm::Empty | 
        IdxTm::Sing(_) |
        IdxTm::Apart(_, _) |
        // Function application forms are not normal
        IdxTm::App(_, _) |
        IdxTm::Union(_, _) |
        IdxTm::Bin(_, _) |
        IdxTm::Map(_, _) |
        IdxTm::MapStar(_, _) |
        IdxTm::FlatMap(_, _) |
        IdxTm::FlatMapStar(_, _) |
        IdxTm::NoParse(_) => false
    }
}

/// Compute normal form for index term
pub fn normal_idxtm_rec(ctx:&Ctx, i:Rc<IdxTm>) -> Rc<IdxTm> {
    //fgi_db!("BEGIN: normal_idxtm_rec({}) = ?", i);
    let r = Rc::new(normal_idxtm(ctx, (*i).clone()));
    //fgi_db!("END:   normal_idxtm_rec({}) = {}", i, r);
    r
}


/// Normalize index terms, by expanding definitions and reducing
/// function applications where possible.
///
///
/// ## Example 1:
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
///   NORM[ (#x:Nm. {x * @1} % {x * @2}) (X) ]
///   % (
///   {z*@1} % {z*@2}
///   %  (
///   NORM[ (#x:Nm. {x * @1} % {x * @2}) (Y) ]
///   %
///   0 )))
///  : NmSet
/// ```
///
/**

Where the index-level flat-map terms (in each `NORM[ ... ]`) normalize
further, converting into name-level maps, as follows:

```text
NORM[ (#x:Nm. {x * @1} % {x * @2}) (X) ]
==
[ #x:Nm. x * @1 ](X) % [ #x:Nm. x * @2 ](X)
```

*/
/**

## Example 2:

The following index term:

```text
(#x:Nm. {x, @1} % {x, @2}) ({@3}%Y)%(X%{z})
```

Normalizes to the following:

```text
{@3 * @1}
   % (
       {@3 * @2}
       % (
           ((#x:Nm. {x,@1}) Y)
               %  (
                   ((#x:Nm. {x,@2}) Y)
                       % (
                           ((#x:Nm. {x,@1}) (X))
                               % (
                                   ((#x:Nm. {x,@2}) (X))
                                       % (
                                           {z,@1} % {z,@2}
                                           %                                        
                                               0 ))))))
```

Notice that the nested binary tree of disjoint unions (`%`) is
flattened into a list, where disjoint union (`%`) plays the rule
of `Cons`, and where empty set (`0`) plays the role of `Nil`.

Further, the flat-mapped function (`bin`) has been applied to the
set structure:

1. The mapping function has been applied to the singleton sets of
   name constant `@3` and name variable `z`, respectively.

2. Meanwhile, as the set variables `X` and `Y` stand for unknown
   _sets_ of names, the flat map is not reduced over these (unknown)
   sets, but only distributed across the disjoint union (`%`) that
   connects them.

3. Finally, the flat-map term `(#x:Nm. {x * @1} % {x * @2}) (X)`
   normalizes into two mapping terms, one for each singleton set of
   the flat-map function's body.

*/
pub fn normal_idxtm(ctx:&Ctx, i:IdxTm) -> IdxTm {
    if is_normal_idxtm(ctx, &i) {
        return i
    } else {
        match i {
            IdxTm::Empty => {
                IdxTm::NmSet(NmSet{cons:None, terms:vec![]})
            }
            IdxTm::Var(ref x) => {
                let xdef = bitype::find_defs_for_idxtm_var(&ctx, x);
                normal_idxtm(ctx, xdef.unwrap())
            }
            IdxTm::Sing(n) => {
                let n = normal_nmtm(ctx, n);
                IdxTm::NmSet(NmSet{cons:None, terms:vec![
                    NmSetTm::Single( n )                        
                ]})
            }
            IdxTm::NmTm(n) => {
                IdxTm::NmTm(normal_nmtm(ctx, n))
            }

            IdxTm::Ident(ref ident) => {
                match ctx.lookup_idxtm_def(ident) {
                    Some(i) => normal_idxtm(ctx, i),
                    _ => {
                        fgi_db!("undefined idxtm: {} in\n{}", ident, ctx);
                        // Give up:
                        i.clone()
                    }
                }
            }

            IdxTm::NmSet(ns) => {
                let mut terms = vec![];
                let mut cons = ns.cons.clone();
                for t in ns.terms.iter() {
                    match t {
                        &NmSetTm::Single(ref n) => {
                            let tm = normal_nmtm(ctx, n.clone());
                            nmset_terms_add(cons.clone(), &mut terms, NmSetTm::Single(tm))
                        }
                        &NmSetTm::Subset(ref i) => {
                            let i2 = normal_idxtm(ctx, i.clone());
                            match i2 {
                                // Flatten any nested NmSet term vectors into the present one
                                IdxTm::NmSet(ns2) => {
                                    cons = nmset_cons_join(cons.clone(), ns2.cons.clone());
                                    for tm2 in ns2.terms {
                                        nmset_terms_add(cons.clone(), 
                                                        &mut terms, 
                                                        tm2.clone())
                                    }
                                },
                                i => {
                                    nmset_terms_add(cons.clone(),
                                                    &mut terms, 
                                                    NmSetTm::Subset(i));
                                }
                            }
                        }
                    }
                }                
                IdxTm::NmSet(NmSet{
                    cons:ns.cons.clone(),
                    terms:terms,
                })
            }

            IdxTm::Apart(i1, i2) => {
                let i1 = normal_idxtm_rec(ctx, i1);
                let i2 = normal_idxtm_rec(ctx, i2);
                match ((*i1).clone(), (*i2).clone()) {
                    // Case: Two name set terms lists.  Append them.
                    (IdxTm::NmSet(ns1),
                     IdxTm::NmSet(ns2)) => {
                        match (ns1.cons, ns2.cons) {
                            (None, None) |
                            (None, Some(NmSetCons::Apart)) |
                            (Some(NmSetCons::Apart), None) |
                            (Some(NmSetCons::Apart), Some(NmSetCons::Apart)) => {
                                let mut terms1 = ns1.terms;
                                let mut terms2 = ns2.terms;
                                terms1.append(&mut terms2);
                                IdxTm::NmSet(NmSet{
                                    cons:Some(NmSetCons::Apart),
                                    terms:terms1
                                })
                            },
                            _ => IdxTm::Apart(i1, i2) 
                        }}
                    // Case: Either LHS or RHS has a name set term
                    // list.  Push the non-name-set term onto the
                    // name-set term list:
                    (i, IdxTm::NmSet(mut ns))  |
                    (IdxTm::NmSet(mut ns), i) => {
                        nmset_terms_add(ns.cons.clone(), &mut ns.terms, NmSetTm::Subset(i));
                        IdxTm::NmSet(ns)
                    }
                    // Case: no existing `NmSet` term ==> No other way
                    // to combine these subsets' representations (),
                    // so introduce a new `NmSet` term, with two entries:
                    _ => {
                        IdxTm::NmSet(NmSet{
                            cons:Some(NmSetCons::Apart),
                            terms:vec![NmSetTm::Subset((*i1).clone()),
                                       NmSetTm::Subset((*i2).clone())],
                        })
                    }
                }
            }

            // XXX -- add cases that are analygous to Apart cases above
            IdxTm::Union(i1, i2) => {
                let i1 = normal_idxtm_rec(ctx, i1);
                let i2 = normal_idxtm_rec(ctx, i2);
                match ((*i1).clone(), (*i2).clone()) {
                    (IdxTm::NmSet(ns1),
                     IdxTm::NmSet(ns2)) => {
                        // if the ns is Union-based, it's fine to
                        // combine; if Apart-based, it's still fine
                        // (sound), though we loose some information
                        // in the process of doing so:
                        /*
                        match (ns1.cons, ns2.cons) {
                            (None, None) |
                            (None, Some(NmSetCons::Union)) |
                            (Some(NmSetCons::Union), None) |
                            (Some(NmSetCons::Union), Some(NmSetCons::Union)) => {
                         */
                        let mut terms1 = ns1.terms;
                        let mut terms2 = ns2.terms;
                        terms1.append(&mut terms2);
                        IdxTm::NmSet(NmSet{
                            cons:Some(NmSetCons::Union),
                            terms:terms1
                        })
                    }                
                    // Case: Either LHS or RHS has a name set term
                    // list.  Push the non-name-set term onto the
                    // name-set term list:
                    (i, IdxTm::NmSet(mut ns))  |
                    (IdxTm::NmSet(mut ns), i) => {
                        nmset_terms_add(ns.cons.clone(), &mut ns.terms, NmSetTm::Subset(i));
                        IdxTm::NmSet(ns)
                    }
                    // Case: no existing `NmSet` term ==> No other way
                    // to combine these subsets' representations (),
                    // so introduce a new `NmSet` term, with two entries:
                    _ => {
                        IdxTm::NmSet(NmSet{
                            cons:Some(NmSetCons::Union),
                            terms:vec![NmSetTm::Subset((*i1).clone()),
                                       NmSetTm::Subset((*i2).clone())],
                        })
                    }
                }
            }            

            // Case: Name-set-level binary composition:
            //
            // Make normal by attempting to convert this structure
            // (and its sub-terms) to name-term-level binary
            // composition:
            //
            //  { n } * { m } == { n * m }
            //
            //  i * { m } == FlatMap(#x:Nm.x * m, i)
            //
            //  { n } * j == FlatMap(#y:Nm.n * y, j)
            //
            //  (X1 % X2) * j == (X1 * j) % (X2 * j)
            //
            //  i * (Y1 % Y2) == (i * Y1) % (i * Y2)
            //
            IdxTm::Bin(i1, i2) => {
                use self::NmSetTm::*;
                let i1 = normal_idxtm_rec(ctx, i1);
                let i2 = normal_idxtm_rec(ctx, i2);
                
                fn bin_tm (ctx:&Ctx, tm1:NmSetTm, tm2:NmSetTm) -> NmSetTm { match (tm1, tm2) {
                    //  { m } * { n } == { m * n }
                    (Single(n), Single(m)) => {
                        Single(normal_nmtm(
                            ctx, NameTm::Bin(Rc::new(n), Rc::new(m))
                        ))
                    },
                    //  i * { m } == Map(#x:Nm.x * m, i)
                    (Subset(i), Single(m)) => {
                        Subset( normal_idxtm(
                            ctx, fgi_index!{
                                [ #x:Nm. x * (^m) ] ^i
                            }
                        ))
                    },
                    //  { n } * j == Map(#y:Nm.n * y, j)
                    (Single(n), Subset(j)) => {
                        Subset(normal_idxtm(
                            ctx, fgi_index!{
                                [ #x:Nm. (^n) * x ] ^j
                            }
                        ))
                    },
                    //  (X1 % X2) * j == (X1 * j) % (X2 * j)
                    (Subset(IdxTm::Var(ref x_w_def)), Subset(ref j))
                        if None != bitype::find_defs_for_idxtm_var(&ctx, x_w_def)
                        =>
                    { let xdef = bitype::find_defs_for_idxtm_var(&ctx, x_w_def);
                      match normal_idxtm(ctx, xdef.unwrap()) {
                          IdxTm::NmSet(ns) => {
                              let mut terms = vec![];
                              for t in ns.terms.iter() {
                                  match t {
                                      &NmSetTm::Single(ref n) => {
                                          fgi_db_normal!("Here? 1");
                                          let tm = normal_idxtm(ctx, IdxTm::Bin(Rc::new(IdxTm::Sing(n.clone())), Rc::new(j.clone())));
                                          nmset_terms_add(ns.cons.clone(), &mut terms, NmSetTm::Subset(tm))
                                      }
                                      &NmSetTm::Subset(ref i) => {
                                          fgi_db_normal!("Here? 2");
                                          let tm = normal_idxtm(ctx, IdxTm::Bin(Rc::new(i.clone()), Rc::new(j.clone())));
                                          nmset_terms_add(ns.cons.clone(), &mut terms, NmSetTm::Subset(tm));
                                      }
                                  }
                              };
                              Subset(IdxTm::NmSet(NmSet{
                                  cons:ns.cons.clone(),
                                  terms:terms,
                              }))
                          },
                          _ => {
                              Subset(normal_idxtm(
                                  ctx, IdxTm::Bin(Rc::new(IdxTm::Var(x_w_def.clone())),Rc::new(j.clone()))
                              ))
                          }
                      }
                    }
                    //  i * (Y1 % Y2) == (i * Y1) % (i * Y2)
                    //
                    //  TODO
                    //  
                    // (subset-level identity) -- no normalization recursion; it would diverge.
                    (Subset(i), Subset(j)) => {
                        Subset(IdxTm::Bin(
                            Rc::new(i),
                            Rc::new(j)
                        ))
                    },                    
                }};
                match ((*i1).clone(), (*i2).clone()) {
                    (IdxTm::Var(x),
                     IdxTm::NmSet(ns2)) =>
                    {
                        let mut terms = vec![];
                        for tm2 in ns2.terms.iter() {
                            nmset_terms_add(
                                ns2.cons.clone(), &mut terms,
                                bin_tm(ctx, NmSetTm::Subset(IdxTm::Var(x.clone())),tm2.clone()));
                        }
                        IdxTm::NmSet(NmSet{
                            cons:ns2.cons,
                            terms:terms
                        })
                    },                    
                    (IdxTm::NmSet(ns1),
                     IdxTm::Var(y)) =>
                    {
                        let mut terms = vec![];
                        for tm1 in ns1.terms.iter() {
                            nmset_terms_add(
                                ns1.cons.clone(), &mut terms,
                                bin_tm(ctx, tm1.clone(), NmSetTm::Subset(IdxTm::Var(y.clone()))));
                        }
                        //fgi_db!("match bin DONE");
                        IdxTm::NmSet(NmSet{
                            cons:ns1.cons,
                            terms:terms
                        })
                    },                   
                    (IdxTm::NmSet(ns1),
                     IdxTm::NmSet(ns2)) =>
                    {
                        let cons3 = nmset_cons_join(ns1.cons, ns2.cons);
                        let mut terms = vec![];
                        for tm1 in ns1.terms.iter() {
                            for tm2 in ns2.terms.iter() {
                                nmset_terms_add(
                                    cons3.clone(), &mut terms,
                                    bin_tm(ctx, tm1.clone(), tm2.clone()));
                            }
                        }
                        //fgi_db!("match bin DONE");
                        IdxTm::NmSet(NmSet{
                            cons:cons3,
                            terms:terms
                        })                        
                    },
                    (i, j) => {
                        //fgi_db!("match bin DONE");
                        IdxTm::Bin(Rc::new(i), Rc::new(j))
                    }
                }
            }                

            IdxTm::App(i1, i2) => {
                let i1 = normal_idxtm_rec(ctx, i1);
                let i2 = normal_idxtm_rec(ctx, i2);
                match (*i1).clone() {
                    IdxTm::WriteScope => {
                        match (*i2).clone() {
                            IdxTm::NmSet(mut ns) => {
                                let mut terms = vec![];
                                for t in ns.terms.iter() {
                                    match *t {
                                        NmSetTm::Single(ref n) => {
                                            terms.push( NmSetTm::Single(
                                                normal_nmtm(
                                                    ctx, NameTm::App( Rc::new(NameTm::WriteScope), Rc::new(n.clone())
                                                    ) ) ) )
                                        },
                                        NmSetTm::Subset(ref i) => {
                                            let i = 
                                                if false {
                                                    // Causing infinite regression:
                                                    normal_idxtm(
                                                        ctx, IdxTm::App(
                                                            Rc::new( IdxTm::WriteScope ),
                                                            Rc::new(i.clone())))
                                                } else { 
                                                    IdxTm::App(
                                                        Rc::new( IdxTm::WriteScope ),
                                                        Rc::new(i.clone()))
                                                };
                                            nmset_terms_add(
                                                ns.cons.clone(),
                                                &mut terms,
                                                NmSetTm::Subset( i )
                                            );
                                        }
                                    }
                                }
                                ns.terms = terms;
                                //fgi_db!("App BEGIN 2");
                                let r = normal_idxtm(ctx, IdxTm::NmSet(ns));
                                //fgi_db!("App END 2");
                                r
                            },
                            i2 => {
                                fgi_db_normal!("Here? 3");
                                normal_idxtm(ctx, IdxTm::Map(Rc::new(NameTm::WriteScope), Rc::new(i2)))
                            }
                        }
                    },
                    IdxTm::Lam(x,_gx,i11) => {
                        fgi_db_normal!("Here? 4");
                        let i11 = subst::subst_term_idxtm(Term::IdxTm((*i2).clone()), &x, (*i11).clone());
                        normal_idxtm(ctx, i11)
                    }
                    _ => IdxTm::App(i1, i2)
                }
            }

            IdxTm::Map(n1, i2) => {
                let n1 = normal_nmtm_rec(ctx, n1);
                let i2 = normal_idxtm_rec(ctx, i2);
                match ((*n1).clone(), (*i2).clone()) {
                    // Case: The function is known, and the set is
                    // (possibly) known, via the context; use the
                    // context to see if there are propositional
                    // definitions of the variable; if so, decompose
                    // the variable:
                    (NameTm::Lam(_,_,_), IdxTm::Var(ref x))
                        if None != bitype::find_defs_for_idxtm_var(&ctx, &x) =>
                    {
                        let xdef = bitype::find_defs_for_idxtm_var(&ctx, &x).unwrap();
                        match normal_idxtm(ctx, xdef) {
                            IdxTm::NmSet(ns) => {
                                let mut terms = vec![];
                                for t in ns.terms.iter() {
                                    match t {
                                        &NmSetTm::Single(ref n) => {
                                            fgi_db_normal!("Here? 5");
                                            let tm = normal_idxtm(ctx, IdxTm::Map(n1.clone(), Rc::new(IdxTm::Sing(n.clone()))));
                                            nmset_terms_add(ns.cons.clone(), &mut terms, NmSetTm::Subset(tm))
                                        }
                                        &NmSetTm::Subset(ref i) => {
                                            fgi_db_normal!("Here? 6");
                                            let tm = normal_idxtm(ctx, IdxTm::Map(n1.clone(), Rc::new(i.clone())));
                                            nmset_terms_add(ns.cons.clone(), &mut terms, NmSetTm::Subset(tm));
                                        }
                                    }
                                };
                                IdxTm::NmSet(NmSet{                                            
                                    cons:ns.cons.clone(),
                                    terms:terms,
                                })
                            },
                            _ => {
                                IdxTm::Map(n1, i2)
                            }
                        }
                    }
                    (NameTm::Lam(_x,_gx,_n11), IdxTm::NmSet(ns2)) => {
                        let mut terms = vec![];
                        for tm2 in ns2.terms.iter() {
                            use self::NmSetTm::*;
                            let mapped_tm = match tm2.clone() {
                                Single(n) => {
                                    Single(normal_nmtm(ctx, NameTm::App(n1.clone(), Rc::new(n.clone()))))
                                }
                                Subset(i) => {
                                    Subset(IdxTm::Map(n1.clone(), Rc::new(i)))
                                }
                            };
                            nmset_terms_add(ns2.cons.clone(), &mut terms, mapped_tm)
                        };
                        IdxTm::NmSet(NmSet{
                            cons:ns2.cons,
                            terms:terms
                        })
                    },                            
                    (NameTm::WriteScope, IdxTm::NmSet(ns2)) => {
                        let mut terms = vec![];
                        for tm2 in ns2.terms.iter() {
                            use self::NmSetTm::*;
                            let mapped_tm = match tm2.clone() {
                                Single(n) => {
                                    Single(normal_nmtm(ctx, NameTm::App(Rc::new(NameTm::WriteScope), Rc::new(n.clone()))))
                                }
                                Subset(i) => {
                                    fgi_db_normal!("Here? 7");
                                    // FIX(?): Divergent loop: Subset(normal_idxtm(ctx, IdxTm::Map(Rc::new(NameTm::WriteScope), Rc::new(i))))
                                    Subset(IdxTm::Map(Rc::new(NameTm::WriteScope), Rc::new(i)))
                                }
                            };
                            nmset_terms_add(ns2.cons.clone(), &mut terms, mapped_tm)
                        };
                        IdxTm::NmSet(NmSet{
                            cons:ns2.cons,
                            terms:terms
                        })
                    },                            
                    (n1, i2) => {
                        IdxTm::Map(Rc::new(n1), Rc::new(i2))
                    }
                }
            }

            IdxTm::MapStar(n1, i2) => {
                //fgi_db!("BEGIN normal(MapStar {} {}) = ", n1, i2);
                let n1 = normal_nmtm_rec(ctx, n1);
                let i2 = normal_idxtm_rec(ctx, i2);
                match ((*n1).clone(), (*i2).clone()) {
                    // Case: The function is known, and the set is
                    // (possibly) known, via the context; use the
                    // context to see if there are propositional
                    // definitions of the variable; if so, decompose
                    // the variable:
                    (NameTm::Lam(_,_,_), IdxTm::Var(ref x))
                        if None != bitype::find_defs_for_idxtm_var(&ctx, &x) =>
                    {
                        let xdef = bitype::find_defs_for_idxtm_var(&ctx, &x).unwrap();
                        match normal_idxtm(ctx, xdef) {
                            IdxTm::NmSet(ns) => {
                                let mut terms = vec![];
                                for t in ns.terms.iter() {
                                    match t {
                                        &NmSetTm::Single(ref n) => {
                                            fgi_db_normal!("Here? 8");                                            
                                            let tm = normal_idxtm(ctx, IdxTm::MapStar(n1.clone(), Rc::new(IdxTm::Sing(n.clone()))));
                                            nmset_terms_add(ns.cons.clone(), &mut terms, NmSetTm::Subset(tm));
                                        }
                                        &NmSetTm::Subset(ref i) => {
                                            fgi_db_normal!("Here? 9");                                            
                                            let tm = normal_idxtm(ctx, IdxTm::MapStar(n1.clone(), Rc::new(i.clone())));
                                            nmset_terms_add(ns.cons.clone(), &mut terms, NmSetTm::Subset(tm));
                                        }
                                    }
                                };
                                IdxTm::NmSet(NmSet{                                            
                                    cons:ns.cons.clone(),
                                    terms:terms,
                                })
                            },
                            _ => {
                                IdxTm::MapStar(n1, i2)
                            }
                        }
                    }
                    (NameTm::Lam(_,_,_), IdxTm::NmSet(ref ns2)) => {
                        if ns2.terms.len() == 0 {
                            // For empty sets, the map result is always
                            // empty. We do not apply the (starred)
                            // function for non-empty sets.
                            IdxTm::NmSet(NmSet{
                                cons:ns2.cons.clone(),
                                terms:vec![]
                            })
                        } else {
                            let mut terms = vec![];
                            //fgi_db!("Begin: Terms are {}", ns2.terms);
                            for tm2 in ns2.terms.iter() {
                                use self::NmSetTm::*;
                                let mapped_tm = match tm2.clone() {
                                    Single(n) => {
                                        Subset(IdxTm::MapStar(n1.clone(), Rc::new(IdxTm::Sing(n))))
                                    }
                                    Subset(i) => {
                                        Subset(IdxTm::MapStar(n1.clone(), Rc::new(i)))
                                    }
                                };
                                nmset_terms_add(ns2.cons.clone(), &mut terms, mapped_tm)
                            };                   
                            //fgi_db!("Done: New terms are {}", terms);
                            IdxTm::NmSet(NmSet{
                                cons:ns2.cons.clone(),
                                terms:terms
                            })
                        }
                    },                            
                    (n1, i2) => {
                        //fgi_db!("Done: Terms are UNCHANGED: {} {}", n1, i2);
                        IdxTm::MapStar(Rc::new(n1), Rc::new(i2))
                    }
                }
            }
            
            IdxTm::FlatMap(i1, i2) => {
                //fgi_db!("BEGIN normal(FlatMap {} {}) = ", i1, i2);
                let i1 = normal_idxtm_rec(ctx, i1);
                let i2 = normal_idxtm_rec(ctx, i2);
                match ((*i1).clone(), (*i2).clone()) {
                    // Case: The function is known, and the set has
                    // structure: Apply the function:
                    (IdxTm::Lam(x,_gx,i11), IdxTm::NmSet(ns2)) => {
                        let mut terms = vec![];
                        for tm2 in ns2.terms.iter() {
                            use self::NmSetTm::*;
                            match tm2.clone() {
                                Single(n) => {
                                    let i12 = subst::subst_term_idxtm(Term::NmTm(n.clone()), &x, (*i11).clone());
                                    match normal_idxtm(ctx, i12) {
                                        IdxTm::NmSet(mut ns) => {
                                            if ns.cons == None || ns.cons == Some(NmSetCons::Apart) {
                                                // Flatten!
                                                terms.append(&mut ns.terms);
                                                ns.cons = Some(NmSetCons::Apart);
                                            } else {
                                                // Union-based name set; Do not flatten.
                                                terms.push(Subset(IdxTm::NmSet(ns)))
                                            }
                                        }
                                        i13 => {
                                            nmset_terms_add(ns2.cons.clone(), &mut terms, Subset(i13))
                                        }
                                    }
                                }
                                Subset(i) => {
                                    fgi_db_normal!("Here? 9");
                                    nmset_terms_add(
                                        ns2.cons.clone(),
                                        &mut terms,
                                        NmSetTm::Subset(normal_idxtm(ctx, IdxTm::FlatMap(i1.clone(), Rc::new(i))))
                                    );
                                }
                            };                            
                        };
                        // construct set of terms:
                        IdxTm::NmSet(NmSet{
                            cons:ns2.cons,
                            terms:terms
                        })                          
                    },
                    // Case: The function is known, and the set is
                    // (possibly) known, via the context; use the
                    // context to see if there are propositional
                    // definitions of the variable; if so, decompose
                    // the variable:
                    (IdxTm::Lam(_,_,_), IdxTm::Var(ref x))
                        if None != bitype::find_defs_for_idxtm_var(&ctx, &x) =>
                    {
                        let xdef = bitype::find_defs_for_idxtm_var(&ctx, &x).unwrap();
                        match normal_idxtm(ctx, xdef) {
                            IdxTm::NmSet(ns) => {
                                let mut terms = vec![];
                                for t in ns.terms.iter() {
                                    match t {
                                        &NmSetTm::Single(ref n) => {
                                            fgi_db_normal!("Here? 10");
                                            let tm = normal_idxtm(ctx, IdxTm::FlatMap(i1.clone(), Rc::new(IdxTm::Sing(n.clone()))));
                                            nmset_terms_add(ns.cons.clone(), &mut terms, NmSetTm::Subset(tm))
                                        }
                                        &NmSetTm::Subset(ref i) => {
                                            fgi_db_normal!("Here? 11");
                                            let tm = normal_idxtm(ctx, IdxTm::FlatMap(i1.clone(), Rc::new(i.clone())));
                                            nmset_terms_add(ns.cons.clone(), &mut terms, NmSetTm::Subset(tm));
                                        }
                                    }
                                };
                                IdxTm::NmSet(NmSet{                                            
                                    cons:ns.cons.clone(),
                                    terms:terms,
                                })
                            },
                            _ => {
                                //panic!("TODO");
                                IdxTm::FlatMap(i1, i2)
                            }
                        }
                    }
                    // Case: The body of the function is exposing set
                    // structure (but not the set argument), so apply
                    // the function and re-expose this set structure.
                    (IdxTm::Lam(x,gx,body), j) => { match (*body).clone() {
                        IdxTm::Sing(body_nmtm) => {
                            fgi_db_normal!("Here? 11");
                            //fgi_db_normal!("XXX Lam Sing");
                            //fgi_db!(" ************** \n Name term body:\n\t{}", body_nmtm);
                            normal_idxtm(
                                ctx,
                                IdxTm::Map(Rc::new(NameTm::Lam(x,gx,Rc::new(body_nmtm))),
                                           Rc::new(j))
                            )
                        },
                        // XXX/TODO -- Same reasoning for Unions?
                        IdxTm::Apart(body_l, body_r) => {
                            fgi_db_normal!("Here? 12");
                            //fgi_db!(" ************** \n Left:\n\t{}\n Right:\n\t{}", body_l, body_r);
                            normal_idxtm(
                                ctx,
                                IdxTm::Apart(
                                    Rc::new(normal_idxtm(
                                        ctx, 
                                        IdxTm::FlatMap(
                                            Rc::new(IdxTm::Lam(x.clone(), gx.clone(), body_l)),
                                            Rc::new(j.clone())
                                        ))),
                                    Rc::new(normal_idxtm(
                                        ctx, 
                                        IdxTm::FlatMap(
                                            Rc::new(IdxTm::Lam(x.clone(), gx.clone(), body_r)),
                                            Rc::new(j)
                                        ))),
                                ))
                        },
                        // Give up: The set argument is not exposing
                        // any structure, and the lambda body is not
                        // exposing any set structure, so give up, and
                        // do not return a canonical `NmSet` form.
                        _ => {
                            //panic!("TODO");
                            IdxTm::FlatMap(i1, i2)
                        }
                    }},
                    _tm => {
                        //panic!("TODO: {}", tm);
                        // Give up: No structure to work with at all:
                        IdxTm::FlatMap(i1, i2)
                    }
                }
            },

            IdxTm::FlatMapStar(i, j) => {
                // Do _not_ unroll the kleene star; there's no way to
                // know how much is the right amount
                let i = normal_idxtm_rec(ctx, i);
                let j = normal_idxtm_rec(ctx, j);
                match ((*i).clone(), (*j).clone()) {
                    // Case: The function is known, and the set is
                    // (possibly) known, via the context; use the
                    // context to see if there are propositional
                    // definitions of the variable; if so, decompose
                    // the variable:
                    (IdxTm::Lam(_,_,_), IdxTm::Var(ref x))
                        if None != bitype::find_defs_for_idxtm_var(&ctx, &x) =>
                    {
                        let xdef = bitype::find_defs_for_idxtm_var(&ctx, &x).unwrap();
                        match normal_idxtm(ctx, xdef) {
                            IdxTm::NmSet(ns) => {
                                let mut terms = vec![];
                                for t in ns.terms.iter() {
                                    match t {
                                        &NmSetTm::Single(ref n) => {
                                            fgi_db_normal!("Here? 12");
                                            let tm = normal_idxtm(ctx, IdxTm::FlatMapStar(i.clone(), Rc::new(IdxTm::Sing(n.clone()))));
                                            nmset_terms_add(
                                                ns.cons.clone(),
                                                &mut terms,
                                                NmSetTm::Subset(tm)
                                            );
                                        }
                                        &NmSetTm::Subset(ref j) => {
                                            fgi_db_normal!("Here? 13");
                                            let tm = normal_idxtm(ctx, IdxTm::FlatMapStar(i.clone(), Rc::new(j.clone())));
                                            nmset_terms_add(
                                                ns.cons.clone(),
                                                &mut terms,
                                                NmSetTm::Subset(tm)
                                            );
                                        }
                                    }
                                };
                                IdxTm::NmSet(NmSet{                                            
                                    cons:ns.cons.clone(),
                                    terms:terms,
                                })
                            },
                            _ => {
                                //panic!("TODO");
                                IdxTm::FlatMapStar(i, j)
                            }
                        }
                    },
                    // Case: The body of the function is exposing set
                    // structure; so apply
                    // the function and re-expose this set structure.
                    (IdxTm::Lam(x,gx,body),_) => { match (*body).clone() {
                        IdxTm::Sing(body_nmtm) => {
                            //fgi_db!("Here? -- normalize MapStar");
                            //fgi_db!(" ************** \n Name term body:\n\t{}", body_nmtm);
                            fgi_db_normal!("Here? 14");
                            // normal_idxtm(
                            //     ctx,
                            //     IdxTm::MapStar(Rc::new(NameTm::Lam(x,gx,Rc::new(body_nmtm))), j)
                            // )
                            IdxTm::MapStar(Rc::new(NameTm::Lam(x,gx,Rc::new(body_nmtm))), j)
                        },
                        // XXX/TODO -- Same reasoning for Unions?                        
                        IdxTm::Apart(body_l, body_r) => {
                            fgi_db_normal!("Here? 15");
                            //fgi_db!(" ************** \n Left:\n\t{}\n Right:\n\t{}", body_l, body_r);
                            normal_idxtm(
                                ctx,
                                IdxTm::Apart(
                                    Rc::new(normal_idxtm(
                                        ctx, 
                                        IdxTm::FlatMapStar(
                                            Rc::new(IdxTm::Lam(x.clone(), gx.clone(), body_l)),
                                            j.clone()
                                        ))),
                                    Rc::new(normal_idxtm(
                                        ctx, 
                                        IdxTm::FlatMapStar(
                                            Rc::new(IdxTm::Lam(x.clone(), gx.clone(), body_r)), j
                                        ))),
                                ))
                        },
                        // Give up: The set argument is not exposing
                        // any structure, and the lambda body is not
                        // exposing any set structure, so give up, and
                        // do not return a canonical `NmSet` form.
                        _ => {
                            //panic!("TODO");
                            IdxTm::FlatMapStar(i, j)
                        }
                    }},
                    (_, _) => {
                        //panic!("TODO: {} {}", i j);
                        // Give up: No structure to work with at all:
                        IdxTm::FlatMapStar(i, j)
                    }
                }
            }

            // In all other cases, do nothing:
            i_othercase => {
                i_othercase
            }
        }
    }
}

/// Compute normal form for name term (expand definitions and reduce applications).
pub fn normal_nmtm(ctx:&Ctx, n:NameTm) -> NameTm {
    if is_normal_nmtm(ctx, &n) {
        return n
    } else {
        match n {
            NameTm::Ident(x) => {
                match ctx.lookup_nmtm_def(&x) {
                    Some(a) => {
                        normal_nmtm(ctx, a)
                    },
                    _ => {
                        fgi_db!("undefined name term: {} in\n{}", x, ctx);
                        // Give up:
                        NameTm::Ident(x.clone())
                    }
                }
            }
            NameTm::Bin(n1,n2) => {
                let n1 = normal_nmtm_rec(ctx, n1);
                let n2 = normal_nmtm_rec(ctx, n2);
                match ((*n1).clone(),(*n2).clone()) {
                    (NameTm::Name(n1),
                     NameTm::Name(n2)) => {
                        // Normal form of `n`:
                        NameTm::Name(
                            Name::Bin(Rc::new(n1),
                                      Rc::new(n2)))
                    },
                    _ => NameTm::Bin(n1,n2)
                }
            },
            NameTm::App(n1,n2) => {
                let n1 = normal_nmtm_rec(ctx, n1);
                let n2 = normal_nmtm_rec(ctx, n2);
                match ((*n1).clone(), (*n2).clone()) {
                    (NameTm::Lam(x, _xg, n11), n2) => {
                        let n12 = subst::subst_nmtm_rec(n2, &x, n11);
                        normal_nmtm(ctx, (*n12).clone())
                    },
                    _ => NameTm::App(n1,n2)
                }
            },
            // In all other cases (NoParse, etc), do nothing:
            n_othercase => n_othercase
        }
    }
}

/// Compute normal form for name term (expand definitions and reduce applications).
pub fn normal_nmtm_rec(ctx:&Ctx, n:Rc<NameTm>) -> Rc<NameTm> {
    Rc::new(normal_nmtm(ctx, (*n).clone()))
}


/// Convert the highly-structured, vectorized name set representation
/// into a less structured, AST representation.
pub fn idxtm_of_nmsettms(tms:&NmSetTms) -> IdxTm {
    let mut i : IdxTm = IdxTm::Empty;
    for t in tms.iter() {
        // TODO/XXX -- take set cons as param
        i = IdxTm::Apart(
            Rc::new({
                match (*t).clone() {
                    NmSetTm::Single(m) => IdxTm::Sing(m),
                    NmSetTm::Subset(i) => i.clone()
                }
            }),
            Rc::new(i)
        );
    }
    return i
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
    db_region_open!(false);
    fgi_db!("normal({}) ~~> ?", typ);
    let res = match typ {
        // normal forms:
        &Type::Unit         |
        &Type::Var(_)       |        
        &Type::NoParse(_)   
            =>
            typ.clone(),

        // TODO: ----------------------
        &Type::Rec(_, _)    |
        &Type::Nm(_)        |
        &Type::NmFn(_)      |
        &Type::TypeFn(_,_,_)|
        &Type::IdxFn(_,_,_)
            =>
            typ.clone(),

        &Type::Thk(ref i, ref ce) => {
            Type::Thk(normal_idxtm(ctx,i.clone()),
                      Rc::new(normal_ceffect(ctx, (**ce).clone())))
        }
        &Type::Ref(ref i, ref a) => {
            Type::Ref(normal_idxtm(ctx,i.clone()),
                      Rc::new(normal_type(ctx, a)))
        }        
        &Type::Sum(ref a, ref b) => {
            Type::Sum(Rc::new(normal_type(ctx, a)), 
                      Rc::new(normal_type(ctx, b)))
        }
        &Type::Prod(ref a, ref b) => {
            Type::Prod(Rc::new(normal_type(ctx, a)), 
                       Rc::new(normal_type(ctx, b)))
        }
        &Type::Exists(ref x, ref g, ref p, ref t) => {
            // TODO: Normalize name/index terms in proposition(s) p.
            // TODO: Extend context.
            //let xctx = ctx.var
            let t2 = normal_type(ctx, t);
            Type::Exists(x.clone(), g.clone(), p.clone(), Rc::new(t2))
        }
        &Type::Ident(ref x) => {
            crate::expand::expand_type(ctx, Type::Ident(x.clone()))
        },
        &Type::IdentDef(ref _ident, ref def) => { 
            (**def).clone() 
        },
        &Type::Prim(ref pt) => { Type::Prim(pt.clone()) },
        &Type::Abstract(ref x) => { Type::Abstract(x.clone()) },
        &Type::IdentUndef(ref x) => { Type::IdentUndef(x.clone()) },
        &Type::TypeApp(ref a, ref b) => {
            let a = normal_type(ctx, a);
            let b = normal_type(ctx, b);
            match a {
                Type::TypeFn(ref x, ref _k, ref body) => {
                    let body = subst::subst_type_type(b,x,(**body).clone());
                    normal_type(ctx, &body)
                },
                a => {
                    Type::TypeApp(Rc::new(a), Rc::new(b))
                }
            }
        }
        &Type::IdxApp(ref a, ref i) => {
            let a = normal_type(ctx, a);
            let i = normal_idxtm(ctx, i.clone());
            //fgi_db!("normal_type(IdxApp({}, _) = ...", a);
            match a {
                Type::IdxFn(ref x, ref _g, ref body) => {
                    let body = subst::subst_idxtm_type(i.clone(),x,(**body).clone());
                    normal_type(ctx, &body)
                },
                a => {
                    Type::IdxApp(Rc::new(a), i.clone())
                }
            }
        }
    };
    fgi_db!("normal({}) ~~> {}", typ, res);
    db_region_close!();
    res
}


/// Normalize a computation type.
pub fn normal_ctype(ctx:&Ctx, ct:CType) -> CType {
    match ct {
        CType::Lift(a) => {
            CType::Lift(normal_type(ctx, &a))
        }
        CType::Arrow(a, ce) => {
            CType::Arrow(normal_type(ctx, &a),
                         normal_ceffect_rec(ctx, ce))
        }
        CType::NoParse(s) => CType::NoParse(s)
    }
}

/// Normalize an effect.
pub fn normal_effect(ctx:&Ctx, eff:Effect) -> Effect {
    match eff {
        Effect::WR(i, j) => {
            Effect::WR(normal_idxtm(ctx, i),
                       normal_idxtm(ctx, j))
        },
        Effect::NoParse(s) => Effect::NoParse(s)
    }        
}

/// Normalize a computation effect.
pub fn normal_ceffect(ctx:&Ctx, ce:CEffect) -> CEffect {
    db_region_open!(false);
    fgi_db!("normal({}) ~~> ?", ce);
    let res = match ce.clone() {
        CEffect::Cons(ct, eff) => {
            CEffect::Cons(normal_ctype(ctx, ct),
                          normal_effect(ctx, eff))
        }
        CEffect::ForallType(y, k, ce) => {
            CEffect::ForallType(y, k, normal_ceffect_rec(ctx, ce))
        }
        CEffect::ForallIdx(y, g, p, ce) => {
            CEffect::ForallIdx(y, g,
                               //normal_prop(t.clone(), x, p),
                               p.clone(),
                               normal_ceffect_rec(ctx, ce))
        }
        CEffect::NoParse(s) => CEffect::NoParse(s)
    };
    fgi_db!("normal({}) ~~> {}", ce, res);
    db_region_close!();
    res
}

/// Normalize a computation effect.
pub fn normal_ceffect_rec(ctx:&Ctx, ce:Rc<CEffect>) -> Rc<CEffect> {
    Rc::new(normal_ceffect(ctx, (*ce).clone()))
}


pub fn match_ceffect(ctx:&Ctx, ce:CEffect) -> CEffect {
    db_region_open!(false);
    fgi_db!("match_ceffect({}) ~~> ?", ce);
    let res = match ce.clone() {
        CEffect::Cons(ce, eff) => CEffect::Cons(match_ctype(ctx, ce), eff),
        ce => ce
    };
    fgi_db!("match_ceffect({}) ~~> {}", ce, res);
    db_region_close!();
    res
}

pub fn match_ctype(ctx:&Ctx, ct:CType) -> CType {
    match ct {
        CType::Lift(ref a) => CType::Lift(match_type(ctx, a)),
        ct => ct
    }
}

pub fn match_type_rec(ctx:&Ctx, t:&TypeRec) -> TypeRec {
    Rc::new(match_type(ctx, &**t))
}

pub fn match_type(ctx:&Ctx, t:&Type) -> Type {
    db_region_open!(false);
    fgi_db!("match_type({}) ~~> ?", t);
    let res = match t.clone() {
        Type::IdxApp(ref t, ref i) => {
            normal_type
                (&Ctx::Empty, 
                 &Type::IdxApp(crate::expand::expand_type_rec(ctx, t.clone()), i.clone()))
        },
        Type::IdentDef(_, ref t) => (**t).clone(),
        Type::Ident(ref x) => {
            crate::expand::expand_type(ctx, Type::Ident(x.clone()))
        },
        t => t,
    };
    fgi_db!("match_type({}) ~~> {}", t, res);
    db_region_close!();
    res
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
pub fn unroll_type(ctx:&Ctx, typ:&Type) -> (Type, bool) {
    db_region_open!(false);
    fgi_db!("unroll_type({}) ~~> ?", typ);
    let (res, flag) = match typ {
        // case: rec x.A =>
        &Type::Rec(ref x, ref a) => {
            //fgi_db!("UNROLL (2/2): Success.");
            // [(rec x.A)/x]A
            (subst::subst_type_type(typ.clone(), x, (**a).clone()), true)
        }
        &Type::IdxApp(ref t, ref i) => {
            //fgi_db!("UNROLL (1.5/2): IdxApp(_, {}).", i);
            let (t2, b) = unroll_type(ctx, t);
            (Type::IdxApp(Rc::new(t2), i.clone()), b)
        },
        &Type::TypeApp(ref t1, ref t2) => {
            //fgi_db!("UNROLL (1.5/2): TypeApp(_, {}).", t2);
            let (t12, b) = unroll_type(ctx, t1);
            (Type::TypeApp(Rc::new(t12), t2.clone()), b)
        },
        &Type::IdentDef(_, ref xdef) => {
            //fgi_db!("UNROLL (1.5/2): {}", x);
            unroll_type(ctx, &**xdef)
        },
        &Type::Ident(_) => {
            //fgi_db!("UNROLL (1.5/2): {}", x);
            unroll_type(ctx, &crate::expand::expand_type(ctx, typ.clone()))
        },
        // error
        _ => {
            //fgi_db!("UNROLL (2/2): Failure: Not (apparently) a recursive type.");
            //fgi_db!("error: not a recursive type; did not unroll it: {}", typ);
            (typ.clone(), false)
        }
    };       
    if flag {
        fgi_db!("unroll_type({}) ~~> {}", typ, res);
    } else {
        fgi_db!("unroll_type: failed to unroll: {}", typ);
    }
    db_region_close!();    
    (res, flag)
}

/*
/// **** UNSOUND: *******
///
/// Unroll a `rec` type just a little, exposing any binder that lies
/// just within its body, as the body's (head) type constructor.
///
/// Case 1:
///   `rec x. #y:g. A`       (expose index function)
///    ~~> `#y:g. rec x. A`
///
/// Case 2:
///   `rec x. #y:k. A`       (expose type function)
///    ~~> `#y:k. rec x. A`
///
/// Case 3:
///   `rec x. A`       (otherwise...)
///    ~~> `rec x. A`  (...no change)

fn unroll_past_binder(typ:&Type) -> (Type, bool) {    
    fgi_db!("unroll_past_binder({}) = ...", typ);
    match typ {
        // case: rec x.A =>
        &Type::Rec(ref x, ref a) => {
            match &**a {
                // rec x. #y:g. A
                //  ~~> #y:g. rec x. A
                &Type::IdxFn(ref y, ref g, ref body) => {
                    (Type::IdxFn(y.clone(), g.clone(), 
                                 Rc::new(Type::Rec(x.clone(), body.clone()))),
                     true)
                },
                // rec x. #y:k. A
                //  ~~> #y:k. rec x. A
                &Type::TypeFn(ref y, ref k, ref body) => {
                    (Type::TypeFn(y.clone(), k.clone(),
                                  Rc::new(Type::Rec(x.clone(), body.clone()))),
                     true)
                },
                _ => {
                    (typ.clone(), false)
                }
            }
        }
        // not a recursive type
        _ => {
            //fgi_db!("error: not a recursive type; did not unroll it: {}", typ);
            (typ.clone(), false)
        }
    }
}
*/
