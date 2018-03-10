#![recursion_limit="128"]
#[macro_use]
extern crate fungi_lang;

use std::rc::Rc;
use fungi_lang::ast::*;
use fungi_lang::normal;
use fungi_lang::bitype;

fn idxtm_equiv_test(tm1:IdxTm, tm2:IdxTm) {
    let ctx = bitype::Ctx::Empty;
    let tm1 = normal::normal_idxtm(&ctx, tm1);
    let tm2 = normal::normal_idxtm(&ctx, tm2);
    if let (IdxTm::NmSet(mut ns1),
            IdxTm::NmSet(mut ns2)) = (tm1, tm2) {
        ns1.terms.sort();
        ns2.terms.sort();
        if false {
            println!("{:?}\n =({})=\n {:?}",
                     &ns1,
                     &ns1 == &ns2,
                     &ns2,
            );
        };
        assert_eq!(ns1, ns2);
    } else {
        unreachable!()
    }
}

#[test]
fn normal_test_1() {
    let (tm1, tm2) = (
        fgi_index![
            (#x:Nm. {x, @1} % {x, @2})
                ({@3}%Y)%(X%{z})
        ],
        fgi_index![
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
        ]);
    idxtm_equiv_test(tm1, tm2)    
}

#[test]
fn normal_test_2() {
    let (tm1, tm2) = (
        fgi_index![
            (#x:Nm. {x, @1} % {x, @2} % {x, @4} )
                ({@3}%Y)%(X%{z})
        ],
        fgi_index![
            {@3 * @1}
            % ( {@3 * @2}
                  % ( {@3 * @4}
                        % ( ((#x:Nm. {x,@1} % {x,@2} % {x,@4}) (Y))
                               %  ( ((#x:Nm. {x,@1} % {x,@2} % {x,@4}) (X))
                                       % ( {z,@1} % {z,@2} % {z,@4}
                                            % 0 )))))
        ]);
    idxtm_equiv_test(tm1, tm2)    
}


///////////////////////////

// NmSet { cons: Some(Apart), terms: [
//     Single(Name(Bin(Num(3), Num(1)))),
//     Single(Name(Bin(Num(3), Num(2)))),
//     Single(Bin(Var("z"), Name(Num(1)))),
//     Single(Bin(Var("z"), Name(Num(2)))),
//     Subset(FlatMap(Lam("x", Nm, Apart(Sing(Bin(Var("x"), Name(Num(1)))), Sing(Bin(Var("x"), Name(Num(2)))))), Var("X"))),
//     Subset(FlatMap(Lam("x", Nm, Apart(Sing(Bin(Var("x"), Name(Num(1)))), Sing(Bin(Var("x"), Name(Num(2)))))), Var("Y")))] }

// NmSet { cons: Some(Apart), terms: [
//     Single(Name(Bin(Num(3), Num(1)))),
//     Single(Name(Bin(Num(3), Num(2)))),
//     Single(Bin(Var("z"), Name(Num(1)))),
//     Single(Bin(Var("z"), Name(Num(2)))),
//     Subset(Map(Lam("x", Nm, Bin(Var("x"), Name(Num(1)))), Var("X"))),
//     Subset(Map(Lam("x", Nm, Bin(Var("x"), Name(Num(1)))), Var("Y"))),
//     Subset(Map(Lam("x", Nm, Bin(Var("x"), Name(Num(2)))), Var("X"))),
//     Subset(Map(Lam("x", Nm, Bin(Var("x"), Name(Num(2)))), Var("Y")))
