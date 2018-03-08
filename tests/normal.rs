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
        println!("{:?}\n =({})=\n {:?}",
                 &ns1,
                 &ns1 == &ns2,
                 &ns2,
        );
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
                    ((#x:Nm. {x,@1} % {x,@2}) (Y))
                        %  (
                            ((#x:Nm. {x,@1} % {x,@2}) (X))
                                % (
                                    {z,@1} % {z,@2}
                                    %                                        
                                        0 ))))
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
