#[macro_use]
extern crate iodyn_lang;

// Try to express all of the simple sequence operations for which
// IODyn has evaluation examples
#[test]
fn seq_operations() {
    use std::rc::Rc;
    use iodyn_lang::bitype;
    use iodyn_lang::ast::{Val,Exp,TCtxt,
                          Type,PrimTyApp,CType};
    use iodyn_lang::ast::cons::*;

    let ctx : TCtxt = TCtxt::Empty;
    let ctx : TCtxt =
        TCtxt::Var(Rc::new(ctx),
                   "chars".to_string(),
                   Type::PrimApp(PrimTyApp::Seq(Rc::new(Type::PrimApp(PrimTyApp::Char)))));

    let ast : Exp =
        exp_anno(
            exp_let!(

                // count the number of characters
                count = exp_seq_fold_up(
                    val_var!(chars),
                    val_nat(0),
                    exp_lam!{n => exp_ret(val_nat(1)) },
                    exp_lam!{l, r => exp_nat_add(val_var!(l), val_var!(r))}
                ),

                // get character codes (natural numbers) of chars
                codes = exp_seq_map(
                    val_var!(chars),
                    exp_lam!{c => exp_nat_of_char(val_var!(c))}
                ),

                // map character codes (natural numbers) into strings
                strings = exp_seq_map(
                    val_var!(codes),
                    exp_lam!{c => exp_str_of_nat(val_var!(c))}
                ),

                // reverse the character sequence
                chars_rev = exp_seq_reverse(val_var!(chars)),

                // filter the characters, keeping only "digits"
                digits = exp_seq_filter(
                    val_var!(chars),
                    exp_lam!{c => exp_let!(
                        n  = exp_nat_of_char(val_var!(c)),
                        b1 = exp_nat_lte(val_nat('0' as usize), val_var!(c)),
                        b2 = exp_nat_lte(val_var!(c), val_nat('9' as usize));
                        exp_bool_and(val_var!(b1), val_var!(b2))
                    )}
                ),

                // count the number of digits
                digit_count = exp_seq_fold_up(
                    val_var!(digits),
                    val_nat(0),
                    exp_lam!{n => exp_ret(val_nat(1)) },
                    exp_lam!{l, r => exp_nat_add(val_var!(l), val_var!(r))}
                );

                exp_ret(val_var!(count))
            ),
            CType::F(Rc::new(Type::PrimApp(PrimTyApp::Nat)))
        );
    
    assert!(bitype::synth_exp(ctx, ast.clone()) != None)
}

// Try to express all of the simple sequence operations for which
// IODyn has evaluation examples
#[test]
fn quickhull() {
    use std::rc::Rc;
    use iodyn_lang::bitype;
    use iodyn_lang::ast::{Val,Exp,TCtxt,
                          Type,PrimTyApp,CType};
    use iodyn_lang::ast::cons::*;

    let ctx : TCtxt = TCtxt::Empty;

    // TODO
}

#[test]
fn reverse_polish_calc_step1of3() {
    use std::rc::Rc;
    use iodyn_lang::bitype;
    use iodyn_lang::ast::{Val,Exp,PrimApp,TCtxt,Type,PrimTyApp,CType};
    use iodyn_lang::ast::Exp::*;
    use iodyn_lang::ast::Val::{Var};
    use iodyn_lang::ast::cons::*;

    /* Matt Says:
       What I _want_ to write, someday, is something like this:

     let (ctx, ast, ctype) =
      iodyn_lang_parse("

        val chars       : Seq(Char)
        val lex_st_init : LexSt
        val lex_step    : U( Char -> LexSt -> F(LexSt) )

        let toks = seq_fold_seq(chars, lex_st_init,
                                 \char. \lexst. lex_step char lexst );
        toks
        :
        F(LexSt)
      ")

    */

    // Below, we encode the (1) context, (2) computation type and (3)
    // ast listed above, in our magical parsing invocation.
    //
    // 1. Initialize typing context with variable declarations.  The
    // typing environment gives types for `chars`, `lex_st_init` and
    // `lex_step`.

    let ctx : TCtxt = TCtxt::Empty;

    let ctx : TCtxt =
        TCtxt::Var(Rc::new(ctx),
                   "chars".to_string(),
                   Type::PrimApp(PrimTyApp::Seq(Rc::new(Type::PrimApp(PrimTyApp::Char)))));

    let ctx : TCtxt =
        TCtxt::Var(Rc::new(ctx),
                   "lex_st_init".to_string(),
                   Type::PrimApp(PrimTyApp::LexSt));

    let ctx : TCtxt =
        TCtxt::Var(Rc::new(ctx),
                   "lex_step".to_string(),
                   Type::U(
                       Rc::new(CType::Arrow(
                           Rc::new(Type::PrimApp(PrimTyApp::Char)),
                           Rc::new(CType::Arrow(
                               Rc::new(Type::PrimApp(PrimTyApp::LexSt)),
                               Rc::new(CType::F(Rc::new(Type::PrimApp(PrimTyApp::LexSt))))))))));

    // - - - - - - -
    // 2. Give computation type, for annotating the expression term:
    //
    // cty =def= F(Seq(LexSt))
    //
    let cty : CType =
        CType::F(
            Rc::new(Type::PrimApp(PrimTyApp::LexSt)));

    // 3. Give the expression, as an AST:
    //
    // ast =def= (
    //         let toks = seq_fold_seq(chars, lex_st_init,
    //                                  \char. \lexst.
    //                                     force(lex_step) char lexst );
    //         ret toks
    //       )
    //
    let ast : Exp =
        Anno(Rc::new(
            Let("toks".to_string(),
                Rc::new(PrimApp(
                    PrimApp::SeqFoldSeq(
                        Var("chars".to_string()),
                        Var("lex_st_init".to_string()),
                        Rc::new(Lam("a".to_string(),
                                    Rc::new(Lam("c".to_string(),
                                                Rc::new(App(Rc::new(
                                                    App(Rc::new(
                                                        Force(Var("lex_step".to_string()))),
                                                        Var("a".to_string()))),
                                                            Var("c".to_string())))))))))),
                Rc::new(Ret(Var("toks".to_string()))))),
            cty.clone()
        );

    // 4. Use construction functions and macros instead of raw
    // constructors.
    //
    //         let toks = seq_fold_seq(chars, lex_st_init,
    //                                  \char. \lexst.
    //                                     force(lex_step) char lexst );
    //         ret toks
    //
    // Below, we use Rust macros to make the Rust construction code a
    // bit closer to the ideal, listed above in comments (e.g., avoid
    // "Rc::new", and avoid having to quote and stringify every
    // distinct variable name):

    let ast2 : Exp =
        exp_anno(
            exp_let!(
                toks = exp_seq_fold_seq(
                    val_var!(chars),
                    val_var!(lex_st_init),
                    exp_lam!{a, c =>
                             exp_app!(exp_force(val_var!(lex_step)),
                                      val_var!(a), val_var!(c))
                    }
                );
                exp_ret(val_var!(toks))
            ),
            cty.clone());

    let ast3 = make_exp![
        {
            let toks = {
                SeqFoldSeq(chars,lex_st_init,lam a.lam c.
                    {{force lex_step} a} c
                )
            }
            ret toks
        } : F LexSt
    ];
    
    // assert that abbreviations above preserve the AST structure:
    assert_eq!(ast, ast2);
    assert_eq!(ast2, ast3);

    // assert that the AST types:
    let cty2 = bitype::synth_exp(ctx, ast.clone());
    assert_eq!(Some(cty.clone()), cty2);
}
