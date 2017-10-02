//#[macro_use]
extern crate iodyn_lang;

#[test]
fn reverse_polish_calc_step1of3() {
    use std::rc::Rc;
    use iodyn_lang::bitype;
    use iodyn_lang::ast::{Exp,PrimApp,TCtxt,Type,PrimTyApp,CType};
    use iodyn_lang::ast::Exp::*;
    use iodyn_lang::ast::Val::{Var};

    /* Matt Says:
       What I _want_ to write, someday, is something like this:
    
     let (ctx, ast, ctype) = 
      iodyn_lang_parse("

        val chars : List(Char)
        val lex_st_init : LexSt
        
        let toks = list_fold_seq(chars, lex_st_init, 
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
                   Type::PrimApp(PrimTyApp::List(Rc::new(Type::PrimApp(PrimTyApp::Char)))));

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
    let cty : CType = 
        CType::F(
            Rc::new(Type::PrimApp(PrimTyApp::List(
                Rc::new(Type::PrimApp(PrimTyApp::LexSt))))));

    // 3. Give the expression, as an AST:
    //
    let ast : Exp =
        Anno(Rc::new(
            Let("toks".to_string(),
                Rc::new(PrimApp(
                    PrimApp::ListFoldSeq(
                        Var("chars".to_string()),
                        Var("lex_st_init".to_string()),
                        Rc::new(Lam("accum".to_string(),
                                    Rc::new(Lam("char".to_string(),
                                                Rc::new(App(Rc::new(
                                                    App(Rc::new(
                                                        Force(Var("lex_step".to_string()))),
                                                        Var("char".to_string()))),
                                                            Var("accum".to_string())))))))))),
                Rc::new(Ret(Var("toks".to_string()))))),
            cty.clone()
        );
    
    let cty2 = bitype::synth_exp(ctx, ast);
    assert_eq!(Some(cty), cty2)

    // TODO: Rust macros to make the Rust code a bit closer to the
    // ideal, listed above in comments (e.g., avoid "Rc::new", and
    // avoid having to quote and stringify every distinct variable
    // name).

    // Note on PrimApp type: We build in list/collection primitives
    // because it allows us to avoid the machinery of polymorphic,
    // higher-order functions in the type system and translation
    // rules.  Eventually, we want to handle these as "ordinary"
    // functions (not built-ins), but for now, doing so is more
    // complex than we'd like (again, due to them requiring
    // polymorphic, higher-order types).

}
