//#[macro_use]
extern crate iodyn_lang;

#[test]
fn reverse_polish_calc_step1of3() {
    use std::rc::Rc;
    use iodyn_lang::ast::{Exp,PrimApp};
    use iodyn_lang::ast::Exp::*;
    use iodyn_lang::ast::Val::{Var};

    /* Matt Says:
       What I _want_ to write, someday, is something like this:

     ast = iodyn_lang_parse("
        let toks = list_fold_seq(list_emp, \accum.\char. lex_step accum char);
        toks
    ")
    */

    // This is how to encode the program listed above, in my
    // comment. To check its types, we need a typing environment that
    // gives types for `list_emp`, `lex_step` and gives a (synthesis)
    // typing rule for the (built-in) primitive list_fold_seq.
    //
    // Note on PrimApp type: We build in list/collection primitives
    // because it allows us to avoid the machinery of polymorphic,
    // higher-order functions in the type system and translation
    // rules.  Eventually, we want to handle these as "ordinary"
    // functions (not built-ins), but for now, doing so is more
    // complex than we'd like (again, due to them requiring
    // polymorphic, higher-order types).
    //
    let ast : Exp =
        Let("toks".to_string(),
            Rc::new(PrimApp(
                PrimApp::ListFoldSeq(
                    Var("list_emp".to_string()),
                    Rc::new(Lam("accum".to_string(),
                                Rc::new(Lam("char".to_string(),
                                            Rc::new(App(Rc::new(
                                                App(Rc::new(
                                                    Force(Var("lex_step".to_string()))),
                                                    Var("accum".to_string()))),
                                                        Var("char".to_string())))))))))),
            Rc::new(Ret(Var("toks".to_string()))));
    drop(ast)

    // TODO: Rust macros to make the Rust code a bit closer to the
    // ideal, listed above in comments (e.g., avoid "Rc::new", and
    // avoid having to quote and stringify every distinct variable
    // name).
}
