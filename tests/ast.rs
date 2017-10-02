#[macro_use]
extern crate iodyn_lang;

#[test]
fn reverse_polish_calc_step1of3() {
    use std::rc::Rc;
    use iodyn_lang::ast::{Exp,Val,PrimApp};
    use iodyn_lang::ast::Exp::*; 
    use iodyn_lang::ast::Val::*;

    /* What I _want_ to write, someday:

     ast = iodyn_lang_parse("
        let toks = list_fold_seq(list_emp, \accum.\char. lex_step accum char);
        toks
    ")
    */

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
}
                

