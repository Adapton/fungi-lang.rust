#![recursion_limit="128"]
#[macro_use]
extern crate fungi_lang;
    
#[test]
fn quickhull () {
  use std::thread;
  let child =
    thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || { 
      quickhull2()
    });
  let _ = child.unwrap().join();
}
fn quickhull2() {
    use std::rc::Rc;
    use fungi_lang::ast::*;
    use fungi_lang::bitype::*;
    use fungi_lang::vis::*;
    //use fungi_lang::eval::*;

// From Paper
// ----------
//
// qh1 ln pts h = 
//  let p =[ln@1] max_pt ln pts
//  let l =[ln@2] filter (ln.0,p) pts
//  let r =[ln@3] filter (p,ln.1) pts
//  let h = memo[ln@1](qh1 (p,ln.1) r h)
//  let h = push[ln@2](p,h)
//  let h = memo[ln@3](qh1 (ln.0,p) l h)
//  h

// qh2 ln pts h = 
//  let p =[3@1] max_pt ln pts
//  let l =[3@2] filter (ln.0,p) pts
//  let r =[3@3] filter (p,ln.1) pts
//  let h = memo[1]([1](qh2 (p,ln.1) r h))
//  let h = push[2](p,h)
//  let h = memo[3]([2](qh2 (ln.0,p) l h))
//  h

    let bundle : Bundle = fgi_bundle![
    //let qh_ast = fgi_exp![
        decls {
            type Hull = ( user(Hull) )
            type Pt = ( user(Pt) )
            type Pts = ( user(Pts) )
            type Line = ( (x Pt x Pt) )
        }
        let max_pt : (Thk[0] 0 Line -> 0 Pts -> 0 F Pt) = { unimplemented }
        let filter_line : (Thk[0] 0 Line -> 0 Pts -> 0 F Pts) = { unimplemented }
        let push : (Thk[0] 0 Pt -> 0 Hull -> 0 F Hull) = { unimplemented }

        let qh1 : (Thk[0] 0 Line -> 0 Pts -> 0 Hull -> { {@!}({@1}%{@3});0} F Hull) = {
            ret thunk fix qh1. #ln. #pts. #h.
            let (ll,lr) = { ret ln }
            let p = { {force max_pt} ln pts}
            let l = { {force filter_line} (ll,p) pts}
            let r = { {force filter_line} (p,lr) pts}
            let (rh,h) = { memo(@1){ {force qh1} (p,ll) r h } }
            let h = { {force push} p h }
            let (lh,h) = { memo(@3){ {force qh1} (lr,p) l h } }
            ret h
        }
        ret 0
    ];

    // println!("quickhull AST");
    // println!("-------------");
    // println!("{:?}", qh_ast);
    // let typed = synth_exp(None, &Ctx::Empty, &qh_ast);
    // println!("quickhull typing derivation");
    // println!("---------------------------");
    // println!("{:?}", typed);

    write_bundle("target/quickhull.fgb", &bundle);
}
