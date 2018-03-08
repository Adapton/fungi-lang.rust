#![recursion_limit="128"]
#[macro_use]
extern crate fungi_lang;
    
#[test]
fn max () {
  use std::thread;
  let child =
    thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || { 
        max2()
    });
  let _ = child.unwrap().join();
}
fn max2() {
    use std::rc::Rc;
    use fungi_lang::ast::*;
    use fungi_lang::bitype::*;
    use fungi_lang::vis::*;

    let bundle : Bundle = fgi_bundle![
        decls {
            /// Optional natural numbers:
            type OpNat = (+ Unit + Nat );

            /// Compute the maximum optional natural number (among a pair)
            fn opnat_max:(
                Thk[0] 0 OpNat -> 0 OpNat -> 0 F OpNat
            ) = {
                #xo.#yo.
                match (xo) {
                    _u  => { ret yo }
                    x => { match (yo) {
                        _u => { ret yo }
                        y => {
                            if { x < y } {ret yo}
                            else {ret xo}
                        }
                    }}
                }
            }

            /// Levels (as numbers), for level trees.
            type Lev = ( Nat )

            /// Sequences (balanced binary level trees), whose leaves
            /// are optional natural numbers:
            type Seq = (
                rec seq. foralli (X,Y):NmSet.
                    (+ (+ Unit + Nat)
                     + (exists (X1,X2,X3)   :NmSet | ((X1%X2%X3)=X:NmSet).
                        exists (Y1,Y2,Y3,Y4):NmSet | ((Y1%Y2%Y3%Y4)=Y:NmSet).
                        x Nm[X1] x Lev
                        x Ref[Y1](seq[X2][Y2])
                        x Ref[Y3](seq[X3][Y4]))
                    )
            );                

            /// Pointers written for each name in a structural recursion (-`_SR`) over a sequence:
            idxtm Seq_SR = ( #x:Nm.({x,@1})%({x,@2}) );

            /// ... prefixed with the current write scope (`WS`-), named `@!` below, as a nameset-level function
            idxtm WS_Seq_SR  = ( #x:NmSet.{@!}((Seq_SR) x) );

            fn is_empty:(
                Thk[0] foralli (X,Y):NmSet.
                    0 (Seq[X][Y]) -> { 0; Y } F Bool
            ) = { unimplemented }
        }

        // Compute the optional natural number in a sequence
        let max:(
            Thk[0] foralli (X,Y):NmSet.
                0 Seq[X][Y] -> { {WS_Seq_SR} X; Y } F OpNat
        ) = {
            ret thunk fix max. #seq. match seq {
                on => { ret on }
                bin => {
                    unpack (X1,X2,X3,Y1,Y2,Y3,Y4) bin = bin
                    let (n,lev,l,r) = {ret bin}
                    let (_rsl, ml) = { memo{n,(@1)}{ {force max}[X2][Y2]{!l} } }
                    let (_rsr, mr) = { memo{n,(@2)}{ {force max}[X3][Y4]{!r} } }
                    {{force opnat_max} ml mr}
                }
            }
        }
        ret 0
    ];
    write_bundle("target/max.fgb", &bundle);
}
