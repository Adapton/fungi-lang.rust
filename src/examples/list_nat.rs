//
// Fungi module: linked lists with names, holding natural numbers
//
fgi_mod!{
    /// Lists of natural numbers
    type List  = (
        rec list. foralli (X,Y):NmSet.
            (+ Unit +
             (exists (X1,X2):NmSet | ((X1%X2)=X:NmSet).
              exists (Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
              x Nm[X1] x Nat x Ref[Y1](list[X2][Y2])
             )
            )
    );
    
    // Allocates a ref cell, holding a cons cell, pointing at a list:
    //
    // ref         cons       ref     list
    // |{@!}X1|--->|X1|_|*|-->|Y1|--> |...[X2][Y2]...|
    //
    // : Ref[{@!}X1](List[X1%X2][Y1%Y2])
    //
    fn ref_cons:(
        Thk[0]
            foralli (X,X1,X2):NmSet | ((X1%X2)=X:NmSet).
            foralli (Y,Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
            0 Nm[X1] ->
            0 Nat ->
            0 Ref[Y1](List[X2][Y2]) ->
        {{@!}X;0} F Ref[{@!}X1](List[X1%X2][Y1%Y2])
    ) = {            
        #n.#h.#t. ref n
        roll inj2 pack (X1,X2,Y1,Y2) (n, h, t)
    }
    
    fn nat_is_zero:(
        Thk[0] 
            0 Nat -> 0 F Nat
    ) = {
        #n. {unsafe (1) trapdoor::nat_is_zero} n
    }
    
    fn nat_sub:(
        Thk[0] 
            0 Nat -> 0 Nat -> 0 F Nat
    ) = {
        #n.#m. {unsafe (2) trapdoor::nat_sub} n m
    }
    
    // XXX -- This type is wrong.  TODO -- figure out how to
    // ecode this type correctly, with existentials.
    fn name_of_nat:(
        Thk[0] 
            foralli X:NmSet.
            0 Nat -> 0 F Nm[X]
    ) = {
        #n. {unsafe (1) trapdoor::name_of_nat} n
    }
    
    // XXX -- This type is wrong.  TODO -- figure out how to
    // ecode this type correctly, with existentials.  
    fn gen:(
        Thk[0]
            foralli (Y1,X1,Y2):NmSet.
            0 Nat -> 0 F Ref[Y1](List[X1][Y2])
    ) = {
        #n. if {{force nat_is_zero} n} {
            ref (@0) roll inj1 ()
        } else {
            let nm = {{force name_of_nat} n}
            let p  = {{force nat_sub} n 1}
            let l  = {{force gen} p}
            {{force ref_cons}
             [X1][X1][X1][(Y1%Y2)][Y1][Y2]
             nm p l}
        }
    }
    
    fn map:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 (Thk[0] 0 Nat -> 0 F Nat) ->
            0 List[X][Y] ->
        {{@!}X; Y%({@!}X)} F List[X][{@!}X]
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let h2 = {{force f} h}
                let (rt2,_t2) = {
                    memo(n){{force map} [X2][Y2] f {!t}}
                }
                ret roll inj2
                    pack (X1,X2,{@!}X1,{@!}X2) (n, h2, rt2)
            }
        }
    }
    
    fn reverse:(
        Thk[0]
            foralli (X,Xa,Xb,Xc):NmSet | ((Xa%Xb%Xc)=X:NmSet).
            foralli (Y,Ya,Yb1,Yb2):NmSet | ((Ya%Yb1%Yb2)=Y:NmSet).
            0 List[Xa][Ya] ->
            0 Ref[Yb1](List[Xb][Yb2]) ->
            0 Nm[Xc] ->
        //
        // TODO: Fix parse error here:
        //        { {@!}(Xa % (Xa*({@1}))) ;
        //               {@!}(Xa*({@1})) % Y }
            0
            F Ref[{@!}Xc] List[Xa%Xb][Y]
    ) = {
        #l.#r.#rn. unroll match l {
            _u => { let r = {get r}
                    ref rn r }
            c => {
                unpack (Xa1,Xa2,Ya1,Ya2) c = c
                let (n, h, t) = { ret c }
                let r2 = { {force ref_cons}
                            [(Xa%Xb)][Xa][Xb][(Yb1%Yb2)][Yb1][Yb2]
                            n h t}
                let (_r,r) = {memo{n,(@1)}{{force reverse} {!t} r2 rn}}
                ret r
            }
        }
    }
}

pub mod dynamic_tests {
    #[test]    
    pub fn listing1() {
        use reduce;
        use std::rc::Rc;
        use ast::*;
        use adapton::engine;
        
        // ----------------------------------------------------
        // Fungi program (expression) to reduce, and visualize;
        //
        // Note: The presence of `use super::*` means that the module
        // declared above is in scope for the code below, without
        // having to manually duplicate the code.
        // ----------------------------------------------------
        let e = fgi_exp![
            use super::*;
            
            let list1  = {{force gen} 5} // list1 = [4,3,2,1,0]
            let refnil = {ref (@@nil) roll inj1 ()}
            let outs = { memo (@@archivist) {
                let list2 = {ws (@@map1) {memo (@@map1) {{force map} (thunk #x. x + 1) {!list1}}}}
                let list3 = {ws (@@map2) {memo (@@map2) {{force map} (thunk #x. x + 2) {!list1}}}}
                let list4 = {ws (@@rev)  {memo (@@rev)  {{{force reverse} {!list1} refnil (@@revres)}}}}
                ret (list1, list2, list3, list4)
            }}
            ret outs
            //
            // Produces the tuple:
            /*
                ( [4,3,2,1,0]
                , [5,4,3,2,1]
                , [7,5,4,3,2]
                , [0,1,2,3,4] 
        )
             */
        ];
        
        // --------------------------------------
        // Fungi/Adapton trace-collection harness
        // ---------------------------------------
        use html;
        use vis;
        use adapton::reflect;
        use adapton::reflect::trace;
        use std::fs::File;
        use std::io::BufWriter;
        use std::io::Write;
        use html::WriteHTML;
        
        // Initialize Adapton
        engine::manage::init_dcg();
        // Record a debugging trace of Adapton's behavior
        reflect::dcg_reflect_begin();
        // Run our Fungi program:
        let _result = {
            let mut lab = 0;
            // Label the sub-expressions of the Fungi program:
            let e = vis::label_exp(e, &mut lab);
            // Run the Fungi program:
            reduce::reduce(vec![], vec![], e)
        };
        let traces = reflect::dcg_reflect_end();
        let count = trace::trace_count(&traces, None);
        println!("{:?}", count);
        let f = File::create(format!("target/{}.html", filename_of_module_path!())).unwrap();
        let mut writer = BufWriter::new(f);
        writeln!(writer, "{}", html::style_string()).unwrap();
        writeln!(writer, "<div class=\"traces\">").unwrap();
        for tr in traces {
            html::div_of_trace(&tr).write_html(&mut writer);
        };
        writeln!(writer, "</div>").unwrap();
    }
}

// TODO (Hammer): 
//
// Once we have a fuller story for the module system, move these
// natural number primmitives into an appropriate module for them.
//
pub mod trapdoor {
    // This code essentially extends the Fungi evaluator
    use ast::{Name};
    use dynamics::{RtVal,ExpTerm};
    
    pub fn name_of_nat(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => { 
                ExpTerm::Ret(RtVal::Name(Name::Num(*n)))
            }
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }
    
    pub fn nat_is_zero(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => { 
                ExpTerm::Ret(RtVal::Bool(n == &0)) 
            },
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }
    
    pub fn nat_is_odd(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => { 
                ExpTerm::Ret(RtVal::Bool(n.checked_rem(2) == Some(1)))
            },
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }
    
    pub fn nat_is_even(args:Vec<RtVal>) -> ExpTerm {
        match &args[0] {
            RtVal::Nat(n) => { 
                ExpTerm::Ret(RtVal::Bool(n.checked_rem(2) == None))
            },
            v => panic!("expected a natural number, not: {:?}", v)
        }
    }
    
    pub fn nat_sub(args:Vec<RtVal>) -> ExpTerm {
        match (&args[0], &args[1]) {
            (RtVal::Nat(n), RtVal::Nat(m)) => {
                assert!(n >= m);
                //println!("{:?} - {:?} = {:?}", n, m, n - m);
                ExpTerm::Ret(RtVal::Nat(n - m))
            },
            (v1, v2) => 
                panic!("expected two natural numbers, not: {:?} and {:?}", v1, v2)
                
        }
    }
}


///////////////////////////////////////////////////////////////////////////////////////////////////////
#[test]
pub fn listing1 () { fgi_listing_expect![
    [Expect::FailurexXXX]
        
        decls {
            /// Lists of natural numbers
            type List  = (
                rec list. foralli (X,Y):NmSet.
                    (+ Unit +
                     (exists (X1,X2):NmSet | ((X1%X2)=X:NmSet).
                      exists (Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
                      x Nm[X1] x Nat x Ref[Y1](list[X2][Y2])
                     ))
            );
        }
    
    let cons:(
        Thk[0]
            foralli (X1,X2):NmSet. // <-- forgot to insist that X1%X2
            foralli (Y1,Y2):NmSet. // <-- forgot to insist that Y1%Y2
            0 Nm[X1] ->
            0 Nat ->
            0 Ref[Y1](List[X2][Y2]) ->
            0 F List[X1%X2][Y1%Y2]
    ) = {            
        ret thunk #n.#h.#t. ret roll inj2
            pack (X1,X2,Y1,Y2) (n, h, t)
    }
    
    ret 0
]}

///////////////////////////////////////////////////////////////////////////////////////////////////////
// OLD STUFF -- The following is stale, as of Friday, 2018.05.18
///////////////////////////////////////////////////////////////////////////////////////////////////////
/*

#[test]
pub fn listing0 () { fgi_listing_expect![
    [Expect::SuccessxXXX]
    
    decls {
        /// Lists of natural numbers
        type List  = (
            rec list. foralli (X,Y):NmSet.
            (+ Unit +
             (exists (X1,X2):NmSet | ((X1%X2)=X:NmSet).
              exists (Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
              x Nm[X1] x Nat x Ref[Y1](list[X2][Y2])
             ))
        );

        /// Optional natural numbers
        type OpNat  = (+ Unit + Nat );
    }

    // let nil:(
    //     Thk[0] foralli (X,Y):NmSet. 0 Unit -> 0 F List[X][Y]
    // ) = {            
    //     ret thunk #_u. ret roll inj1 ()
    // }
    
    let cons:(
        Thk[0]
            foralli (X,X1,X2):NmSet | ((X1%X2)=X:NmSet).
            foralli (Y,Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
            0 Nm[X1] ->
            0 Nat ->
            0 Ref[Y1](List[X2][Y2]) ->
            0 F List[X1%X2][Y1%Y2]
    ) = {            
        ret thunk #n.#h.#t. ret roll inj2
            pack (X1,X2,Y1,Y2) (n, h, t)
    }

    //
    // Allocates a ref cell, holding a cons cell, pointing at a list:
    //
    // ref         cons       ref     list
    // |{@!}X1|--->|X1|_|*|-->|Y1|--> |...[X2][Y2]...|
    //
    // : Ref[{@!}X1](List[X1%X2][Y1%Y2])
    //
    let ref_cons:(
        Thk[0]
            foralli (X,X1,X2):NmSet | ((X1%X2)=X:NmSet).
            foralli (Y,Y1,Y2):NmSet | ((Y1%Y2)=Y:NmSet).
            0 Nm[X1] ->
            0 Nat ->
            0 Ref[Y1](List[X2][Y2]) ->
            {{@!}X;0} F Ref[{@!}X1](List[X1%X2][Y1%Y2])
    ) = {            
        ret thunk #n.#h.#t. ref n
            roll inj2 pack (X1,X2,Y1,Y2) (n, h, t)
    }
   
    let rec map:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 (Thk[0] 0 Nat -> 0 F Nat) ->
            0 List[X][Y] ->
        {{@!}X; Y%({@!}X)} F List[X][{@!}X]
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let h2 = {{force f} h}
                let (rt2,_t2) = {
                    memo(n){{force map} [X2][Y2] f {!t}}
                }
                ret roll inj2
                    pack (X1,X2,{@!}X1,{@!}X2) (n, h2, rt2)
            }
        }
    }

    let rec filter:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 (Thk[0] 0 Nat -> 0 F Bool) ->
            0 List[X][Y] ->
        {{@!}X; Y%({@!}X)} F List[X][{@!}X]
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let (rt2, t2) = {
                    memo(n){{force filter} [X2][Y2] f {!t}}
                }
                if {{force f} h} {
                    ret roll inj2
                        pack (X1,X2,{@!}X1,{@!}X2) (n, h, rt2)
                }
                else {
                    ret t2
                }
            }
        }
    }

    let rec map_filter:(
        Thk[0]
            foralli (X,Y):NmSet.
            0 (Thk[0] 0 Nat -> 0 F OpNat) ->
            0 List[X][Y] ->
        {{@!}X; Y%({@!}X)} F List[X][{@!}X]
    ) = {
        #f.#l. unroll match l {
            _u => { ret roll inj1 () }
            c => {
                unpack (X1,X2,Y1,Y2) c = c
                let (n, h, t) = { ret c }
                let (rt2, t2) = {
                    memo(n){{force map_filter} [X2][Y2] f {!t}}
                }
                let oh2 = {{force f} h}
                match oh2 {
                    _u => { ret t2 }
                    h2 => {
                        ret roll inj2
                            pack (X1,X2,{@!}X1,{@!}X2) (n, h, rt2)
                    }
                }
            }
        }
    }

    let rec reverse:(
        Thk[0]
            foralli (X,Xa,Xb,Xc):NmSet | ((Xa%Xb%Xc)=X:NmSet).
            foralli (Y,Ya,Yb1,Yb2):NmSet | ((Ya%Yb1%Yb2)=Y:NmSet).
            0 List[Xa][Ya] ->
            0 Ref[Yb1](List[Xb][Yb2]) ->
            0 Nm[Xc] ->
        //
        // TODO: Fix parse error here:
        //        { {@!}(Xa % (Xa*({@1}))) ;
        //               {@!}(Xa*({@1})) % Y }
            0
            F Ref[{@!}Xc] List[Xa%Xb][Y]
    ) = {
        #l.#r.#n. unroll match l {
            _u => { let r = {get r}
                    ref n r }
            c => {
                unpack (Xa1,Xa2,Ya1,Ya2) c = c
                let (n, h, t) = { ret c }
                let r2 = { {force ref_cons}
                            [(Xa%Xb)][Xa][Xb][(Yb1%Yb2)][Yb1][Yb2]
                            n h t}
                let (_r,r) = {memo{n,(@1)}{{force reverse} {!t} r2}}
                ret r
            }
        }
    }

    // let rec fold:(
    //     Thk[0]
    //         0 List ->
    //         0 Nat ->
    //         0 (Thk[0] 0 Nat -> 0 Nat -> 0 F Nat) ->
    //         0 F Nat
    // ) = {
    //     #l.#a.#f. unroll match l {
    //         _u => { ret a }
    //         c => {
    //             let (h, t) = { ret c }
    //             let a2 = {{force f} a h}
    //             {{force fold} t a2 f}
    //         }
    //     }
    // }
        
    ret 0
]}

*/
