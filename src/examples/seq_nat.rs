//
// Fungi module: linked lists with names, holding natural numbers
//
fgi_mod!{
    /// Lists of natural numbers
    type List  = (
        rec list. foralli (X,Y):NmSet.
            (+ Unit +
             (exists (X1,X2):NmSet | ((X1%X2)=X:NmSet).
              x Nm[X1] x Nat x Ref[Y](list[X2][Y])
             )
            )
    );

    type Lev = (Nat);
    
    /// Level trees of natural numbers
    type Seq  = (
        rec seq. foralli (X,Y):NmSet.
            (+ Unit
             + (x Nm[X] x Nat)
             (exists (X1,X2,X3):NmSet | ((X1%X2%X3)=X:NmSet).
              x Nm[X1] x Lev
              x Ref[Y](seq[X2][Y])
              x Ref[Y](seq[X3][Y])
             )
            )
    );
}

// TODO implement this stuff somewhere else:
// ============================================

// fn seq_of_list_untyped:(
//     Thk[0] foralli (X1,X2,Y):NmSet.
//         0 Lev ->
//         0 Ref[Y](x List[X1][Y] x Tree[X2][Y]) ->
//         exists (X1a,X1b):NmSet|(X1=(X1a%X1b)):NmSet.
//     { {@!}X1a ; ({@!}X1a)%Y }
//     F (Ref[Y] (x List[X1b][Y]
//                x Tree[X2%X1a][Y%({@!}X1a)]))
// ) = {
//     #plev. #list_ltree.
//     let list = {{force get_prj1} list_ltree }
//     unroll match list {
//         _u => { ret list_ltree }ll inj2 (inj1 (n, x))
//                 }
//                 let listref_xleaf = {{force ref_pair} listref xleaf}
//                 let (list_rtree, _list_rtree) = {
//                     memor{n,@1}{
//                         {force seq_of_list}[X1b][X1a][Y]
//                             xlev listref_xleaf
//                     }
//                 }
//                 let list  = {{force ref_prj1} list_ltree }
//                 let ltree = {{force ref_prj2} list_ltree }
//                 let nbin  = { n,(@@bin) }
//                 let tree = {
//                     ref nbin roll inj2 inj2 pack
//                         (?,?,?) (nbin, xlev, ltree, rtree)
//                 }
//                 let list_tree = {{force ref_pair} list tree}                  
//                 let (_list_rtree, list_rtree) = memo{n,@2}{
//                     {force seq_of_list}[?][?][?]
//                         plev list_tree
//                 }
//                 ret list_rtree
//             } else {
//                 ret list_ltree
//             }
//         }
//     }
// }

// fn seq_of_list:(
//     Thk[0] foralli (X1,X2,Y):NmSet.
//         0 Lev ->
//         0 Ref[Y](x List[X1][Y] x Tree[X2][Y]) ->
//         exists (X1a,X1b):NmSet|(X1=(X1a%X1b)):NmSet.
//     { {@!}X1a ; ({@!}X1a)%Y }
//     F (Ref[Y] (x List[X1b][Y]
//                x Tree[X2%X1a][Y%({@!}X1a)]))
// ) = {
//     #plev. #list_ltree.
//     let list = {{force get_prj1} list_ltree }
//     unroll match list {
//         _u => { ret list_ltree }
//         c => {
//             unpack (X1a,X1b) c = c
//             let (n, x, listref) = { ret c }
//             let xlev = {lev_of_name n}
//             if {xlev <= plev} {
//                 let xleaf : Tree[X1a][{@!}X1a] = {
//                     ref n roll inj2 (inj1 (n, x))
//                 }
//                 let listref_xleaf = {{force ref_pair} listref xleaf}
//                 let- (X1b1,X1b2) list_rtree = {
//                     memor{n,@1}{
//                         {force seq_of_list}[X1b][X1a][Y]
//                             xlev listref_xleaf
//                     }
//                 }
//                 let list  = {{force ref_prj1} list_ltree }
//                 let ltree = {{force ref_prj2} list_ltree }
//                 let nbin  = { n,(@@bin) }
//                 let tree : Tree[?][?] = {
//                     ref nbin roll inj2 inj2 pack
//                         (X1a,X2,X1b1) (nbin, xlev, ltree, rtree)
//                 }
//                 let list_tree = {{force ref_pair} list tree}
//                 pack- (?,?) {
//                     memo{n,@2}
//                     {{force seq_of_list}[?][?][?]
//                      plev list_tree
//                     }
//                 }
//             } else {
//                 ret list_ltree
//             }
//         }
//     }
// }
