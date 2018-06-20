use examples::seq_nat;
use examples::name;
use examples::nat;

fgi_mod!{
    use seq_nat::*;
    use name::*;
    use nat::*;

    /// Generate a sequence of natural numbers
    //
    // XXX -- This type is wrong.  TODO -- figure out how to
    // ecode this type correctly, with existentials.  
    fn seq_gen:(
        Thk[0]
            foralli (Y1,X1,Y2):NmSet.
            0 Nat -> 0 F Ref[Y1](Seq[X1][Y2])
    ) = {
        #n. if {{force nat_is_zero} n} {
            ref (@0) roll inj1 ()
        } else {
            let nm = {{force name_of_nat} n}
            let pred = {{force nat_sub} n 1}
            let seq_ref = {{force seq_gen} pred}
            let nil_ref = {ref {nm,(@1)} roll inj1 ()}
            ref nm
                roll inj2 inj2 pack (?,?,?)
                (nm, n, nil_ref, seq_ref)
        }
    }
}
