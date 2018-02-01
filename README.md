# IODyn: A functional language for implicitly-incremental programs with dynamic input and output collections [![Travis](https://api.travis-ci.org/cuplv/iodyn-lang.rust.svg?branch=master)](https://travis-ci.org/cuplv/iodyn-lang.rust)


## Examples

### Sequences

#### type

```text
type Seq = (
            rec Seq.#X.#Y.
            (+ Vec 
             + (exists (X1,X2,X3)   :NmSet | (X1%X2%X3=X).
                exists (Y1,Y2,Y3,Y4):NmSet | (Y1%Y2%Y3%Y4=Y).
                x Nm[X1] x Nat
                x Ref[Y1](Seq[X2][Y2])
                x Ref[Y3](Seq[X3][Y4]))
            )
)
```

#### max

TODO

#### filter

```text
let rec filter:(
            Thk[0] foralli (X,Y):NmSet.
                (Seq[X][Y] Nat) -> (
                    (Thk[0] Nat -> (F Bool |> {0;0}) |> {0;0}) ->
                    (F Nat |> {(#x.{x,@1} % {x,@2}) X; 0})
                    |> {0;0}
                ) |> {0;0}
        ) = {
            #seq. #f. unroll match seq {
                vec => { {force vec_filter} f vec }
                bin => {
                    let (n,lev,l,r) = {ret bin}
                    let (rsl, sl) = { memo{n,(@1)}{ {force filter} f {!l} } }
                    let (rsr, sr) = { memo{n,(@2)}{ {force filter} f {!r} } }
                    // if left is empty, return the right
                    if {{force is_empty} sl} { ret sr }
                    else { // if right is empty, return the left
                        if {{force is_empty} sr} { ret sl }
                        else {
                            // neither are empty; construct SeqBin node:
                            ret roll inj2 (n,lev,rsl,rsr)
                        }
                    }
                }
            }
}
```
