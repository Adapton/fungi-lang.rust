# IODyn: A functional language for implicitly-incremental programs with dynamic input and output collections [![Travis](https://api.travis-ci.org/cuplv/iodyn-lang.rust.svg?branch=master)](https://travis-ci.org/cuplv/iodyn-lang.rust)

## IODyn is an ML-like language with collections

IODyn is a functional language, in the ML family of languages (SML, OCaml, Elm, etc.).  As with other languages in this family, IODyn consists of a typed core calculus, with functions and algebraic data types.  Further, we enrich this core calculus with a collections library over sequences, sets, finite maps and graphs (in progress).  Finally, we give well-typed, well-annotated programs in this language an implicitly-incremental semantics, via translation to Fungi, our low-level core calculus for functional programs that name their own cached dependency graphs.

## Fungi is a core calculus for functional programs that name their own cached dependency graphs

Fungi serves as the target language for IODyn.  Unlike IODyn, the incremental features of Fungi are explicit.  In particular, Fungi provides language affordances for
 - _first-class names_, 
 - _first class name-functions_, 
 - input/output collections whose types are indexed by _sets of names_ (e.g., to uniquely identify positions in a list), and 
 - functions whose types are indexed by what cached data and computations they read and write.
 Though the semantics of Fungi are effectful, wherein it allocates programmer-named values and computations, and reads these objects from memory later, **the behavior of Fungi is functional**: the key invariant of its type-and-effects system.
 
 More precisely, Fungi provides two languages: One for the **Archivist** (the functional subset), and an imperative "wrapper" language for the **Editor**, who is permitted to mutate the Archivist's input, and then indicate where the output of archivist computations should be incrementally repaired, on demand.

## Fungi Examples

### Sequences

A recursive algebraic type for sequences, as balanced level trees

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

### filter a sequence by an element-wise predicate

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
