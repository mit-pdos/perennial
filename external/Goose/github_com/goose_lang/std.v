(* autogenerated from github.com/goose-lang/std *)
From Perennial.goose_lang Require Import prelude.
Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

(* Test if the two byte slices are equal. *)
Definition BytesEqual: val :=
  rec: "BytesEqual" "x" "y" :=
    let: "xlen" := slice.len "x" in
    (if: "xlen" ≠ slice.len "y"
    then #false
    else
      let: "i" := ref_to uint64T #0 in
      let: "retval" := ref_to boolT #true in
      Skip;;
      (for: (λ: <>, ![uint64T] "i" < "xlen"); (λ: <>, Skip) := λ: <>,
        (if: SliceGet byteT "x" (![uint64T] "i") ≠ SliceGet byteT "y" (![uint64T] "i")
        then
          "retval" <-[boolT] #false;;
          Break
        else
          "i" <-[uint64T] ![uint64T] "i" + #1;;
          Continue));;
      ![boolT] "retval").

(* Compute the sum of two numbers, `Assume`ing that this does not overflow.
   *Use with care*, assumptions are trusted and should be justified! *)
Definition SumAssumeNoOverflow: val :=
  rec: "SumAssumeNoOverflow" "x" "y" :=
    control.impl.Assume ("x" + "y" ≥ "x");;
    "x" + "y".

End code.
