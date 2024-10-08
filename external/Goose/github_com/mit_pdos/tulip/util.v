(* autogenerated from github.com/mit-pdos/tulip/util *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.

Section code.
Context `{ext_ty: ext_types}.

Definition NextAligned: val :=
  rec: "NextAligned" "current" "interval" "low" :=
    let: "delta" := ref (zero_val uint64T) in
    let: "rem" := "current" `rem` "interval" in
    (if: "rem" < "low"
    then "delta" <-[uint64T] ("low" - "rem")
    else "delta" <-[uint64T] (("interval" + "low") - "rem"));;
    std.SumAssumeNoOverflow "current" (![uint64T] "delta").

Definition swap: val :=
  rec: "swap" "ns" "i" "j" :=
    let: "tmp" := SliceGet uint64T "ns" "i" in
    SliceSet uint64T "ns" "i" (SliceGet uint64T "ns" "j");;
    SliceSet uint64T "ns" "j" "tmp";;
    #().

Definition Sort: val :=
  rec: "Sort" "ns" :=
    let: "i" := ref_to uint64T #1 in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (slice.len "ns")); (λ: <>, Skip) := λ: <>,
      let: "j" := ref_to uint64T (![uint64T] "i") in
      Skip;;
      (for: (λ: <>, (![uint64T] "j") > #0); (λ: <>, Skip) := λ: <>,
        (if: (SliceGet uint64T "ns" ((![uint64T] "j") - #1)) ≤ (SliceGet uint64T "ns" (![uint64T] "j"))
        then Break
        else
          swap "ns" ((![uint64T] "j") - #1) (![uint64T] "j");;
          "j" <-[uint64T] ((![uint64T] "j") - #1);;
          Continue));;
      "i" <-[uint64T] ((![uint64T] "i") + #1);;
      Continue);;
    #().

End code.
