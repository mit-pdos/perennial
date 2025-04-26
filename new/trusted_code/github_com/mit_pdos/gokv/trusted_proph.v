From New.golang Require Import defn.

Section defs.
Context `{ffi_syntax}.

Definition NewProph : val :=
  λ: <>, goose_lang.NewProph.

Definition BytesToVal : val :=
  λ: "sl",
    let: "res" := ref list.Nil in
    slice.for_range #byteT "slice" (λ: "idx" "val",
      "res" <- list.Cons "val" (!"res")
    ) "slice";;;
    !"res".

Definition ResolveBytes : val :=
  λ: "p" "slice",
  let: "bytesval" := BytesToVal "slice" in
  goose_lang.ResolveProph "p" "bytesval".

End defs.
