From Perennial.goose_lang Require Import lang notation prelude.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context {ext_ty:ext_types ext}.

Local Coercion Var' (s:string) : expr := Var s.

Definition ActReadId : Z := 0.
Definition ActAbortId : Z := 1.
Definition ActCommitId : Z := 2.

Definition NewProph : val :=
  λ: <>, goose_lang.NewProph.

Definition BytesToVal : val :=
  λ: "slice",
    (* Goose alloc lemmas are very wonky, and directly allocating a #() does not work.
       So we allocate a 0 and then store #() in it... *)
    let: "res" := ref #0 in
    "res" <- #();;
    forSlice (byteT) (λ: "idx" "val",
      "res" <- ("val", !"res")
    ) "slice";;
    !"res".

Definition ResolveBytes : val :=
  λ: "p" "slice",
  let: "bytesval" := BytesToVal "slice" in
  goose_lang.ResolveProph "p" "bytesval".

End goose_lang.
