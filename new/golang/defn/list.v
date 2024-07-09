From Perennial.goose_lang Require Export lang notation.

Module list.
Section defn.
  Context `{ffi_syntax}.
  Local Coercion Var' (s:string) : expr := Var s.

  Definition Cons_def : val := λ: "h" "tl", InjR ("h", "tl").
  Program Definition Cons := unseal (_:seal (@Cons_def)). Obligation 1. by eexists. Qed.
  Definition Cons_unseal : Cons = _ := seal_eq _.

  Definition Match : val :=
    λ: "nilCase" "consCase" "l",
      Match "l"
        <> ("nilCase" #())
        "x" (let: ("hd", "tl") := "x" in "consCase" "hd" "tl").

  Fixpoint val_def (x : list val) : val :=
    match x with
    | [] => InjLV #()
    | h :: tl => (InjRV (h, val_def tl))
    end.
  Program Definition val := unseal (_:seal (@val_def)). Obligation 1. by eexists. Qed.
  Definition val_unseal : val = _ := seal_eq _.

End defn.
End list.

Notation "[ ]" := (list.val nil) (only parsing) : expr_scope.
Notation "[ x ]" := (list.Cons x []%E) : expr_scope.
Notation "[ x ; y ; .. ; z ]" := (list.Cons x (list.Cons y .. (list.Cons z []%E) ..)) : expr_scope.
