From New Require Export notation.

Module array.
Section defn.
  Context `{ffi_syntax}.

  Fixpoint val_def (x : list val) : val :=
    match x with
    | [] => #()
    | h :: tl => (h, val_def tl)
    end
  .
  Program Definition val := unseal (_:seal (@val_def)). Obligation 1. by eexists. Qed.
  Definition val_unseal : val = _ := seal_eq _.

End defn.
End array.
