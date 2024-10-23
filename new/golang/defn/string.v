From New.golang.defn Require Export notation.
From New.golang.defn Require Export typing slice.

Section defn.
  Context `{ffi_syntax}.
  Definition string__mset : list (string * val) := [].
End defn.

Module string.
Section defn.
  Context `{ffi_syntax}.

  Local Definition to_bytes_aux: val :=
    (rec: "to_bytes" "i" "s" :=
       if: (Var "i") = #(W64 0)
       then #slice.nil
       else
         let: "j" := "i" - #(W64 1) in
         (slice.append byteT ("to_bytes" "j" "s") (StringGet "s" "j")))
  .

  Definition to_bytes_def : val :=
    rec: "f" "s" :=
      (* assume that IsNoStringOverflow *)
      if: (IsNoStringOverflow "s") then
        to_bytes_aux (StringLength "s") "s"
      else "f".
  Program Definition to_bytes := unseal (_:seal (@to_bytes_def)). Obligation 1. by eexists. Qed.
  Definition to_bytes_unseal : to_bytes = _ := seal_eq _.

  Definition from_bytes : val :=
    (rec: "from_bytes" "b" :=
       if: (slice.len "b") = #(W64 0)
       then (# "")
       else (to_string ![byteT] (slice.elem_ref byteT "b" #(W64 0))) +
              ("from_bytes" (slice.slice byteT "b" #(W64 1) (slice.len "b")))).

End defn.
End string.
