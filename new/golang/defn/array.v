From New Require Export notation.
From New.golang.defn Require Import typing.

Module array.
Section defn.
  Context `{ffi_syntax}.

  Definition elem_ref (t : go_type) : val.
  Admitted.

  Definition elem_get (t : go_type) : val.
  Admitted.

  Definition len (t : go_type) : val.
  Admitted.

  Definition cap (t : go_type) : val.
  Admitted.

  Definition slice : val.
  Admitted.

  (* takes a list as input, and makes an array value *)
  Definition literal : val :=
    rec: "literal" "len" "elems" :=
      list.Match (λ: <>, #()) (λ: "hd" "tl", ("hd", "literal" "tl")).
End defn.
End array.
