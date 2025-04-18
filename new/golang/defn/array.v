From New Require Import notation.
From New.golang.defn Require Import typing list.

(** Fixed-size arrays.

NOTE: this library is incomplete, even the signatures here could be wrong.
*)

Module array.
Section defn.
  Context `{ffi_syntax}.

  Definition elem_ref : val :=
    λ: "et" "a" "i", Panic "todo".

  Definition elem_get : val :=
    λ: "et" "a" "i", Panic "todo".

  (* t here is the array type, not the element type *)
  Definition len : val :=
    λ: "t", Panic "todo".

  (* t here is the array type, not the element type *)
  Definition cap : val :=
    λ: "t", len "t".

  Definition slice : val :=
    λ: "t" "a", Panic "todo".

  (* takes a list as input, and makes an array value *)
  Definition literal : val :=
    rec: "literal" "len" "elems" :=
      list.Match "elems" (λ: <>, #()) (λ: "hd" "tl", ("hd", "literal" "tl")).
End defn.
End array.
