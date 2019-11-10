From Perennial.go_lang Require Export lang notation.
From Perennial.go_lang Require Import notation struct.

(** * Slice library

    Intended to model Go slices. We don't track slice capacity because our model
    soundly approximates slices as never having extra capacity.
 *)

Module slice.
  Definition sliceS := mkStruct ["p"; "len"].
  Section fields.
    Context {ext:ext_op}.
    Definition ptr := structF! sliceS "p".
    Definition len: val := structF! sliceS "len".
  End fields.
End slice.

(*
Eval compute in get_field sliceS "p".
Eval compute in get_field sliceS "len".
*)
Section go_lang.
  Context `{ffi_sem: ext_semantics}.

  Definition Var' s : @expr ext := Var s.
  Local Coercion Var' : string >-> expr.

Definition NewByteSlice: val :=
  λ: "sz",
  let: "p" := AllocN "sz" #(LitByte 0) in
  ("p", "sz").

Definition MemCpy: val :=
  λ: "dst" "src" "n",
    for: "i" < "n" :=
    ("dst" +ₗ "i") <- !("src" +ₗ "i").

(* explicitly recursive version of MemCpy *)
Definition MemCpy_rec: val :=
  rec: "memcpy" "dst" "src" "n" :=
    if: "n" = #0
    then #()
    else "dst" <- !"src";;
         "memcpy" ("dst" +ₗ #1) ("src" +ₗ #1) ("n" - #1).

Definition SliceSkip: val :=
  λ: "s" "n", (slice.ptr "s" +ₗ "n", slice.len "s" - "n").

Definition SliceTake: val :=
  λ: "s" "n", if: slice.len "s" < "n"
              then #() (* TODO: this should be Panic *)
              else (slice.ptr "s", "n").

Definition SliceGet: val :=
  λ: "s" "i",
  !(slice.ptr "s" +ₗ "i").

Definition SliceAppend: val :=
  λ: "s1" "s2",
  let: "p" := AllocN (slice.len "s1" + slice.len "s2") #() in
  MemCpy "p" (slice.ptr "s1");;
  MemCpy ("p" +ₗ slice.len "s2") (slice.ptr "s2");;
  (* TODO: unsound, need to de-allocate s1.p *)
  ("p", slice.len "s1" + slice.len "s2").

End go_lang.
