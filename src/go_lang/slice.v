From Perennial.go_lang Require Export lang notation.
From Perennial.go_lang Require Import notation struct.

(** * Slice library

    Intended to model Go slices. We don't track slice capacity because our model
    soundly approximates slices as never having extra capacity.
 *)

Definition sliceS := struct ["p"; "len"].

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

Definition SlicePtr: val := structF! sliceS "p".
Definition SliceLen: val := structF! sliceS "len".

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
  λ: "s" "n", (SlicePtr "s" +ₗ "n", SliceLen "s" - "n").

Definition SliceTake: val :=
  λ: "s" "n", if: SliceLen "s" < "n"
              then #() (* TODO: this should be Panic *)
              else (SlicePtr "s", "n").

Definition SliceGet: val :=
  λ: "s" "i",
  !(SlicePtr "s" +ₗ "i").

Definition SliceAppend: val :=
  λ: "s1" "s2",
  let: "p" := AllocN (SliceLen "s1" + SliceLen "s2") #() in
  MemCpy "p" (SlicePtr "s1");;
  MemCpy ("p" +ₗ SliceLen "s2") (SlicePtr "s2");;
  (* TODO: unsound, need to de-allocate s1.p *)
  ("p", SliceLen "s1" + SliceLen "s2").

End go_lang.
