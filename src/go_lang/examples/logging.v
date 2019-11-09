From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Export ffi.disk.
From Perennial.go_lang Require Import proofmode notation.

Existing Instances disk_op disk_model disk_semantics disk_interp.

Coercion Var' (s: string) : expr := Var s.

Record descriptor :=
  struct { fields: list string; }.

(* Check eq_refl : (#0, #1, #2)%E = ((#0, #1), #2)%E. *)

Fixpoint get_field_e (f0: string) (rev_fields: list string): expr :=
  match rev_fields with
  | nil => #()
  | [f] => if String.eqb f f0 then "v" else #()
  | f::fs => if String.eqb f f0 then Snd "v" else Fst (get_field_e f0 fs)
  end.

Definition get_field (d:descriptor) f : val :=
  λ: "v", get_field_e f (rev d.(fields)).

Definition sliceS := struct ["p"; "len"].

(*
Eval compute in get_field sliceS "p".
Eval compute in get_field sliceS "len".
*)

Definition NewByteSlice: val :=
  λ: "sz",
  let: "p" := AllocN "sz" #(LitByte 0) in
  ("p", "sz").

Ltac make_structF desc fname :=
  let f := eval compute [desc get_field rev app get_field_e fields String.eqb Ascii.eqb eqb]
  in (get_field desc fname) in
      lazymatch f with
      | context[LitUnit] => fail "struct" desc "does not have field" fname
      | _ => exact f
      end.

Notation "'structF!' desc fname" := (ltac:(make_structF desc fname))
                                    (at level 0, desc, fname at next level, only parsing) : val_scope.

Definition SlicePtr: val := structF! sliceS "p".
Definition SliceLen: val := structF! sliceS "len".

Definition MemCpy: val :=
  rec: "memcpy" "dst" "src" "n" :=
    if: "n" = #0
    then #()
    else "dst" <- "src";;
         "memcpy" ("dst" +ₗ #1) ("src" +ₗ #1) ("n" - #1).

Definition SliceAppend: val :=
  λ: "s1" "s2",
  let: "p" := AllocN (SliceLen "s1" + SliceLen "s2") #() in
  MemCpy "p" (SlicePtr "s1");;
  MemCpy ("p" +ₗ SliceLen "s2") (SlicePtr "s2");;
  (* TODO: unsound, need to de-allocate s1.p *)
  ("p", SliceLen "s1" + SliceLen "s2").

Definition logS := struct ["log_sz"; "disk_sz"].

Definition init: val :=
  λ: "disk_sz",
  let: "log_sz" := #0 in
  let: "hdr" := AllocN #4096 #(LitByte 0) in
  EncodeInt "log_sz" "hdr";;
  EncodeInt "disk_sz" ("hdr" +ₗ #8);;
  ExternalOp Write (#0, "hdr");;
  (#0, "disk_sz").
