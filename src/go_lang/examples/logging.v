From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Export ffi.disk.
From Perennial.go_lang Require Import proofmode notation.

Existing Instances disk_op disk_model disk_semantics disk_interp.

Coercion Var' (s: string) : expr := Var s.

(** Lightweight struct library: access field offsets within pairs by name rather
than using prod projections. *)

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

Ltac make_structF desc fname :=
  let f := eval compute [desc get_field rev app get_field_e fields String.eqb Ascii.eqb eqb]
  in (get_field desc fname) in
      lazymatch f with
      | context[LitUnit] => fail "struct" desc "does not have field" fname
      | _ => exact f
      end.

Notation "'structF!' desc fname" := (ltac:(make_structF desc fname))
                                    (at level 0, desc, fname at next level, only parsing) : val_scope.

(** Slice library, for manipulating (pointer, len) structs. *)

Definition sliceS := struct ["p"; "len"].

(*
Eval compute in get_field sliceS "p".
Eval compute in get_field sliceS "len".
*)

Definition NewByteSlice: val :=
  λ: "sz",
  let: "p" := AllocN "sz" #(LitByte 0) in
  ("p", "sz").

Definition SlicePtr: val := structF! sliceS "p".
Definition SliceLen: val := structF! sliceS "len".

Definition For (v:string) (bound:expr) (body:expr) : expr :=
  (rec: "__loop" v :=
     if: v < bound then body v;; "__loop" (v + #1) else #()) #0.

Notation "'for:' v < b := e" := (For v%string b%E e%E)
  (at level 200, v at level 1, b at level 1, e at level 200,
   format "'[' 'for:'  v  <  b  :=  '/  ' e ']'") : expr_scope.

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

Definition logS := struct ["log_sz"; "disk_sz"].

Definition write_hdr: val :=
  λ: "log",
    let: "hdr" := AllocN #4096 #(LitByte 0) in
    EncodeInt "log_sz" "hdr";;
    EncodeInt "disk_sz" ("hdr" +ₗ #8);;
    ExternalOp Write (#0, "hdr").

Definition init: val :=
  λ: "disk_sz",
  if: "disk_sz" < #1 then NONE
  else
    let: "log" := (#0, "disk_sz") in
    write_hdr "log";;
    SOME "log".

Definition LogSize: val := structF! logS "log_sz".
Definition DiskSize: val := structF! logS "disk_sz".

Definition get: val :=
  λ: "log" "i",
  let: "sz" := LogSize "log" in
  if: "i" < "sz"
  then SOME (ExternalOp Read (#1+"i"))
  else NONE.

Definition write_all: val :=
  λ: "bks" "off",
  let: "len" := SliceLen "bks" in
  for: "i" < "len" :=
    let: "bk" := SliceGet "bks" "i" in
    ExternalOp Write ("off" + "i", "bk").

Definition append: val :=
  λ: "log" "bks",
  if: #1 + LogSize "log" + SliceLen "bks" ≥ DiskSize "log" then
    NONEV
  else
    write_all "bks" (#1 + LogSize "log");;
    let: "new_log" := (LogSize "log" + SliceLen "bks", DiskSize "log") in
    write_hdr "new_log";;
    SOME "new_log".

Definition reset: val :=
  λ: "log",
  let: "new_log" := (#0, DiskSize "log") in
  write_hdr "new_log";;
  "new_log".
