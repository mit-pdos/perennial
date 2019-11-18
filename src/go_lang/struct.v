From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Import notation.
From Perennial.go_lang Require Import typing.

(** * Lightweight struct library

    Access field offsets within pairs by name rather than using Fst and Snd. *)

Record descriptor :=
  mkStruct { fields: list (string*ty); }.

(* Check eq_refl : (#0, #1, #2)%E = ((#0, #1), #2)%E. *)

Section go_lang.
  Context `{ffi_sem: ext_semantics}.

Fixpoint getField_e (f0: string) (rev_fields: list (string*ty)) (se: expr): expr :=
  match rev_fields with
  | [] => LitV LitUnit
  | [f] => if String.eqb (fst f) f0 then se else #()
  | f::fs => if String.eqb (fst f) f0 then Snd se else getField_e f0 fs (Fst se)
  end.

Definition getField (d:descriptor) f : val :=
  λ: "v", getField_e f (rev d.(fields)) (Var "v").

Fixpoint assocl_lookup {A} (field_vals: list (string * A)) (f0: string) : option A :=
  match field_vals with
  | [] => None
  | (f, v)::fs => if String.eqb f f0 then Some v else assocl_lookup fs f0
  end.

Fixpoint build_struct_val
         (field_vals: list (string * expr))
         (rev_fields: list (string * ty)) : option expr :=
  match rev_fields with
  | [] => None
  | [f] => assocl_lookup field_vals (fst f)
  | f::fs => match assocl_lookup field_vals (fst f) with
           | Some v => match build_struct_val field_vals fs with
                      | Some vs => Some (vs, v)%E
                      | None => None
                      end
           | None => None
           end
  end.

Definition buildStruct (d:descriptor) (fvs: list (string*expr)) : expr :=
  match build_struct_val fvs (rev d.(fields)) with
  | Some v => v
  | None => LitV LitUnit
  end.

Fixpoint struct_ty_prod (rev_fields: list (string*ty)) : ty :=
  match rev_fields with
  | nil => unitT
  | [f] => snd f
  | f::fs => struct_ty_prod fs * snd f
  end.

Definition structTy (d:descriptor) : ty :=
  struct_ty_prod (rev (fields d)).

Fixpoint ty_size (t:ty) : nat :=
  match t with
  | prodT t1 t2 => ty_size t1 + ty_size t2
  (* this gives unit values space, which seems fine *)
  | _ => 1
  end.

Fixpoint load_ty (t:ty) (e:expr) : expr :=
  match t with
  | prodT t1 t2 => (load_ty t1 e, load_ty t2 (e +ₗ #(ty_size t1)))
  | _ => !e
  end.

Definition loadStruct (d:descriptor) : val :=
  λ: "p", load_ty (structTy d) (Var "p").

Fixpoint field_offset (fields: list (string*ty)) f0 : (Z * ty) :=
  match fields with
  | nil => (-1, unitT)
  | f::fs => if String.eqb (fst f) f0 then (0, snd f)
           else let (off, t) := field_offset fs f0 in
                (ty_size (snd f) + off, t)
  end%Z.

Definition loadField (d:descriptor) (f:string) : val :=
  let (off, t) := field_offset d.(fields) f in
  λ: "p", load_ty t (Var "p" +ₗ #off).

End go_lang.

Declare Reduction getField := cbv [getField rev fst snd app getField_e fields String.eqb Ascii.eqb eqb].

Ltac make_structF desc fname :=
  let f := eval unfold desc in (getField desc fname) in
  let f := eval getField in f in
      lazymatch f with
      | context[LitUnit] => fail "struct" desc "does not have field" fname
      | _ => exact f
      end.

(* we don't use this, but just to document the relevant reduction *)
Declare Reduction buildStruct :=
  cbv [buildStruct
       build_struct_val
       rev app assocl_lookup
       String.eqb Ascii.eqb eqb].

Module struct.
  Notation new := mkStruct.
  Notation mk := buildStruct.
  Notation get := getField.
  (* TODO: load/loadF could probably use better names *)
  Notation load := loadStruct.
  Notation loadF := loadField.
  Notation t := structTy.
End struct.

Notation "'structF!' desc fname" := (ltac:(make_structF desc fname))
                                    (at level 0, desc, fname at next level, only parsing).

Notation "f :: t" := (@pair string ty f%string t%ht).
Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.
