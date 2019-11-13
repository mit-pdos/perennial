From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Import notation.

(** * Lightweight struct library

    Access field offsets within pairs by name rather than using Fst and Snd. *)

Record descriptor :=
  mkStruct { fields: list string; }.

(* Check eq_refl : (#0, #1, #2)%E = ((#0, #1), #2)%E. *)

Section go_lang.
  Context `{ffi_sem: ext_semantics}.

  Definition Var' s : @expr ext := Var s.
  Local Coercion Var' : string >-> expr.

Fixpoint get_field_e (f0: string) (rev_fields: list string): expr :=
  match rev_fields with
  | [] => LitV LitUnit
  | [f] => if String.eqb f f0 then "v" else #()
  | f::fs => if String.eqb f f0 then Snd "v" else Fst (get_field_e f0 fs)
  end.

Definition get_field (d:descriptor) f : val :=
  λ: "v", get_field_e f (rev d.(fields)).

Fixpoint assocl_lookup {A} (field_vals: list (string * A)) (f0: string) : option A :=
  match field_vals with
  | [] => None
  | (f, v)::fs => if String.eqb f f0 then Some v else assocl_lookup fs f0
  end.

Fixpoint build_struct_val
         (field_vals: list (string * expr))
         (rev_fields: list string) : option expr :=
  match rev_fields with
  | [] => None
  | [f] => assocl_lookup field_vals f
  | f::fs => match assocl_lookup field_vals f with
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

End go_lang.

Declare Reduction get_field := cbv [get_field rev app get_field_e fields String.eqb Ascii.eqb eqb].

Ltac make_structF desc fname :=
  let f := eval unfold desc in (get_field desc fname) in
  let f := eval get_field in f in
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

Notation "'structF!' desc fname" := (ltac:(make_structF desc fname))
                                    (at level 0, desc, fname at next level, only parsing).

Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.
