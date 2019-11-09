From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Import notation.

(** * Lightweight struct library

    Access field offsets within pairs by name rather than using Fst and Snd. *)

Record descriptor :=
  struct { fields: list string; }.

(* Check eq_refl : (#0, #1, #2)%E = ((#0, #1), #2)%E. *)

Section go_lang.
  Context `{ffi_sem: ext_semantics}.

  Definition Var' s : @expr ext := Var s.
  Local Coercion Var' : string >-> expr.

Fixpoint get_field_e (f0: string) (rev_fields: list string): expr :=
  match rev_fields with
  | nil => LitV LitUnit
  | [f] => if String.eqb f f0 then "v" else #()
  | f::fs => if String.eqb f f0 then Snd "v" else Fst (get_field_e f0 fs)
  end.

Definition get_field (d:descriptor) f : val :=
  λ: "v", get_field_e f (rev d.(fields)).

End go_lang.

Ltac make_structF desc fname :=
  let f := eval compute [desc get_field rev app get_field_e fields String.eqb Ascii.eqb eqb]
  in (get_field desc fname) in
      lazymatch f with
      | context[LitUnit] => fail "struct" desc "does not have field" fname
      | _ => exact f
      end.

Notation "'structF!' desc fname" := (ltac:(make_structF desc fname))
                                    (at level 0, desc, fname at next level, only parsing) : val_scope.
