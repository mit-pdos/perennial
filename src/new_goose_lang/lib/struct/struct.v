From iris.proofmode Require Import coq_tactics reduction.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.goose_lang Require Import proofmode.
From Perennial.new_goose_lang.lib Require Export typed_mem struct.impl.
From Perennial.Helpers Require Import NamedProps.

Notation "l ↦s[ d :: f ] dq v" := (struct.fieldRef_f d f l ↦[struct.fieldTy d f]{dq} v)%I
  (at level 50, dq custom dfrac at level 70, d at level 59, f at level 59,
     format "l  ↦s[ d :: f ] dq  v").

Section lemmas.
Context `{heapGS Σ}.
(* FIXME: move this *)
Local Fixpoint struct_big_fields_rec l dq (d: descriptor) (fs:descriptor) (v:val): iProp Σ :=
  match fs with
  | [] => "_" ∷ ⌜v = #()⌝
  | (f,t)::fs =>
    match v with
    | PairV v1 v2 => ("H" ++ f) ∷ l ↦s[d :: f]{dq} v1 ∗
                    struct_big_fields_rec l dq d fs v2
    | _ => False
    end
  end.

Definition struct_fields l dq d v : iProp Σ := struct_big_fields_rec l dq d d v.

Theorem struct_fields_split l q d {dwf: struct.wf d} v :
  typed_pointsto l q (structT d) v ⊣⊢ struct_fields l q d v.
Proof.
Admitted.

End lemmas.
