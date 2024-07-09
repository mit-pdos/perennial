From iris.proofmode Require Import coq_tactics reduction.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.goose_lang Require Import proofmode lifting.
From New.golang.defn Require Export struct.
From New.golang.theory Require Import mem typing exception.
From Perennial.Helpers Require Import NamedProps.

Module struct.
Section goose_lang.
Context `{ffi_syntax}.

Implicit Types (d : struct.descriptor).
Infix "=?" := (String.eqb).
(* FIXME: what does _f mean? Want better name. *)
Fixpoint get_field_f d f0: val -> val :=
  λ v, match d with
       | [] => #()
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 => if f =? f0 then v1 else get_field_f fs f0 v2
         | _ => #()
         end
       end.

Fixpoint set_field_f d f0 fv: val -> val :=
  λ v, match d with
       | [] => v
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 =>
           if f =? f0
           then PairV fv v2
           else PairV v1 (set_field_f fs f0 fv v2)
         | _ => v
         end
       end.

Definition field_ref_f d f0 l: loc := l +ₗ (struct.field_offset d f0).1.

Class Wf (d : struct.descriptor) : Set :=
  { descriptor_NoDup: NoDup d.*1; }.

End goose_lang.
End struct.

Notation "l ↦s[ d :: f ] dq v" := (struct.field_ref_f d f l ↦[struct.field_ty d f]{dq} v)%I
  (at level 50, dq custom dfrac at level 70, d at level 59, f at level 59,
     format "l  ↦s[ d  ::  f ] dq  v").

Definition option_descriptor_wf (d : struct.descriptor) : option (struct.Wf d).
  destruct (decide (NoDup d.*1)); [ apply Some | apply None ].
  constructor; auto.
Defined.

Definition proj_descriptor_wf (d : struct.descriptor) :=
  match option_descriptor_wf d as mwf return match mwf with
                                             | Some _ => struct.Wf d
                                             | None => True
                                             end  with
  | Some pf => pf
  | None => I
  end.

Global Hint Extern 3 (struct.Wf ?d) => exact (proj_descriptor_wf d) : typeclass_instances.

Section lemmas.

Context `{heapGS Σ}.

Local Fixpoint struct_big_fields_rec l dq (d : struct.descriptor) (fs : struct.descriptor)
      (v : val): iProp Σ :=
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

Theorem struct_fields_split l q d {dwf: struct.Wf d} v :
  typed_pointsto l q (structT d) v ⊣⊢ struct_fields l q d v.
Proof.
Admitted.

End lemmas.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance pure_struct_field_ref d f (l : loc) :
  WpPureExec True 2 (struct.field_ref d f #l) #(struct.field_ref_f d f l).
Proof.
  split; first done.
  unfold struct.field_ref. cbn.
  eapply pure_exec_impl; first shelve.
  repeat (eapply pure_exec_S; first (simpl; tc_search_pure_exec_ctx)).
  intros _.
  constructor.
  Unshelve.
  2:{ refine True. }
  intros; split; first done.
  split; last done.
  unfold bin_op_eval.
  simpl.
  rewrite /loc_add /addr_id /=.
  repeat f_equal.
  word.
Qed.

End wps.
