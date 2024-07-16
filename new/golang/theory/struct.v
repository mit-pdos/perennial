From Perennial.goose_lang Require Import proofmode lifting.
From New.golang.defn Require Export struct.
From New.golang.theory Require Import mem typing exception list vmap.
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

Definition field_ref_f t f0 l: loc := l +ₗ (struct.field_offset t f0).1.

Class Wf (d : struct.descriptor) : Set :=
  { descriptor_NoDup: NoDup d.*1; }.

End goose_lang.
End struct.

Notation "l ↦s[ t :: f ] dq v" := (struct.field_ref_f t f l ↦[struct.field_ty t f]{dq} v)%I
  (at level 50, dq custom dfrac at level 70, t at level 59, f at level 59,
     format "l  ↦s[ t  ::  f ] dq  v").

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

Fixpoint struct_fields l dq (t : go_type) (fs : struct.descriptor)
      (v : val): iProp Σ :=
  match fs with
  | [] => "_" ∷ ⌜v = #()⌝
  | (f,t')::fs =>
    match v with
    | PairV v1 v2 => ("H" ++ f) ∷ l ↦s[t :: f]{dq} v1 ∗
                    struct_fields l dq t fs v2
    | _ => False
    end
  end.

(* FIXME: could try stating this with (structT d) substituted in. The main
   concern is that it will result in t getting unfolded. *)
Theorem struct_fields_split l q t d {Ht : t = structT d} {dwf : struct.Wf d} v :
  typed_pointsto l q t v ⊣⊢ struct_fields l q t d v.
Proof.
  intros. subst.
Admitted.

End lemmas.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance pure_struct_field_ref t f (l : loc) :
  WpPureExec True 2 (struct.field_ref t f #l) #(struct.field_ref_f t f l).
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

Lemma struct_fields_val_empty :
  {[]}%E = struct.fields_val ∅.
Proof. by rewrite struct.fields_val_unseal. Qed.

Lemma wp_struct_make_field {s E} (fvs : gmap string val) k (v : val) Φ :
  Φ (struct.fields_val $ (<[k := v]> fvs))%stdpp -∗
  WP (<[#(str k) := v]> (struct.fields_val fvs))%E @ s ; E {{ Φ }}
.
Proof.
  rewrite struct.fields_val_unseal /struct.fields_val_def.
  iIntros "Hwp". wp_apply wp_vmap_Insert.
  erewrite -> kmap_insert.
  2:{ intros??. by inversion 1. }
  simpl. iFrame.
Qed.

Definition is_structT (t : go_type) : Prop :=
  match t with
  | structT d => True
  | _ => False
  end.

Lemma wp_struct_make {s E} (t : go_type) (m : gmap string val) Φ :
  is_structT t →
  Φ (struct.val t m) -∗
  WP struct.make t (struct.fields_val m) @ s ; E {{ Φ }}.
Proof.
  rewrite struct.make_unseal struct.val_unseal.
  intros Ht. destruct t; try by exfalso.
  iIntros "HΦ".
  unfold struct.make_def.
  iInduction decls as [] "IH" forall (Φ).
  - wp_pures. simpl. done.
  - destruct a. wp_pures.
    rewrite struct.fields_val_unseal /struct.fields_val_def.
    wp_apply wp_vmap_Get.
    change (#(str s0)) with (LitV ∘ LitString $ s0).
    erewrite lookup_kmap.
    2:{ intros??. by inversion 1. }
    unfold struct.val_def.
    destruct (m !! s0) eqn:Hlookup.
    + wp_pures. wp_apply "IH"; first done.
      wp_pures. done.
    + wp_pures. wp_apply "IH"; first done.
      wp_pures. done.
Qed.
End wps.

Ltac wp_struct_make :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (App (Val (struct.make ?t)) ?fvs) ?Q) =>
      rewrite struct_fields_val_empty; (* FIXME: this might rewrite too much *)
      repeat wp_apply wp_struct_make_field;
      rewrite insert_empty;
      wp_apply wp_struct_make; [constructor|]
  | _ => fail "wp_struct_make: next step is not [struct.make]"
  end.
