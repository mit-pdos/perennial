From Perennial.goose_lang Require Import lifting.
From New.golang.defn Require Export struct.
From New.golang.theory Require Import typed_pointsto exception list typing dynamic_typing.
From Perennial.Helpers Require Import NamedProps.
From RecordUpdate Require Export RecordUpdate.
From Perennial Require Import base.

Set Default Proof Using "Type".

Module struct.
Section goose_lang.
Context `{ffi_syntax}.

Implicit Types (d : struct.descriptor).
Infix "=?" := (ByteString.eqb).

(* FIXME: what does _f mean? Want better name. *)
Definition field_offset_f (t : go_type) f : (w64 * go_type) :=
  let missing := W64 (2^64-1) in
  match t with
  | structT d =>
      (fix field_offset_struct (d : struct.descriptor) : (w64 * go_type) :=
         match d with
         | [] => (missing, badT)
         | (f',t)::fs => if f' =? f then (W64 0, t)
                         else match field_offset_struct fs with
                              | (off, t') => (word.add (go_type_size t) off, t')
                              end
         end) d
  | _ => (missing, badT)
  end .

Definition field_ty_f t f : go_type := (field_offset_f t f).2.

Definition field_get_f t f0: val -> val :=
  match t with
  | structT d =>
      (fix go d v :=
         match d with
         | [] => #()
         | (f,_)::fs =>
             match v with
             | PairV v1 v2 => if f =? f0 then v1 else go fs v2
             | _ => #()
             end
         end) d
  | _ => λ v, LitV LitPoison
  end.

Definition field_set_f t f0 fv: val -> val :=
  match t with
  | structT d =>
      (fix go d v :=
         match d with
         | [] => v
         | (f,_)::fs =>
             match v with
             | PairV v1 v2 =>
                 if f =? f0
                 then PairV fv v2
                 else PairV v1 (go d v2)
             | _ => v
             end
         end) d
  | _ => λ v, LitV LitPoison
  end
  .

Definition field_ref_f_def t f0 l: loc := l +ₗ uint.Z (field_offset_f t f0).1.
Program Definition field_ref_f := sealed @field_ref_f_def.
Definition field_ref_f_unseal : field_ref_f = _ := seal_eq _.

Class Wf (t : go_type) : Set :=
  {
    descriptor_NoDup: match t with
    | structT d => NoDup d.*1
    | _ => False
    end
  }.

End goose_lang.
End struct.

Notation "l ↦s[ t :: f ] dq v" := (struct.field_ref_f t f l ↦{dq} v)%I
  (at level 50, dq custom dfrac at level 70, t at level 59, f at level 59,
     format "l  ↦s[ t  ::  f ] dq  v").

Definition option_descriptor_wf (d : struct.descriptor) : option (struct.Wf (structT d)).
  destruct (decide (NoDup d.*1)); [ apply Some | apply None ].
  constructor; auto.
Defined.

Definition proj_descriptor_wf (d : struct.descriptor) :=
  match option_descriptor_wf d as mwf return match mwf with
                                             | Some _ => struct.Wf (structT d)
                                             | None => True
                                             end  with
  | Some pf => pf
  | None => I
  end.

(* This hint converts [someStructType] into [structT blah] *)
Global Hint Extern 10 (struct.Wf ?t) => unfold t : typeclass_instances.
Global Hint Extern 3 (struct.Wf (structT ?d)) => exact (proj_descriptor_wf d) : typeclass_instances.

Section lemmas.
Context `{heapGS Σ}.

Class IntoValStructField (f : go_string) (t : go_type) {V Vf : Type} {tf}
  (field_proj : V → Vf)
  `{!IntoVal V} `{!IntoVal Vf}
  `{!IntoValTyped Vf tf}
  :=
  {
    field_proj_eq_field_get : ∀ v, #(field_proj v) = (struct.field_get_f t f #v);
  }.

Definition struct_fields `{!IntoVal V} `{!IntoValTyped V t} l dq
  (fs : struct.descriptor) (v : V) : iProp Σ :=
  [∗ list] '(f, _) ∈ fs,
    ∀ `(H:IntoValStructField f t V Vf tf field_proj), ("H" +:+
                                                         (String.string_of_list_byte $
                                                            w8_to_byte <$> f)) ∷ l ↦s[t :: f]{dq} (field_proj v).

Lemma struct_val_inj d fvs1 fvs2 :
  struct.val_aux (structT d) fvs1 = struct.val_aux (structT d) fvs2 →
  ∀ f, In f d.*1 →
       match (alist_lookup_f f fvs1), (alist_lookup_f f fvs2) with
       | Some v1, Some v2 => v1 = v2
       | _, _ => True
       end.
Proof.
  rewrite struct.val_aux_unseal.
  induction d as [|[]].
  { done. }
  intros Heq ? [].
  - subst. simpl in Heq.
    injection Heq as ??.
    repeat destruct alist_lookup_f; naive_solver.
  - simpl in *. injection Heq as ??. by apply IHd.
Qed.

Class StructFieldsSplit `{!IntoVal V} `{!IntoValTyped V t} {dwf : struct.Wf t}
                        (dq : dfrac) (l : loc) (v : V) (Psplit : iProp Σ)
  :=
  {
    struct_fields_split : l ↦{dq} v ⊢ Psplit ;
    struct_fields_combine : Psplit ⊢ l ↦{dq} v
  }.

Theorem struct_fields_acc_update f t V Vf
  l dq {dwf : struct.Wf t} (v : V)
  `{IntoValStructField f t V Vf tf field_proj} `{!SetterWf field_proj} :
  typed_pointsto l dq v -∗
  l ↦s[t :: f]{dq} (field_proj v) ∗
  (∀ fv', l ↦s[t :: f]{dq} fv' -∗
          typed_pointsto l dq (set field_proj (λ _, fv') v)).
Proof.
Admitted.

Theorem struct_fields_acc f t V Vf
  l dq {dwf : struct.Wf t} (v : V)
  `{IntoValStructField f t V Vf tf field_proj} `{!SetterWf field_proj} :
  typed_pointsto l dq v -∗
  l ↦s[t :: f]{dq} (field_proj v) ∗
  (l ↦s[t :: f]{dq} (field_proj v) -∗ typed_pointsto l dq v).
Proof.
  iIntros "Hl".
  iDestruct (struct_fields_acc_update with "[$]") as "[$ H]".
  iIntros "* Hl".
  iSpecialize ("H" with "[$]").
  erewrite set_eq.
  2:{ done. } iFrame.
Qed.

End lemmas.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

#[global] Instance field_offset_into_val : IntoVal (w64 * go_type) :=
  { to_val_def := fun '(off, t) => (#off, #t)%V; }.

Lemma field_off_to_val_unfold (p: w64 * go_type) :
  #p = (#p.1, #p.2)%V.
Proof.
  destruct p.
  rewrite {1}to_val_unseal //=.
Qed.

Global Instance pure_struct_field_offset_wp (t: go_type) f :
  PureWp True (struct.field_offset #t #f) (#(struct.field_offset_f t f)).
Proof.
  apply pure_wp_val. iIntros (??).
  induction t using go_type_ind;
    try solve [
        iIntros (Φ) "_ HΦ"; wp_call_lc "?";
        rewrite [in #(_, _)]to_val_unseal /=;
          iApply "HΦ"; done
      ].
  iIntros (Φ) "_ HΦ"; wp_call_lc "?".
  iSpecialize ("HΦ" with "[$]").
  iInduction decls as [|[f' ft] decls] forall (Φ).
  - wp_pures.
    rewrite field_off_to_val_unfold /=.
    iApply "HΦ".
  - match goal with
    | |- context[environments.Esnoc _ (INamed "IHdecls") ?P] =>
        set (IHdeclsP := P)
    end.
    wp_pures.
    rewrite !field_off_to_val_unfold !desc_to_val_unfold /=.
    wp_pures.
    destruct (bool_decide_reflect (f' = f)); subst.
    + rewrite -> bool_decide_eq_true_2 by auto; wp_pures.
      rewrite -> ByteString.eqb_eq by auto.
      iApply "HΦ".
    + rewrite -> bool_decide_eq_false_2 by auto; wp_pures.
      rewrite -> ByteString.eqb_ne by auto.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      iApply "IHdecls".
      { naive_solver. }
      wp_pures.
      rewrite field_off_to_val_unfold.
      destruct ((fix field_offset_struct (d : struct.descriptor) :=
                  match d with
                  | nil => _
                  | cons _ _ => _
                  end)
        decls) eqn:Hoff.
      wp_pures.
      wp_apply wp_type_size.
      iIntros "_".
      wp_pures.
      iApply "HΦ".
Qed.

Global Instance pure_struct_field_ref_wp (t: go_type) f (l : loc) :
  PureWp True (struct.field_ref #t #f #l) #(struct.field_ref_f t f l).
Proof.
  pure_wp_start.
  destruct (struct.field_offset_f t f) eqn:Hoff.
  rewrite field_off_to_val_unfold /=; wp_pures.
  iExactEq "HΦ".
  repeat f_equal.
  rewrite struct.field_ref_f_unseal /struct.field_ref_f_def.
  rewrite Hoff /=.
  repeat (f_equal; try word).
Qed.

Definition is_structT (t : go_type) : Prop :=
  match t with
  | structT d => True
  | _ => False
  end.

Definition wp_struct_make (t : go_type) (l : list (go_string*val)) :
  is_structT t →
  PureWp True
  (struct.make #t (alist_val l))
  (struct.val_aux t l).
Proof.
  intros ?.
  pure_wp_start.
  rewrite struct.make_unseal /struct.make_def struct.val_aux_unseal.
  destruct t; try by exfalso.
  wp_pures.
  iInduction decls as [|[f ft] decls] "IH" forall (Φ).
  - wp_pure_lc "?". wp_pures. by iApply "HΦ".
  - wp_pure_lc "?"; wp_pures.
    rewrite !desc_to_val_unfold /=; wp_pures.
    destruct (alist_lookup_f _ _).
    + wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      unshelve iApply "IH"; first done.
      iIntros "_".
      simpl fill. wp_pures. by iApply "HΦ".
    + wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      unshelve iApply "IH"; first done.
      iIntros "_".
      simpl fill. wp_pures. by iApply "HΦ".
Qed.

Global Instance points_to_access_struct_field_ref {V Vf} l f v (proj : V → Vf) dq {t tf : go_type}
  `{!IntoVal V} `{!IntoValTyped V t}
  `{!IntoVal Vf} `{!IntoValTyped Vf tf}
  `{!IntoValStructField f t proj} `{!SetterWf proj}
  `{!struct.Wf t}
  : PointsToAccess (struct.field_ref_f t f l) (proj v)
                   dq
                   (l ↦{dq} v)%I
                   (λ vf', l ↦{dq} (set proj (λ _, vf') v))%I.
Proof.
  constructor.
  - intros. by iApply struct_fields_acc_update.
  - by rewrite RecordSet.set_eq.
Qed.
End wps.
