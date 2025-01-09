From Perennial.goose_lang Require Import lifting.
From New.golang.defn Require Export struct.
From New.golang.theory Require Import mem exception list typing.
From Perennial.Helpers Require Import NamedProps.
From RecordUpdate Require Export RecordUpdate.

Module struct.
Section goose_lang.
Context `{ffi_syntax}.

Implicit Types (d : struct.descriptor).
Infix "=?" := (ByteString.eqb).

(* FIXME: what does _f mean? Want better name. *)
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

Definition field_ref_f t f0 l: loc := l +ₗ (struct.field_offset t f0).1.

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
       match (assocl_lookup f fvs1), (assocl_lookup f fvs2) with
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
    repeat destruct assocl_lookup; naive_solver.
  - simpl in *. injection Heq as ??. by apply IHd.
Qed.

(* FIXME: could try stating this with (structT d) substituted in. The main
   concern is that it will result in t getting unfolded. *)
Theorem struct_fields_split `{!IntoVal V} `{!IntoValTyped V t}
  l q {dwf : struct.Wf t} (v : V) :
  typed_pointsto l q v
  ⊣⊢ match t with
     | structT d  => struct_fields l q d v
     | _ => typed_pointsto l q v
     end.
Proof.
  subst.
  destruct t; try done.
  iSplit.
  - (* split up struct *)
    iIntros "Hv".
    admit.
  - (* combine struct fields *)
    admit.
Admitted.

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

Global Instance pure_struct_field_ref_wp t f (l : loc) :
  PureWp True (struct.field_ref t f #l) #(struct.field_ref_f t f l).
Proof.
  iIntros (?????) "HΦ".
  wp_call_lc "?".
  iSpecialize ("HΦ" with "[$]").
  iExactEq "HΦ". rewrite /struct.field_ref_f.
  repeat (f_equal; try word).
Qed.

Definition is_structT (t : go_type) : Prop :=
  match t with
  | structT d => True
  | _ => False
  end.

Global Instance wp_struct_fields_cons_nil (k : go_string) (l : list (go_string * val)) (v : val) :
  PureWp  True
    (list.Cons (PairV #k v) (struct.fields_val l))
    (struct.fields_val ((pair k v) :: l))
.
Proof.
  iIntros (?????) "HΦ".
  rewrite struct.fields_val_unseal list.Cons_unseal.
  wp_call_lc "?". by iApply "HΦ".
Qed.

Global Instance wp_struct_fields_cons (k : go_string) (l : list (go_string * val)) (v : val) :
  PureWp True
    (list.Cons (PairV #k v) (struct.fields_val l))
    (struct.fields_val ((pair k v) :: l))
.
Proof.
  iIntros (?????) "HΦ".
  rewrite struct.fields_val_unseal list.Cons_unseal /=.
  wp_call_lc "?". by iApply "HΦ".
Qed.

Global Instance wp_struct_assocl_lookup (k : go_string) (l : list (go_string * val)) :
  PureWp True
    (struct.assocl_lookup #k (struct.fields_val l))
    (match (assocl_lookup k l) with | None => InjLV #() | Some v => InjRV v end)
.
Proof.
  iIntros (?????) "HΦ".
  rewrite struct.fields_val_unseal.
  iInduction l as [|[]] "IH" forall (Φ); [refine ?[base]| refine ?[cons]].
  [base]:{
    simpl. wp_call. rewrite list.Match_unseal.
    wp_call_lc "?". by iApply "HΦ".
  }
  [cons]: {
    wp_call_lc "?".
    rewrite /struct.fields_val_def list.Match_unseal /=.
    wp_call.
    destruct bool_decide eqn:Heqb; wp_pures.
    {
      rewrite bool_decide_eq_true in Heqb.
      subst.
      wp_pures.
      rewrite /ByteString.eqb bool_decide_true //.
      by iApply "HΦ".
    }
    {
      rewrite bool_decide_eq_false in Heqb.
      wp_pures.
      iApply "IH".
      destruct (ByteString.eqb g _)%go eqn:Hx.
      { exfalso. apply Heqb. repeat f_equal. symmetry.
        rewrite /ByteString.eqb bool_decide_eq_true // in Hx. }
      by iApply "HΦ".
    }
  }
Qed.

Definition wp_struct_make (t : go_type) (l : list (go_string*val)) :
  PureWp (is_structT t)
  (struct.make t (struct.fields_val l))
  (struct.val_aux t l).
Proof.
  intros ?????K.
  rewrite struct.make_unseal struct.val_aux_unseal.
  destruct t; try by exfalso.
  unfold struct.make_def.
  iIntros "HΦ".
  iInduction decls as [] "IH" forall (Φ K).
  - wp_pure_lc "?". by iApply "HΦ".
  - destruct a.
    wp_pure_lc "?". wp_pures.
    unfold struct.val_aux_def.
    destruct (assocl_lookup _ _).
    + wp_pures.
      unshelve wp_apply ("IH" $! _ _ []); first done.
      iIntros "_".
      simpl fill. wp_pures. by iApply "HΦ".
    + wp_pures.
      unshelve wp_apply ("IH" $! _ _ []); first done.
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
