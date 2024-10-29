From Perennial.goose_lang Require Import lifting.
From New.golang.defn Require Export struct.
From New.golang.theory Require Import mem exception list typing.
From Perennial.Helpers Require Import NamedProps.

Module struct.
Section goose_lang.
Context `{ffi_syntax}.

Implicit Types (d : struct.descriptor).
Infix "=?" := (String.eqb).

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

Class Wf (d : struct.descriptor) : Set :=
  { descriptor_NoDup: NoDup d.*1; }.

End goose_lang.
End struct.

Notation "l ↦s[ t :: f ] dq v" := (struct.field_ref_f t f l ↦#{dq} v)%I
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

Class IntoValStructField (f : string) (t : go_type) {V Vf : Type}
  (field_proj : V → Vf)
  `{!IntoVal V} `{!IntoVal Vf}
  `{!IntoValTyped Vf (
        match t with
        | structT fs => default boolT (assocl_lookup f fs)
        | _ => boolT
        end
      )
  }
  :=
  {
    field_proj_eq_field_get : ∀ v, #(field_proj v) = (struct.field_get_f t f #v);
  }.

Definition struct_fields `{!IntoVal V} `{!IntoValTyped V t} l dq
  (fs : struct.descriptor) (v : V) : iProp Σ :=
  [∗ list] '(f, _) ∈ fs,
    ∀ `(H:IntoValStructField f t V Vf field_proj), ("H" +:+ f) ∷ l ↦s[t :: f]{dq} (field_proj v).

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
  l q d {Ht : t = structT d} {dwf : struct.Wf d} (v : V) :
  typed_pointsto l q v ⊣⊢ struct_fields l q d v.
Proof.
  subst.
  iSplit.
  - (* split up struct *)
    iIntros "Hv".
    admit.
  - (* combine struct fields *)
    admit.
Admitted.

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

Global Instance wp_struct_fields_cons_nil (k : string) (l : list (string * val)) (v : val) :
  PureWp  True
    (list.Cons (PairV #k v) (struct.fields_val l))
    (struct.fields_val ((pair k v) :: l))
.
Proof.
  iIntros (?????) "HΦ".
  rewrite struct.fields_val_unseal list.Cons_unseal.
  wp_call_lc "?". by iApply "HΦ".
Qed.

Global Instance wp_struct_fields_cons (k : string) (l : list (string * val)) (v : val) :
  PureWp True
    (list.Cons (PairV #k v) (struct.fields_val l))
    (struct.fields_val ((pair k v) :: l))
.
Proof.
  iIntros (?????) "HΦ".
  rewrite struct.fields_val_unseal list.Cons_unseal /=.
  wp_call_lc "?". by iApply "HΦ".
Qed.

Global Instance wp_struct_assocl_lookup (k : string) (l : list (string * val)) :
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
      rewrite (String.eqb_refl).
      by iApply "HΦ".
    }
    {
      rewrite bool_decide_eq_false in Heqb.
      wp_pures.
      iApply "IH".
      destruct (s =? _)%string eqn:Hx.
      { exfalso. apply Heqb. repeat f_equal. symmetry. by apply String.eqb_eq. }
      by iApply "HΦ".
    }
  }
Qed.

Definition wp_struct_make (t : go_type) (l : list (string*val)) :
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
End wps.
