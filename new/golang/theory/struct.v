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
Fixpoint field_get_f d f0: val -> val :=
  λ v, match d with
       | [] => #()
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 => if f =? f0 then v1 else field_get_f fs f0 v2
         | _ => #()
         end
       end.

Fixpoint field_set_f d f0 fv: val -> val :=
  λ v, match d with
       | [] => v
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 =>
           if f =? f0
           then PairV fv v2
           else PairV v1 (field_set_f fs f0 fv v2)
         | _ => v
         end
       end.

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

Class IntoValStructField (f : string) (fs : struct.descriptor) (V : Type) (Vf : Type)
  `{!IntoVal V} `{!IntoVal Vf}
  `{!IntoValTyped Vf (default boolT (assocl_lookup f fs))}
  :=
  {
    field_proj : V → Vf ;
    field_proj_eq_field_get : ∀ v, #(field_proj v) = (struct.field_get_f fs f #v);
  }.

Global Arguments field_proj (f) {_ _ _ _ _ _ _} (v).

Definition struct_fields `{!IntoVal V} `{!IntoValTyped V t} l dq
  (fs : struct.descriptor) (v : V) : iProp Σ :=
  [∗ list] ft ∈ fs,
    ∀ `(H:IntoValStructField f fs V Vf), ("H" +:+ f) ∷ l ↦s[t :: f]{dq} (field_proj f v).

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
  PureWpVal True (struct.field_ref t f #l) #(struct.field_ref_f t f l).
Proof.
  iIntros (?? Φ?) "HΦ".
  rewrite /struct.field_ref. wp_pures.
  iModIntro.
  (* FIXME: avoid unfolding to_val *)
  iExactEq "HΦ". Transparent to_val. rewrite /to_val /=. Opaque to_val.
  unfold struct.field_ref_f. simpl.
  rewrite /loc_add /= /addr_id /=.
  repeat (f_equal; try word).
Qed.

Definition is_structT (t : go_type) : Prop :=
  match t with
  | structT d => True
  | _ => False
  end.

Global Instance wp_struct_fields_cons_nil (k : string) (l : list (string * val)) (v : val) :
  PureWpVal True
    (list.Cons (PairV #k v) (struct.fields_val l))
    (struct.fields_val ((pair k v) :: l))
.
Proof.
  iIntros (???) "_ HΦ".
  rewrite struct.fields_val_unseal /=.
  wp_pures. by iApply "HΦ".
Qed.

Global Instance wp_struct_fields_cons (k : string) (l : list (string * val)) (v : val) :
  PureWpVal True
    (list.Cons (PairV #k v) (struct.fields_val l))
    (struct.fields_val ((pair k v) :: l))
.
Proof.
  iIntros (???) "_ HΦ".
  rewrite struct.fields_val_unseal /=.
  wp_pures. by iApply "HΦ".
Qed.

Fixpoint is_comparable_type (t : go_type) : Prop :=
  match t with
  | arrayT _ elem => is_comparable_type elem
  | structT d =>
      (fix is_comparable_type_struct d : Prop :=
         match d with
         | [] => True
         | (_,t) :: d => is_comparable_type t ∧ is_comparable_type_struct d
         end
      ) d
  | funcT => False
  | _  => True
  end
.

Global Instance wp_if_destruct `{!IntoVal V} `{!IntoValTyped V t} `{!EqDecision V} (v1 v2 : V) :
  PureWpVal (is_comparable_type t) (# v1 = # v2) #(bool_decide (v1 = v2)).
Proof.
  iIntros (?? Φk) "%Ht HΦ".
Admitted.

Global Instance wp_struct_assocl_lookup (k : string) (l : list (string * val)) :
  PureWpVal True
    (struct.assocl_lookup #k (struct.fields_val l))
    (match (assocl_lookup k l) with | None => InjLV #() | Some v => InjRV v end)
.
Proof.
  iIntros (?? Φ) "_ HΦ".
  rewrite struct.fields_val_unseal.
  iInduction l as [|[]] "IH" forall (Φ); [refine ?[base]| refine ?[cons]].
  [base]: {
    wp_rec.
    rewrite /struct.fields_val_def /=.
    wp_pures. by iApply "HΦ".
  }
  [cons]: {
    wp_rec.
    rewrite /struct.fields_val_def /=.
    wp_pures.
    wp_pure; [done|].
    destruct bool_decide eqn:Heqb; wp_pures.
    {
      rewrite bool_decide_eq_true in Heqb.
      eapply (inj (R:=(=))) in Heqb.
      2:{
      }
      inversion Heqb; subst. clear Heqb.
      wp_pures.
      rewrite (String.eqb_refl).
      by iApply "HΦ".
    }
    {
      rewrite bool_decide_eq_false in Heqb.
      wp_apply "IH".
      destruct (s =? _)%string eqn:Hx.
      { exfalso. apply Heqb. repeat f_equal. symmetry. by apply String.eqb_eq. }
      by iApply "HΦ".
    }
  }
Qed.

Global Instance wp_struct_make (t : go_type) (l : list (string*val)) :
  PureWpVal (is_structT t)
  (struct.make t (struct.fields_val l))
  (struct.val t l).
Proof.
  intros ????Ht.
  rewrite struct.make_unseal struct.val_unseal.
  destruct t; try by exfalso.
  unfold struct.make_def.
  iIntros "HΦ".
  iInduction decls as [] "IH" forall (Φ).
  - wp_pures. simpl. done.
  - destruct a.
    wp_pures.
    unfold struct.val_def.
    destruct (assocl_lookup _ _).
    + wp_pures. wp_apply "IH"; first done.
      wp_pures. done.
    + wp_pures. wp_apply "IH"; first done.
      wp_pures. done.
Qed.
End wps.
