From New.proof Require Import proof_prelude.
From iris.algebra.lib Require Import mono_list mono_nat dfrac_agree gmap_view.

Module cmra_expr.
Inductive t :=
| gmap (K : Type) `{Countable K} (V : t)
| mono_list (E : Type)
| frac
| agree (A : Type)
| dfrac_agree (A : Type)
| excl (A : Type)
| gmap_view (K : Type) `{Countable K} (V : t)
.

Fixpoint interpret (x : t) : cmra :=
  match x with
  | gmap K V => gmapR K (interpret V)
  | mono_list A => mono_listR (leibnizO A)
  | frac => fracR
  | agree A => agreeR (leibnizO A)
  | dfrac_agree A => dfrac_agreeR (leibnizO A)
  | excl A => exclR (leibnizO A)
  | gmap_view K V => gmap_viewR K (interpret V)
  end.
End cmra_expr.

Inductive csigT {A : Type} P :=
| CexistT : ∀ (x : A), P x → csigT P
| Cinvalid : csigT P.
Arguments CexistT {_ _} (_).
Arguments Cinvalid {_ _}.

Definition any_cmra_car : Type := csigT cmra_expr.interpret.

Local Instance any_cmra_equiv_instance : Equiv any_cmra_car :=
  λ a a',
    match a, a' with
    | CexistT A a, CexistT A' a' =>
        (∃ (pf : A = A'), (eq_rect A cmra_expr.interpret a A' pf) = a')
    | Cinvalid, Cinvalid => True
    | _, _ => False
    end.
(*
Inductive any_cmra_equiv_instance : Equiv any_cmra_car :=
| any_cmra_equiv {A} (a b : cmra_expr.interpret A)
  : a ≡ b → (existT A a) ≡ (existT A b).
Local Existing Instance any_cmra_equiv_instance. *)

Inductive any_cmra_dist_instance : Dist any_cmra_car :=
| any_cmra_dist {A} (a b : cmra_expr.interpret A) i :
  a ≡{i}≡ b → (existT A a) ≡{i}≡ (existT A b).
Existing Instance any_cmra_dist_instance.

Inductive any_cmra_valid_instance : Valid any_cmra_car :=
| any_cmra_valid {A} (a : cmra_expr.interpret A) : ✓ a → ✓ (existT A a).
Existing Instance any_cmra_valid_instance.

Inductive any_cmra_validN_instance : ValidN any_cmra_car :=
| any_cmra_validN {A} (a : cmra_expr.interpret A) (n : nat) : (✓{n} a) → (✓{n} (existT A a)).
Existing Instance any_cmra_validN_instance.

Global Instance pcore_instance : PCore any_cmra_car :=
  λ x, let '(existT A a) := x in (existT A) <$> pcore a.

Global Instance op_instance : Op all_ucmra :=
  λ x y, λ A, (x A) ⋅ (y A).

Global Instance dist_equivalence n : Equivalence (dist n (A:=all_ucmra)).
Proof.
  split.
  - intros ??. done.
  - intros ????. done.
  - intros ??????. specialize (H A). specialize (H0 A). rewrite H H0 //.
Qed.

Lemma all_ucmra_ofe_mixin : OfeMixin all_ucmra.
  split.
  - intros ??. split.
    + intros H n. intros A. apply equiv_dist. apply H.
    + intros H. intros A. apply equiv_dist. intros n.
      specialize (H n). apply H.
  - apply _.
  - intros. intros A. eapply dist_le; last done. apply H.
Qed.


Lemma all_ucmra_ucmra_mixin : UcmraMixin all_ucmra.
Proof.
  split.
  - intros ?. apply ucmra_unit_valid.
  - intros ??. apply ucmra_unit_left_id.
  - constructor. simpl. unfold equiv. unfold equiv_instance.
    intros ?. rewrite ucmra_pcore_unit //.
Qed.

Lemma all_ucmra_cmra_mixin : CmraMixin all_ucmra.
  split; repeat intros ?.
  - specialize (H A). by apply cmra_op_ne.
  - eexists _; split; [done|].
    intros A. specialize (H A).
    setoid_rewrite <- H.
    rewrite /pcore /pcore_instance in H0.
    simplify_eq. done.
  - specialize (H A). specialize (H0 A). by eapply cmra_validN_ne.
  - split; repeat intros ?.
    + specialize (H A). by apply cmra_valid_validN.
    + apply cmra_valid_validN. intros n. specialize (H n A). done.
  - specialize (H A). by eapply cmra_validN_le.
  - apply cmra_assoc.
  - apply cmra_comm.
  - rewrite /op /op_instance.
    rewrite /pcore /pcore_instance in H. simplify_eq.
    destruct (pcore (x A)) eqn:H.
    + simpl. by apply cmra_pcore_l.
    + simpl. rewrite left_id //.
  - constructor. repeat intros ?.
    inversion H. subst.
    destruct (pcore (x A)) eqn:H'.
    + simpl. rewrite cmra_pcore_idemp //.
    + simpl. rewrite ucmra_pcore_unit //.
  - eexists _; split; [done|].
    destruct H as [z H]. inversion H0. subst.
    eexists _. intros ?.
    specialize (H A). rewrite /pcore /pcore_instance.
(*
    mixin_cmra_pcore_mono : ∀ x y cx : A, x ≼ y → pcore x = Some cx → ∃ cy : A, pcore y = Some cy ∧ cx ≼ cy;
    mixin_cmra_validN_op_l : ∀ (n : SI0) (x y : A), ✓{n} (x ⋅ y) → ✓{n} x;
    mixin_cmra_extend : ∀ (n : SI0) (x y1 y2 : A),
                          ✓{n} x
                          → x ≡{n}≡ y1 ⋅ y2 → {z1 : A & {z2 : A | x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2}} }.
 *)
Admitted.
