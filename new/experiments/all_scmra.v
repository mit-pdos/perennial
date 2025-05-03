From New.proof Require Import proof_prelude.
From iris.algebra.lib Require Import mono_list mono_nat dfrac_agree gmap_view.
From Coq Require Import Logic.ClassicalEpsilon.

Module cmra_expr.
Inductive t :=
| prod (A B : t)
| gmap (K : Type) `{Countable K} (V : t)
| mono_list (E : Type)
| frac
| dfrac
| agree (A : Type)
| excl (A : Type)
| gmap_view (K : Type) `{Countable K} (V : t)
.

Fixpoint interpret (x : t) : cmra :=
  match x with
  | prod A B => prodR (interpret A) (interpret B)
  | gmap K V => gmapR K (interpret V)
  | mono_list A => mono_listR (leibnizO A)
  | frac => fracR
  | dfrac => dfracR
  | agree A => agreeR (leibnizO A)
  | excl A => exclR (leibnizO A)
  | gmap_view K V => gmap_viewR K (interpret V)
  end.
End cmra_expr.

(* This would require ucmra for everything, which would exclude exclR. *)
(* Definition any_cmra : Type := discrete_funUR cmra_expr.interpret. *)

Inductive csigT {A : Type} P :=
| CexistT : ∀ (x : A), P x → csigT P
| Cinvalid : csigT P.
Arguments CexistT {_ _} (_).
Arguments Cinvalid {_ _}.

Definition any_cmra : Type := csigT cmra_expr.interpret.

Inductive any_cmra_equiv_instance : Equiv any_cmra :=
| CexistT_equiv {A} a b : a ≡ b → (CexistT A a) ≡ (CexistT A b)
| Cinvalid_equiv : Cinvalid ≡ Cinvalid.
Local Existing Instance any_cmra_equiv_instance.

Inductive any_cmra_dist_instance : Dist any_cmra :=
| CexistT_dist {A} a b i : a ≡{i}≡ b → (CexistT A a) ≡{i}≡ (CexistT A b)
| Cinvalid_dist i : Cinvalid ≡{i}≡ Cinvalid.
Local Existing Instance any_cmra_dist_instance.

Local Instance any_cmra_valid_instance : Valid any_cmra :=
  λ x, match x with CexistT A a => ✓ a | _ => False end.

Local Instance any_cmra_validN_instance : ValidN any_cmra :=
  λ n x, match x with CexistT A a => ✓{n} a | _ => False end.

Local Instance any_cmra_pcore_instance : PCore any_cmra :=
  λ x, match x with CexistT A a => CexistT A <$> pcore a | _ => Some Cinvalid end.

Local Instance any_cmra_op_instance : Op any_cmra :=
  λ x y,
    match x, y with
    | CexistT A a, CexistT A' a' =>
        match (excluded_middle_informative (A = A')) with
        | right _ => Cinvalid
        | left eq_proof =>
            CexistT A' ((eq_rect A cmra_expr.interpret a A' eq_proof) ⋅ a')
        end
    | _, _ => Cinvalid
    end.

(* Q: does [inj_pair2] *require* [classical]? *)

Local Instance any_cmra_dist_equivalence n : Equivalence (dist n (A:=any_cmra)).
split.
+ intros ?. destruct x; constructor. apply reflexivity.
+ intros ?? Heq. oinversion Heq; subst; constructor.
  symmetry. done.
+ intros ??? Heqy Heqz. oinversion Heqy; subst; oinversion Heqz; subst; constructor.
  apply inj_pair2 in H4. subst. by etransitivity.
Qed.

Local Instance any_cmra_equiv_equivalence : Equivalence (equiv (A:=any_cmra)).
split.
+ intros ?. destruct x; constructor. apply reflexivity.
+ intros ?? Heq. oinversion Heq; subst; constructor.
  symmetry. done.
+ intros ??? Heqy Heqz. oinversion Heqy; subst; oinversion Heqz; subst; constructor.
  apply inj_pair2 in H3. subst. by etransitivity.
Qed.

Lemma any_cmra_ofe_mixin : OfeMixin any_cmra.
Proof.
  split.
  - intros; split.
    + intros Heq n. inversion Heq; constructor. by apply equiv_dist.
    + intros Heq. oinversion (Heq 0ᵢ); subst; constructor.
      apply equiv_dist => n. oinversion (Heq n); subst.
      apply inj_pair2 in H4, H5. subst. done.
  - apply _.
  - intros ???? Heq Hlt. oinversion Heq; constructor; subst.
    by eapply dist_le.
Qed.

Lemma any_cmra_validN A a n :
  ✓{n} CexistT A a ↔ ✓{n} a.
Proof. done. Qed.

Lemma any_cmra_valid A a :
  ✓ CexistT A a ↔ ✓ a.
Proof. done. Qed.

Lemma any_cmra_invalid_validN n :
  ✓{n} Cinvalid = False.
Proof. done. Qed.

Lemma any_cmra_invalid_valid :
  ✓ Cinvalid = False.
Proof. done. Qed.

Lemma CexistT_op A a a' :
  CexistT A a ⋅ CexistT A a' = CexistT A (a ⋅ a').
Proof.
  cbn. destruct excluded_middle_informative; try done. rewrite (UIP_refl _ _ e) //.
Qed.

Lemma any_cmra_included x y :
  x ≼ y ↔ y = Cinvalid ∨ (∃ A a a', x = CexistT A a ∧ y = CexistT A a' ∧ a ≼ a').
Proof.
  split.
  - intros [z Heq]. destruct y; last by left. right.
    destruct x, z; cbn in *; try destruct excluded_middle_informative in Heq; subst; oinversion Heq.
    subst. repeat eexists. apply inj_pair2 in H2, H4. subst. done.
  - intros [|].
    + subst. eexists Cinvalid. by destruct x.
    + destruct H as (? & ? & ? & -> & -> & Hincl). destruct Hincl as [i Hincl].
      eexists (CexistT x0 i). rewrite CexistT_op. constructor. done.
Qed.

Lemma any_cmra_cmra_mixin : CmraMixin any_cmra.
Proof.
  split.
  - intros [] ? ? ? H.
    + inversion H; subst; last done.
      cbn. destruct excluded_middle_informative; constructor. rewrite H0 //.
    + cbn. constructor.
  - intros. oinversion H; subst; simpl.
    + rewrite /pcore /any_cmra_pcore_instance in H0 |- *.
      apply fmap_Some_1 in H0 as [? [Hpcore ?]]; subst.
      eapply cmra_pcore_ne in Hpcore; last eassumption.
      destruct Hpcore as (ca & -> & Heq).
      eexists _; split; first done. constructor. done.
    + eexists _. split; done.
  - intros ?. intros ?? Heq. inversion Heq; last done.
    rewrite !any_cmra_validN. by apply cmra_validN_ne.
  - pose 0ᵢ. intros [|].
    + setoid_rewrite any_cmra_validN. rewrite /= any_cmra_valid ?cmra_valid_validN //.
    + rewrite any_cmra_invalid_valid. split; try done.
      intros H. specialize (H 0). done.
  - intros n m [|]; simpl; eauto using cmra_validN_le.
  - intros [|] [|] [|]; try constructor.
    + cbn. repeat (destruct excluded_middle_informative; subst; cbn); try constructor; try congruence.
      unfold eq_rect. rewrite (UIP_refl _ _ e). rewrite assoc //.
    + cbn. repeat (destruct excluded_middle_informative; subst; cbn); try constructor; try congruence.
  - intros [|] [|]; try constructor. cbn.
    repeat (destruct excluded_middle_informative; subst; cbn); try constructor; try congruence.
    rewrite (UIP_refl _ _ e). rewrite comm //.
  - intros [? a|] ? [=]; subst; auto. cbn in *.
    destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
    cbn. destruct excluded_middle_informative; try done.
    constructor; rewrite (UIP_refl _ _ e). simpl. eauto using cmra_pcore_l.
  - intros [? a|] ? [=]; subst; auto. cbn in *.
    destruct (pcore a) as [ca|] eqn:?; simplify_option_eq. cbn.
    oinversion (cmra_pcore_idemp a ca); repeat constructor; auto.
  - intros ??? Hincl Hpcore. rewrite any_cmra_included in Hincl. destruct Hincl.
    + subst. eexists Cinvalid. split; first done. eexists Cinvalid. destruct cx; reflexivity.
    + destruct H as (? & ? & ? & -> & -> & Hincl). cbn in *. simplify_option_eq. rename H into p.
      eapply cmra_pcore_mono in Hincl; try eassumption. destruct Hincl as (? & -> & Hincl).
      destruct Hincl as [i Hincl]. eexists _. split; first done. eexists (CexistT x0 i).
      cbn. destruct excluded_middle_informative; try done.
      rewrite (UIP_refl _ _ e). simpl. constructor. done.
  - intros n [|] [|]; simpl; try done.
    cbn. destruct excluded_middle_informative; last done.
    destruct e. simpl. cbn. eauto using cmra_validN_op_l.
  - intros n [? a|] y1 y2 Hx Hx'.
    + destruct y1 as [? a1|], y2 as [? a2|]; try by exfalso; inversion Hx'.
      cbn in Hx'. destruct excluded_middle_informative in Hx'; last (exfalso; oinversion Hx').
      subst. simpl in *. destruct (excluded_middle_informative (x = x1)).
      2:{ exfalso. inversion Hx'. subst. done. }
      subst.
      destruct (cmra_extend n a a1 a2) as (z1&z2&?&?&?); [done| |].
      * inversion Hx'. subst. apply inj_pair2 in H2, H3. subst. done.
      * repeat econstructor; try done.
        cbn. destruct excluded_middle_informative; last done.
        rewrite (UIP_refl _ _ e). simpl. constructor. done.
    + destruct y1 as [a1|], y2 as [a2|]; try by exfalso; inversion Hx'.
Qed.

Canonical Structure any_cmraO : ofe := Ofe any_cmra any_cmra_ofe_mixin.
Canonical Structure any_cmraR := Cmra any_cmra any_cmra_cmra_mixin.

Definition to_any (A : cmra_expr.t) a : any_cmra :=
  CexistT A a.

Lemma any_cmra_validN_op A B a b n :
  ✓{n} (CexistT A a ⋅ CexistT B b) ↔
  ∃ (pf : A = B), ✓{n}((eq_rect A _ a B pf) ⋅ b).
Proof.
  split.
  - intros H. cbn in H. destruct excluded_middle_informative in H; try done.
    exists e. destruct e. simpl in *. rewrite any_cmra_validN // in H.
  - intros (? & H). subst. simpl in *. rewrite CexistT_op //.
Qed.

Lemma any_cmra_validN_op_invalid_r A a n :
  ✓{n} (CexistT A a ⋅ Cinvalid) → False.
Proof. done. Qed.

Lemma any_cmra_validN_op_invalid_l A a n :
  ✓{n} (Cinvalid ⋅ CexistT A a) → False.
Proof. done. Qed.

Lemma any_cmra_update {A : cmra_expr.t} a b :
  a ~~> b →
  to_any A a ~~> to_any A b.
Proof.
  unfold to_any. intros Hupd n [[]|] Hvalid.
  - rewrite any_cmra_validN_op in Hvalid. destruct Hvalid as [-> Hvalid].
    simpl. rewrite any_cmra_validN_op. eexists eq_refl.
    simpl in *. specialize (Hupd n (Some c)). by apply Hupd.
  - simpl in *. by apply any_cmra_validN_op_invalid_r in Hvalid.
  - simpl in *. rewrite !any_cmra_validN in Hvalid |- *.
    specialize (Hupd n None). by apply Hupd.
Qed.

Section own.
Context `{!inG Σ any_cmraR}.

Class SimpleCmra A :=
  {
    Aexp : cmra_expr.t;
    eq_proof : A = cmra_expr.interpret Aexp;
  }.

Definition own_any {A : cmra} γ (a : A) : iProp Σ :=
  ∃ (_ : SimpleCmra A), own γ (CexistT Aexp (eq_rect A id a _ eq_proof) : any_cmra).

Lemma own_any_update γ {A : cmra} (a a' : A) :
  a ~~> a' →
  own_any γ a ==∗ own_any γ a'.
Proof.
  intros Hupd. iIntros "[% Hown]".
  iExists _. iApply (own_update with "Hown").
  apply any_cmra_update. simpl. destruct H.
  simpl in *. destruct eq_proof0. simpl.
  apply Hupd.
Qed.

Lemma own_any_alloc `{!SimpleCmra A} (a : A) :
  ✓ a →
  ⊢ |==> ∃ γ, own_any γ a.
Proof.
  intros Hvalid.
  iMod (own_alloc (CexistT Aexp (eq_rect A id a _ eq_proof) : any_cmra)) as (γ) "H".
  { rewrite any_cmra_valid. simpl. destruct SimpleCmra0.
    simpl in *. destruct eq_proof0. simpl in *. done. }
  by iFrame.
Qed.

Instance mlist_simple_cmra (A : Type) : SimpleCmra (mono_listR (leibnizO A)).
Proof. by eexists (cmra_expr.mono_list A). Qed.

Lemma own_any_mono_list (l : list nat) :
  ⊢ |==> ∃ γ, own_any γ (●ML l).
Proof.
  iApply own_any_alloc. apply mono_list_auth_valid.
Qed.
End own.

(* Print Assumptions own_any_mono_list.
  constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
  classic : ∀ P : Prop, P ∨ ¬ P
*)
