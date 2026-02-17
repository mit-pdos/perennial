(* Based on https://gitlab.mpi-sws.org/iris/iris/-/blob/849f50f421114ad1b8caf0cd1b66aff338e4abfa/iris/base_logic/lib/saved_prop.v *)
From New.ghost Require Export own.

(* From stdpp Require Import gmap. *)
(* From iris.algebra Require Import dfrac_agree. *)
(* From iris.proofmode Require Import proofmode. *)
(* From iris.base_logic Require Export own. *)
From iris.bi Require Import fractional.
(* From iris.prelude Require Import options. *)
Import uPred.

Section saved_prop.
  Context `{!allG Σ}.
  Definition saved_prop_own (γ : gname) (dq : dfrac) (P : iProp Σ) :=
    own γ (to_dfrac_agree dq (Next P)).
  Global Typeclasses Opaque saved_prop_own.

  Implicit Types (γ : gname) (dq : dfrac).

  Global Instance saved_prop_discarded_persistent γ P :
    Persistent (saved_prop_own γ DfracDiscarded P).
  Proof. rewrite /saved_prop_own; apply _. Qed.

  Global Instance saved_prop_ne γ dq : NonExpansive (saved_prop_own γ dq).
  Proof. solve_proper. Qed.
  Global Instance saved_prop_proper γ dq : Proper ((≡) ==> (≡)) (saved_prop_own γ dq).
  Proof. solve_proper. Qed.

  Global Instance saved_prop_fractional γ P : Fractional (λ q, saved_prop_own γ (DfracOwn q) P).
  Proof. intros q1 q2. rewrite /saved_prop_own -own_op -dfrac_agree_op //. Qed.
  Global Instance saved_prop_as_fractional γ P q :
    AsFractional (saved_prop_own γ (DfracOwn q) P) (λ q, saved_prop_own γ (DfracOwn q) P) q.
  Proof. split; [done|]. apply _. Qed.

  (** Allocation *)
  Lemma saved_prop_alloc_strong P (I : gname → Prop) dq :
    ✓ dq →
    pred_infinite I →
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_prop_own γ dq P.
  Proof. intros ??. by apply own_alloc_strong. Qed.

  Lemma saved_prop_alloc_cofinite P (G : gset gname) dq :
    ✓ dq →
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_prop_own γ dq P.
  Proof. intros ?. by apply own_alloc_cofinite. Qed.

  Lemma saved_prop_alloc P dq :
    ✓ dq →
    ⊢ |==> ∃ γ, saved_prop_own γ dq P.
  Proof. intros ?. by apply own_alloc. Qed.

  (** Validity *)
  Lemma saved_prop_valid γ dq P :
    saved_prop_own γ dq P -∗ ⌜✓ dq⌝.
  Proof.
    rewrite /saved_prop_own own_valid dfrac_agree_validI //. eauto.
  Qed.
  Lemma saved_prop_valid_2 γ dq1 dq2 P Q :
    saved_prop_own γ dq1 P -∗ saved_prop_own γ dq2 Q -∗ ⌜✓ (dq1 ⋅ dq2)⌝ ∗ ▷ (P ≡ Q).
  Proof.
    iIntros "Hx Hy". rewrite /saved_prop_own.
    iCombine "Hx Hy" gives "Hv".
    rewrite dfrac_agree_validI_2. iDestruct "Hv" as "[$ $]".
  Qed.
  Lemma saved_prop_agree γ dq1 dq2 P Q :
    saved_prop_own γ dq1 P -∗ saved_prop_own γ dq2 Q -∗ ▷ (P ≡ Q).
  Proof. iIntros "Hx Hy". iPoseProof (saved_prop_valid_2 with "Hx Hy") as "[_ $]". Qed.

  Global Instance saved_prop_combine_as γ dq1 dq2 P Q :
    CombineSepAs (saved_prop_own γ dq1 P) (saved_prop_own γ dq2 Q)
      (saved_prop_own γ (dq1 ⋅ dq2) P).
  (* higher cost than the Fractional instance, which kicks in for #qs *)
  Proof.
    rewrite /CombineSepAs. iIntros "[Hx Hy]".
    unfold saved_prop_own.
    iCombine "Hx Hy" gives "H". rewrite dfrac_agree_validI_2.
    iDestruct "H" as "[_ Heq]". iRewrite -"Heq" in "Hy".
    iCombine "Hx Hy" as "H". rewrite dfrac_agree_op. iFrame.
  Qed.

  Global Instance saved_prop_combine_gives γ dq1 dq2 P Q :
    CombineSepGives (saved_prop_own γ dq1 P) (saved_prop_own γ dq2 Q)
      (⌜✓ (dq1 ⋅ dq2)⌝ ∗ ▷ (P ≡ Q)).
  Proof.
    rewrite /CombineSepGives. iIntros "[Hx Hy]".
    iPoseProof (saved_prop_valid_2 with "Hx Hy") as "[% #$]". eauto.
  Qed.

  (** Make an element read-only. *)
  Lemma saved_prop_persist γ dq v :
    saved_prop_own γ dq v ==∗ saved_prop_own γ DfracDiscarded v.
  Proof.
    iApply own_update. apply dfrac_agree_persist.
  Qed.

  (** Recover fractional ownership for read-only element. *)
  Lemma saved_prop_unpersist γ v :
    saved_prop_own γ DfracDiscarded v ==∗ ∃ q, saved_prop_own γ (DfracOwn q) v.
  Proof.
    iIntros "H".
    iMod (own_updateP with "H") as "H";
      first by apply dfrac_agree_unpersist.
    iDestruct "H" as (? (q&->)) "H".
    iIntros "!>". iExists q. done.
  Qed.

  (** Updates *)
  Lemma saved_prop_update Q γ P :
    saved_prop_own γ (DfracOwn 1) P ==∗ saved_prop_own γ (DfracOwn 1) Q.
  Proof.
    iApply own_update. apply cmra_update_exclusive. done.
  Qed.
  Lemma saved_prop_update_2 Q γ q1 q2 x1 x2 :
    (q1 + q2 = 1)%Qp →
    saved_prop_own γ (DfracOwn q1) x1 -∗ saved_prop_own γ (DfracOwn q2) x2 ==∗
    saved_prop_own γ (DfracOwn q1) Q ∗ saved_prop_own γ (DfracOwn q2) Q.
  Proof.
    intros Hq. rewrite -own_op. iApply own_update_2.
    apply dfrac_agree_update_2.
    rewrite dfrac_op_own Hq //.
  Qed.
  Lemma saved_prop_update_halves Q γ x1 x2 :
    saved_prop_own γ (DfracOwn (1/2)) x1 -∗
    saved_prop_own γ (DfracOwn (1/2)) x2 ==∗
    saved_prop_own γ (DfracOwn (1/2)) Q ∗ saved_prop_own γ (DfracOwn (1/2)) Q.
  Proof. iApply saved_prop_update_2. apply Qp.half_half. Qed.
End saved_prop.

Section saved_pred.
  Context `{!allG Σ} {A : Type}.
  Definition saved_pred_own (γ : gname) (dq : dfrac) (Φ : A → iProp Σ) :=
    own γ (to_dfrac_agree dq (Next ∘ Φ : oFunctor_apply (A -d> ▶ ∙) (iPropO Σ))).

  Global Typeclasses Opaque saved_prop_own.

  Global Instance saved_pred_discarded_persistent γ Φ :
    Persistent (saved_pred_own γ DfracDiscarded Φ).
  Proof. rewrite /saved_pred_own; apply _. Qed.

  Global Instance saved_pred_own_contractive `{!savedPredG Σ A} γ dq :
    Contractive (saved_pred_own γ dq : (A -d> iPropO Σ) → iProp Σ).
  Proof.
    solve_proper_core ltac:(fun _ => first [ intros ?; progress simpl | by auto | f_contractive | f_equiv ]).
  Qed.

  Global Instance saved_pred_fractional γ Φ : Fractional (λ q, saved_pred_own γ (DfracOwn q) Φ).
  Proof. intros q1 q2. rewrite /saved_pred_own -own_op -dfrac_agree_op //. Qed.
  Global Instance saved_pred_as_fractional γ Φ q :
    AsFractional (saved_pred_own γ (DfracOwn q) Φ) (λ q, saved_pred_own γ (DfracOwn q) Φ) q.
  Proof. split; [done|]. apply _. Qed.

  (** Allocation *)
  Lemma saved_pred_alloc_strong Φ (I : gname → Prop) dq :
    ✓ dq →
    pred_infinite I →
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_pred_own γ dq Φ.
  Proof. intros ??. by apply own_alloc_strong. Qed.

  Lemma saved_pred_alloc_cofinite Φ (G : gset gname) dq :
    ✓ dq →
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_pred_own γ dq Φ.
  Proof. intros ?. by apply own_alloc_cofinite. Qed.

  Lemma saved_pred_alloc Φ dq :
    ✓ dq →
    ⊢ |==> ∃ γ, saved_pred_own γ dq Φ.
  Proof. intros ?. by apply own_alloc. Qed.

  (** Validity *)
  Lemma saved_pred_valid γ dq Φ :
    saved_pred_own γ dq Φ -∗ ⌜✓ dq⌝.
  Proof.
    rewrite /saved_pred_own own_valid dfrac_agree_validI //. eauto.
  Qed.
  Lemma saved_pred_valid_2 γ dq1 dq2 Φ Ψ x :
    saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ⌜✓ (dq1 ⋅ dq2)⌝ ∗ ▷ (Φ x ≡ Ψ x).
  Proof.
    iIntros "Hx Hy". rewrite /saved_pred_own.
    iCombine "Hx Hy" gives "Hv".
    rewrite dfrac_agree_validI_2.
    iDestruct "Hv" as "[$ Hag]".
    iApply later_equivI. by iApply (discrete_fun_equivI with "Hag").
  Qed.
  Lemma saved_pred_agree γ dq1 dq2 Φ Ψ x :
    saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ▷ (Φ x ≡ Ψ x).
  Proof. iIntros "Hx Hy". iPoseProof (saved_pred_valid_2 with "Hx Hy") as "[_ $]". Qed.

  (** Make an element read-only. *)
  Lemma saved_pred_persist γ dq v :
    saved_pred_own γ dq v ==∗ saved_pred_own γ DfracDiscarded v.
  Proof.
    iApply own_update. apply dfrac_agree_persist.
  Qed.

  (** Recover fractional ownership for read-only element. *)
  Lemma saved_pred_unpersist γ v :
    saved_pred_own γ DfracDiscarded v ==∗ ∃ q, saved_pred_own γ (DfracOwn q) v.
  Proof.
    iIntros "H".
    iMod (own_updateP with "H") as "H";
      first by apply dfrac_agree_unpersist.
    iDestruct "H" as (? (q&->)) "H".
    iIntros "!>". iExists q. done.
  Qed.

  (** Updates *)
  Lemma saved_pred_update Ψ γ Φ :
    saved_pred_own γ (DfracOwn 1) Φ ==∗ saved_pred_own γ (DfracOwn 1) Ψ.
  Proof.
    iApply own_update. apply cmra_update_exclusive. done.
  Qed.
  Lemma saved_pred_update_2 Ψ γ q1 q2 x1 x2 :
    (q1 + q2 = 1)%Qp →
    saved_pred_own γ (DfracOwn q1) x1 -∗ saved_pred_own γ (DfracOwn q2) x2 ==∗
    saved_pred_own γ (DfracOwn q1) Ψ ∗ saved_pred_own γ (DfracOwn q2) Ψ.
  Proof.
    intros Hq. rewrite -own_op. iApply own_update_2.
    apply dfrac_agree_update_2.
    rewrite dfrac_op_own Hq //.
  Qed.
  Lemma saved_pred_update_halves Ψ γ x1 x2 :
    saved_pred_own γ (DfracOwn (1/2)) x1 -∗
    saved_pred_own γ (DfracOwn (1/2)) x2 ==∗
    saved_pred_own γ (DfracOwn (1/2)) Ψ ∗ saved_pred_own γ (DfracOwn (1/2)) Ψ.
  Proof. iApply saved_pred_update_2. apply Qp.half_half. Qed.
End saved_pred.
