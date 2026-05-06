From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode classes modalities.

Section cond.
  Context {PROP : bi} `{!BiAffine PROP}.
  Implicit Types P Q : PROP.

  Definition cond (φ : Prop) (P : PROP) : PROP := P ∨ ⌜¬ φ⌝.
  Local Notation "⟨ φ ⟩ P" := (cond φ P) (at level 20, P at level 20).

  Global Instance cond_ne φ : NonExpansive (cond φ).  Proof. solve_proper. Qed.
  Global Instance cond_proper φ : Proper ((⊣⊢) ==> (⊣⊢)) (cond φ).  Proof. solve_proper. Qed.
  Global Instance cond_mono φ : Proper ((⊢) ==> (⊢)) (cond φ).  Proof. solve_proper. Qed.

  Lemma cond_True  P : ⟨ True ⟩ P  ⊣⊢ P.
  Proof.
    rewrite /cond. iSplit.
    - iIntros "[H | %H]"; [ done | tauto ].
    - iIntros "H". iFrame.
  Qed.
  Lemma cond_False P : ⟨ False ⟩ P ⊣⊢ True.
  Proof. rewrite /cond. iSplit; auto. Qed.

  Lemma cond_intro φ P : P ⊢ ⟨ φ ⟩ P.
  Proof. rewrite /cond. iIntros "$ _". Qed.
  Lemma cond_elim  φ P : φ → ⟨ φ ⟩ P ⊢ P.
  Proof. rewrite /cond=> ?. iIntros "[H | %H]"; first done. tauto. Qed.

  Global Instance cond_persistent φ P `{!Persistent P} : Persistent (⟨ φ ⟩ P).
  Proof. rewrite /cond. apply _. Qed.
  Global Instance cond_timeless φ P `{!Timeless P} : Timeless (⟨ φ ⟩ P).
  Proof. rewrite /cond. apply _. Qed.

  Class CondImplies (φ ψ : Prop) : Prop :=
    cond_implies : φ -> ψ.

  (* Base instances — solved automatically. *)
  Global Instance cond_implies_refl φ : CondImplies φ φ.
  Proof. rewrite /CondImplies //. Qed.
  Global Instance cond_implies_False_l φ : CondImplies False φ.
  Proof. rewrite /CondImplies //. Qed.
  Global Instance cond_implies_True_r φ : CondImplies φ True.
  Proof. rewrite /CondImplies //. Qed.

  Class IntoCond (φ : Prop) (P Q : PROP) := into_cond : P ⊢ cond φ Q.
  Global Hint Mode IntoCond + ! - : typeclass_instances.

  Global Instance into_cond_cond φ Q : IntoCond φ (⟨ φ ⟩ Q) Q | 0.
  Proof. by rewrite /IntoCond. Qed.

  Global Instance into_cond_default φ P : IntoCond φ P P | 100.
  Proof. rewrite /IntoCond. apply cond_intro. Qed.

  Global Instance into_cond_implies φ ψ P `{!CondImplies φ ψ} :
    IntoCond φ (⟨ ψ ⟩ P) P | 5.
  Proof.
    rewrite /IntoCond /cond. iIntros "[H | %H]"; first iFrame.
    iRight. iPureIntro. firstorder.
  Qed.

  Lemma cond_modality_mixin φ :
    modality_mixin (cond φ)
      (MIEnvTransform (IntoCond φ))
      (MIEnvTransform (IntoCond φ)).
  Proof.
    split; simpl.
    - split.
      + rewrite /IntoCond /cond=> P Q HPQ.
        iIntros "#HP".
        iDestruct (HPQ with "HP") as "HPQ".
        iDestruct "HPQ" as "[HQ | %Hφ]".
        * iLeft. iApply "HQ".
        * iRight. firstorder.
      + intros P Q. rewrite /cond.
        iIntros "H". rewrite bi.or_and_r. iSplit.
        * iDestruct "H" as "[H _]". done.
        * iDestruct "H" as "[_ H]". done.
    - rewrite /IntoCond=> P Q HPQ. exact HPQ.
    - rewrite /cond. iIntros "$ _".
    - intros P Q HPQ. rewrite /cond. iIntros "[H | %H]".
      + iDestruct (HPQ with "H") as "H". iFrame.
      + iRight. done.
    - intros P Q. rewrite /cond. iIntros "[HP HQ]".
      iDestruct "HP" as "[HP | %H]".
      2: { iRight. done. }
      iDestruct "HQ" as "[HQ | %H]".
      2: { iRight. done. }
      iLeft. iFrame.
  Qed.

  Definition cond_modality (φ : Prop) : modality PROP PROP :=
    Modality _ (cond_modality_mixin φ).

  (* Hook into iModIntro. *)
  Global Instance from_modal_cond φ P :
    FromModal True (cond_modality φ) (⟨φ⟩ P) (⟨φ⟩ P) P.
  Proof. rewrite /FromModal /=. intros. done. Qed.

  Global Instance elim_modal_cond p φ P Q :
    ElimModal True p false (⟨φ⟩ P) P (⟨φ⟩ Q) Q.
  Proof.
    rewrite /ElimModal /= => _.
    rewrite bi.intuitionistically_if_elim /cond.
    iIntros "[HP HK]".
    iDestruct "HP" as "[HP | %H]".
    2: { iRight. done. }
    iLeft. iApply "HK". done.
  Qed.

End cond.

Notation "⟨ b ⟩ P" := (cond b P) (at level 20, P at level 20).
Global Hint Extern 10 (CondImplies _ _) =>
  (hnf; intros; first [assumption | discriminate | tauto]) : typeclass_instances.
Global Hint Extern 20 (CondImplies _ _) =>
  (hnf; firstorder) : typeclass_instances.

Section cond_examples.
  Context {PROP : bi} `{!BiAffine PROP}.
  Implicit Types P Q : PROP.

  Local Example one:
    ∀ P Q (φ ψ : Prop), (P -∗ Q) -∗ (⟨ φ ∨ ψ ⟩ P) -∗ (⟨ φ ⟩ Q).
  Proof.
    iIntros (????) "H Hp".
    iModIntro. iApply "H". done.
  Qed.

  Local Example two:
    ∀ P Q (φ ψ : Prop), (P -∗ Q) -∗ (⟨ φ ⟩ P) -∗ (⟨ φ ∧ ψ ⟩ Q).
  Proof.
    iIntros (????) "H Hp".
    iModIntro. iApply "H". done.
  Qed.

End cond_examples.
