From Perennial.goose_lang Require Import lifting.
From iris.proofmode Require Import tactics monpred.


Section goose_lang.
Context `{ffi_semantics: ext_semantics}.
Context `{!ffi_interp ffi}.

(*
Definition post_crash `{hG: !heapG Σ} (P: forall {hG': heapG Σ}, iProp Σ) : iProp Σ :=
  (∀ σ σ' hG', ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ (heapG_ffiG (hG := hG')) σ' -∗
                             @P hG').
*)

Definition post_crash {Σ} (P: heapG Σ → iProp Σ) `{hG: !heapG Σ}  : iProp Σ :=
  (∀ σ σ' hG', ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ (heapG_ffiG (hG := hG')) σ' -∗
                             (P hG')).

(*
Definition post_crash `{hG: !heapG Σ} (P: forall {hG': heapG Σ}, iProp Σ) : iProp Σ :=
  (∀ σ σ' new, ffi_crash_rel Σ hG σ (ffi_update Σ hG new) σ' -∗
                             @P (ffi_update Σ hG new)).
*)

Class IntoCrash (P Q: forall Σ, heapG Σ → iProp Σ) :=
  into_crash : ∀ Σ hG, P Σ hG -∗ post_crash (λ hG', Q Σ hG').

Section post_crash_prop.
Context `{hG: !heapG Σ}.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.

Existing Instances ffi_crash_rel_pers.

Lemma post_crash_mono P Q:
  (∀ hG, P hG -∗ Q hG) →
  post_crash P -∗ post_crash Q.
Proof.
  iIntros (Hmono) "HP". iIntros (???) "#Hrel".
  iApply Hmono. iApply "HP"; eauto.
Qed.

Lemma post_crash_pers P Q:
  (P -∗ post_crash Q) →
  □ P -∗ post_crash (λ hG, □ Q hG).
Proof.
  iIntros (Hmono) "#HP". iIntros (???) "#Hrel".
  iAlways. iApply Hmono; eauto.
Qed.

Lemma post_crash_sep P Q:
  post_crash P ∗ post_crash Q -∗ post_crash (λ hG, P hG ∗ Q hG).
Proof.
  iIntros "(HP&HQ)". iIntros (???) "#Hrel".
  iDestruct ("HP" with "[$]") as "$".
  iDestruct ("HQ" with "[$]") as "$".
Qed.

Lemma post_crash_or P Q:
  post_crash P ∨ post_crash Q -∗ post_crash (λ hG, P hG ∨ Q hG).
Proof.
  iIntros "[HP|HQ]"; iIntros (???) "#Hrel".
  - iLeft. by iApply "HP".
  - iRight. by iApply "HQ".
Qed.

Lemma post_crash_and P Q:
  post_crash P ∧ post_crash Q -∗ post_crash (λ hG, P hG ∧ Q hG).
Proof.
  iIntros "HPQ"; iIntros (???) "#Hrel".
  iSplit.
  - iDestruct "HPQ" as "(HP&_)". by iApply "HP".
  - iDestruct "HPQ" as "(_&HQ)". by iApply "HQ".
Qed.

Lemma post_crash_pure (P: Prop) :
  P → ⊢ post_crash (λ _, ⌜ P ⌝).
Proof.
  iIntros (????); eauto.
Qed.

Lemma post_crash_nodep (P: iProp Σ) :
  P -∗ post_crash (λ _, P).
Proof. iIntros "HP". iIntros (???); eauto. Qed.

Lemma post_crash_exists {A} P Q:
  (∀ (x: A), P hG x -∗ post_crash (λ hG, Q hG x)) -∗
  (∃ x, P hG x) -∗ post_crash (λ hG, ∃ x, Q hG x).
Proof.
  iIntros "Hall HP". iIntros (???) "#Hrel".
  iDestruct "HP" as (x) "HP".
  iExists x. iApply ("Hall" with "[$] [$]").
Qed.

Lemma post_crash_forall {A} P Q:
  (∀ (x: A), P hG x -∗ post_crash (λ hG, Q hG x)) -∗
  (∀ x, P hG x) -∗ post_crash (λ hG, ∀ x, Q hG x).
Proof.
  iIntros "Hall HP". iIntros (???) "#Hrel".
  iIntros (?). iApply ("Hall" with "[HP] [$]"). iApply "HP".
Qed.

Lemma post_crash_exists_intro {A} P (x: A):
  (∀ (x: A), P hG x -∗ post_crash (λ hG, P hG x)) -∗
  P hG x -∗ post_crash (λ hG, ∃ x, P hG x).
Proof.
  iIntros "Hall HP". iIntros (???) "#Hrel".
  iExists x. iApply ("Hall" with "[$] [$]").
Qed.


End post_crash_prop.

Section IntoCrash.

  Global Instance sep_into_crash P P' Q Q':
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (λ Σ hG, P Σ hG ∗ Q Σ hG)%I (λ Σ hG, P' Σ hG ∗ Q' Σ hG)%I.
  Proof. iIntros (H1 H2 ??). rewrite ?into_crash post_crash_sep //. Qed.

  Global Instance or_into_crash P P' Q Q':
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (λ Σ hG, P Σ hG ∨ Q Σ hG)%I (λ Σ hG, P' Σ hG ∨ Q' Σ hG)%I.
  Proof. iIntros (H1 H2 ??). rewrite ?into_crash post_crash_or //. Qed.

  Global Instance and_into_crash P P' Q Q':
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (λ Σ hG, P Σ hG ∧ Q Σ hG)%I (λ Σ hG, P' Σ hG ∧ Q' Σ hG)%I.
  Proof. iIntros (H1 H2 ??). rewrite ?into_crash post_crash_and //. Qed.

  (* XXX: probably should rephrase in terms of IntoPure *)
  Global Instance pure_into_crash (P: Prop) :
    IntoCrash (λ _ _, ⌜ P ⌝%I) (λ _ _, ⌜ P ⌝%I).
  Proof. iIntros (???). by iApply post_crash_pure. Qed.

  Global Instance exist_into_crash {A} Φ Ψ:
    (∀ x : A, IntoCrash (λ Σ hG, Φ Σ hG x) (λ Σ hG, Ψ Σ hG x)) →
    IntoCrash (λ Σ hG, (∃ x, Φ Σ hG x)%I) (λ Σ hG, (∃ x, Ψ Σ hG x)%I).
  Proof.
    iIntros (???) "H". iDestruct "H" as (?) "HΦ". iPoseProof (H with "[$]") as "HΦ".
    iApply (post_crash_mono with "HΦ"). eauto.
  Qed.

  Global Instance forall_into_crash {A} Φ Ψ:
    (∀ x : A, IntoCrash (λ Σ hG, Φ Σ hG x) (λ Σ hG, Ψ Σ hG x)) →
    IntoCrash (λ Σ hG, (∀ x, Φ Σ hG x)%I) (λ Σ hG, (∀ x, Ψ Σ hG x)%I).
  Proof. iIntros (???) "H". iApply post_crash_forall; last eauto. iIntros (?). iApply H. Qed.

  Lemma into_crash_proper P P' Q Q':
    IntoCrash P Q →
    (∀ Σ hG, P Σ hG ⊣⊢ P' Σ hG) →
    (∀ Σ hG, Q Σ hG ⊣⊢ Q' Σ hG) →
    IntoCrash P' Q'.
  Proof.
    rewrite /IntoCrash.
    iIntros (HD Hwand1 Hwand2 ??) "HP".
    iApply post_crash_mono; last first.
    { iApply HD. iApply Hwand1. eauto. }
    intros. simpl. by rewrite Hwand2.
  Qed.

  Global Instance big_sepL_into_crash:
    ∀ (A : Type) (Φ Ψ : ∀ Σ, heapG Σ → nat → A → iProp Σ) (l : list A),
    (∀ (k : nat) (x : A), IntoCrash (λ Σ hG, Φ Σ hG k x) (λ Σ hG, Ψ Σ hG k x)) →
    IntoCrash (λ Σ hG, [∗ list] k↦x ∈ l, Φ Σ hG k x)%I (λ Σ hG, [∗ list] k↦x ∈ l, Ψ Σ hG k x)%I.
  Proof.
    intros.
    cut (∀ n, IntoCrash (λ Σ hG, [∗ list] k↦x ∈ l, Φ Σ hG (n + k)%nat x)%I
                        (λ Σ hG, [∗ list] k↦x ∈ l, Ψ Σ hG (n + k)%nat x)%I).
    { intros Hres. specialize (Hres O). eauto. }

    induction l => n.
    - rewrite //=. apply _.
    - rewrite //=. apply sep_into_crash; eauto.
      eapply into_crash_proper; first eapply (IHl (S n)).
      * intros. setoid_rewrite Nat.add_succ_r. setoid_rewrite <-Nat.add_succ_l. eauto.
      * intros. setoid_rewrite Nat.add_succ_r. setoid_rewrite <-Nat.add_succ_l. eauto.
  Qed.

  Lemma into_crash_post_crash_frame_l `{hG: !heapG Σ} P P' `{!IntoCrash P P'} Q:
    (P Σ hG) -∗ post_crash Q -∗ post_crash (λ hG', P' Σ hG' ∗ Q hG').
  Proof. iIntros "HP HQ". rewrite into_crash. iApply post_crash_sep. iFrame. Qed.

  Lemma into_crash_post_crash_frame_r `{hG: !heapG Σ} P P' `{!IntoCrash P P'} Q:
    post_crash Q -∗ (P Σ hG) -∗ post_crash (λ hG', Q hG' ∗ P' Σ hG').
  Proof. iIntros "HP HQ". rewrite into_crash. iApply post_crash_sep. iFrame. Qed.

End IntoCrash.

Section modality.
  Context {Σ: gFunctors}.

  Program Definition heapG_index: biIndex :=
    {| bi_index_type := heapG Σ;
       bi_index_rel := (=);
    |}.
  Next Obligation. admit. Admitted.

  Local Notation monPred := (monPred heapG_index ((iPropI Σ))).
  Local Notation monPredI := (monPredI heapG_index ((iPropI Σ))).

  Program Definition post_crash' (P: monPred) : monPred :=
    {| monPred_at := λ hG, post_crash (hG := hG) P |}.

  Class IntoCrash' (P Q: monPred) :=
    into_crash' : ∀ hG, P hG -∗ post_crash' Q hG.

  Lemma modality_post_crash_mixin :
    modality_mixin (PROP1 := monPredI) (PROP2 := monPredI) (post_crash') (MIEnvTransform IntoCrash') (MIEnvTransform IntoCrash').
  Proof.
    split.
    - rewrite /modality_intuitionistic_action_spec.
      split.
      * rewrite /IntoCrash'/post_crash'. intros. split.
        intros hG => //=. iIntros "HP".
        iPoseProof (post_crash_pers (P hG) Q with "[HP]") as "H".
        ** eauto.
        ** iApply "HP".
        ** iIntros (???) "H'". iSpecialize ("H" with "[$]"). eauto.
      * admit.
    - rewrite /modality_spatial_action_spec.
      rewrite /IntoCrash'/post_crash'. intros. split. intros hG. eauto.
    - rewrite /IntoCrash'/post_crash'. intros. split. intros hG. simpl. iIntros "H". iIntros (??). eauto.
    - admit.
    - admit.
  Admitted.

  Definition modality_post_crash := Modality _ (modality_post_crash_mixin).

  Instance FromModal_post_crash P: FromModal modality_post_crash (post_crash' P) (post_crash' P) P.
  Proof. rewrite /FromModal//=. Qed.

  Instance IntoCrash_post_crash P:
    IntoCrash' (post_crash' P) P.
  Proof. rewrite //=. Qed.

  Lemma test P Q: post_crash' (P -∗ Q) -∗ post_crash' P -∗ post_crash' Q.
  Proof. iIntros "Hwand HP". iModIntro. by iApply "Hwand". Qed.
End modality.
End goose_lang.
