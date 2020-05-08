From Perennial.goose_lang Require Import lifting.

Section goose_lang.
Context `{ffi_semantics: ext_semantics}.
Context `{!ffi_interp ffi}.

(*
Definition post_crash `{hG: !heapG Σ} (P: forall {hG': heapG Σ}, iProp Σ) : iProp Σ :=
  (∀ σ σ' hG', ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ (heapG_ffiG (hG := hG')) σ' -∗
                             @P hG').
*)

Definition post_crash `{hG: !heapG Σ} (P: heapG Σ → iProp Σ) : iProp Σ :=
  (∀ σ σ' hG', ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ (heapG_ffiG (hG := hG')) σ' -∗
                             (P hG')).

(*
Definition post_crash `{hG: !heapG Σ} (P: forall {hG': heapG Σ}, iProp Σ) : iProp Σ :=
  (∀ σ σ' new, ffi_crash_rel Σ hG σ (ffi_update Σ hG new) σ' -∗
                             @P (ffi_update Σ hG new)).
*)

Class Durable (P: forall Σ, heapG Σ → iProp Σ) :=
  durable : ∀ Σ hG, P Σ hG -∗ post_crash (λ hG', P Σ hG').

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

Lemma post_crash_exists {A} P:
  (∀ (x: A), P hG x -∗ post_crash (λ hG, P hG x)) -∗
  (∃ x, P hG x) -∗ post_crash (λ hG, ∃ x, P hG x).
Proof.
  iIntros "Hall HP". iIntros (???) "#Hrel".
  iDestruct "HP" as (x) "HP".
  iExists x. iApply ("Hall" with "[$] [$]").
Qed.

Lemma post_crash_forall {A} P:
  (∀ (x: A), P hG x -∗ post_crash (λ hG, P hG x)) -∗
  (∀ x, P hG x) -∗ post_crash (λ hG, ∀ x, P hG x).
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

Section durable.

  Global Instance sep_durable P Q:
    Durable P →
    Durable Q →
    Durable (λ Σ hG, P Σ hG ∗ Q Σ hG)%I.
  Proof. iIntros (H1 H2 ??). rewrite ?durable post_crash_sep //. Qed.

  Global Instance or_durable P Q:
    Durable P →
    Durable Q →
    Durable (λ Σ hG, P Σ hG ∨ Q Σ hG)%I.
  Proof. iIntros (H1 H2 ??). rewrite ?durable post_crash_or //. Qed.

  Global Instance and_durable P Q:
    Durable P →
    Durable Q →
    Durable (λ Σ hG, P Σ hG ∧ Q Σ hG)%I.
  Proof. iIntros (H1 H2 ??). rewrite ?durable post_crash_and //. Qed.

  Global Instance pure_durable (P: Prop) :
    Durable (λ _ _, ⌜ P ⌝%I).
  Proof. iIntros (???). by iApply post_crash_pure. Qed.

  Global Instance exist_durable {A} Ψ:
    (∀ x : A, Durable (λ Σ hG, Ψ Σ hG x)) → Durable (λ Σ hG, (∃ x, Ψ Σ hG x)%I).
  Proof. iIntros (???). iApply post_crash_exists. iIntros (?). iApply H. Qed.

  Global Instance forall_durable {A} Ψ:
    (∀ x : A, Durable (λ Σ hG, Ψ Σ hG x)) → Durable (λ Σ hG, (∀ x, Ψ Σ hG x)%I).
  Proof. iIntros (???). iApply post_crash_forall. iIntros (?). iApply H. Qed.

  Lemma durable_proper P Q:
    Durable P →
    (∀ Σ hG, P Σ hG ⊣⊢ Q Σ hG) →
    Durable Q.
  Proof.
    rewrite /Durable.
    iIntros (HD Hwand ??) "HQ".
    iApply post_crash_mono; last first.
    { iApply HD. iApply Hwand; eauto. }
    iIntros. iApply Hwand; eauto.
  Qed.

  Global Instance big_sepL_durable:
    ∀ (A : Type) (Φ : ∀ Σ, heapG Σ → nat → A → iProp Σ) (l : list A),
    (∀ (k : nat) (x : A), Durable (λ Σ hG, Φ Σ hG k x)) →
    Durable (λ Σ hG, [∗ list] k↦x ∈ l, Φ Σ hG k x)%I.
  Proof.
    intros.
    cut (∀ n, Durable (λ Σ hG, [∗ list] k↦x ∈ l, Φ Σ hG (n + k)%nat x)%I).
    { intros Hres. specialize (Hres O). eauto. }

    induction l => n.
    - rewrite //=. apply _.
    - rewrite //=. apply sep_durable; eauto.
      eapply durable_proper; first eapply (IHl (S n)).
      intros.
      setoid_rewrite Nat.add_succ_r.
      setoid_rewrite <-Nat.add_succ_l.
      eauto.
  Qed.
End durable.
End goose_lang.


