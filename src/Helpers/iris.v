From iris.proofmode Require Import tactics.
From iris Require Import base_logic.lib.invariants.

(** if the goal [Q] can be duplicated out of an invariant, we can access it
conveniently with this theorem (which weakens the normal invariant opening by
hiding the ability to open further invariants) *)
Theorem inv_dup_acc {Σ} `{!invG Σ} (Q: iProp Σ) N E (P: iProp Σ) :
  ↑N ⊆ E →
  inv N P -∗
  (P -∗ P ∗ Q) -∗
  |={E}=> ▷ Q.
Proof.
  iIntros (Hsub) "Hinv HPtoQ".
  iInv "Hinv" as "HP" "Hclose".
  iDestruct ("HPtoQ" with "HP") as "[HP HQ]".
  iMod ("Hclose" with "HP") as "_".
  iIntros "!> !>".
  iFrame.
Qed.

(** If the goal [Q] is persistent, we can derive it under a fupd by opening an
invariant and using the contents of the invariant without putting them back. In
practice this only works for the timeless part of P, which is expressed by
giving the assumption [▷P] but also providing an "except-0" modality ◇ around
the goal (the later can be stripped from [P] for any timeless components).

 The reason this is sound is informally because [P -∗ Q] can be upgraded to
 [P -∗ P ∗ Q] because [Q] is persistent. *)
Lemma inv_open_persistent `{!invG Σ} N E (P Q: iProp Σ) `{!Persistent Q} :
  ↑N ⊆ E →
  inv N P -∗
  (▷ P -∗ ◇ Q) -∗
  |={E}=> Q.
Proof.
  iIntros (?) "#Hinv HPQ".
  iInv "Hinv" as "HP".
  iModIntro.
  rewrite -fupd_except_0 -fupd_intro.
  iSplit; [done|].
  iApply ("HPQ" with "[$]").
Qed.
