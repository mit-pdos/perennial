From iris.proofmode Require Import tactics.

(** Experimental library to destruct a proposition while retaining how to
restore it. *)

Section bi.
  Context {PROP:bi}.
  Implicit Types (P Q R:PROP).
  Bind Scope bi_scope with PROP.

  Definition Restore_def R P Q: PROP :=
    (P ∗ □(P -∗ Q -∗ R))%I.
  Definition Restore_aux : seal (@Restore_def). Proof. by eexists. Qed.
  Definition Restore := unseal Restore_aux.
  Definition Restore_eq : @Restore = @Restore_def := Restore_aux.(seal_eq).
  Arguments Restore (_ _ _)%bi_scope.

  Ltac unseal := rewrite Restore_eq.

  Theorem restore_intro P :
    P -∗ Restore P P emp.
  Proof.
    unseal.
    iIntros "$".
    iIntros "!> $".
    auto.
  Qed.

  Global Instance restore_IntoSep R P P1 P2 Q :
    IntoSep P P1 P2 →
    FromSep P P1 P2 →
    IntoSep (Restore R P Q) P1 (Restore R P2 (P1 ∗ Q)) | 20.
  Proof.
    rewrite /IntoSep /FromSep.
    unseal.
    iIntros (HP_split HQ_join) "[HP #HPR]".
    iDestruct (HP_split with "HP") as "[HP1 HP2]".
    iFrame "HP1".
    iFrame "HP2".
    iIntros "!> HP2 [HP1 HQ]".
    iApply ("HPR" with "[HP1 HP2] [$]").
    iApply (HQ_join with "[$]").
  Qed.

  (* TODO: check precedence; this instance should be tried before restore_IntoSep *)
  Global Instance restore_IntoSep_persistent_1 R P P1 P2 Q `{!Persistent P1} `{BiAffine PROP} :
    IntoSep P P1 P2 →
    FromSep P P1 P2 →
    IntoSep (Restore R P Q) P1 (Restore R P2 Q) | 10.
  Proof.
    unseal.
    rewrite /IntoSep /FromSep.
    iIntros (HP_split HP_join) "[HP #HR]".
    iDestruct (HP_split with "HP") as "[#HP1 $]".
    iFrame "HP1".
    iIntros "!> HP2".
    iApply "HR".
    iApply (HP_join with "[$]").
  Qed.

  Global Instance restore_IntoExist R Q {A} P (Φ: A → PROP) :
    IntoExist P Φ →
    FromExist P Φ →
    IntoExist (Restore R P Q) (λ x, Restore R (Φ x) Q).
  Proof.
    unseal.
    rewrite /IntoExist /FromExist.
    iIntros (HP_ex HΦ_ex) "[HP #HR]".
    iDestruct (HP_ex with "HP") as (x) "HΦ".
    iExists x; iFrame.
    iIntros "!> HΦ".
    iApply "HR".
    iApply HΦ_ex; eauto.
  Qed.

  Theorem restore_finish R P Q :
    Restore R P Q -∗ P ∗ Restore R emp (P ∗ Q).
  Proof.
    unseal.
    iIntros "[$ #HR]".
    rewrite /Restore_def; iFrame.
    rewrite left_id.
    iIntros "!> _".
    iIntros "[? ?]".
    iApply ("HR" with "[$] [$]").
  Qed.

  Global Instance restore_finish_IntoSep R P Q :
    IntoSep (Restore R P Q) P (Restore R emp (P ∗ Q)) | 30.
  Proof.
    rewrite /IntoSep.
    iApply restore_finish.
  Qed.

  (* not an instance so that applying restore_elim destroys the Restore *)
  Theorem restore_done_persistent R Q :
    Persistent (Restore R emp Q).
  Proof. unseal. apply _. Qed.

  Theorem restore_elim R Q :
    Restore R emp Q -∗ □ (Q -∗ R).
  Proof.
    unseal.
    iIntros "[_ #HR] !>".
    by iApply "HR".
  Qed.

End bi.

Section tests.
  Context {PROP:bi}.
  Context `{BiAffine PROP}.
  Implicit Types (P Q R:PROP).

  Definition all3 P1 P2 P3 :=
    (P1 ∗ P2 ∗ P3)%I.

  Theorem example1 P1 P2 P3 :
    all3 P1 P2 P3 -∗ P2 ∗ (P2 -∗ all3 P1 P2 P3).
  Proof.
    iIntros "H".
    iDestruct (restore_intro with "H") as "H".
    iDestruct "H" as "(HP1&HP2&HP3&H)".
    iDestruct (restore_elim with "H") as "#Hall3"; iClear "H".
    iFrame "HP2".
    iIntros "HP2".
    iApply "Hall3"; iFrame.
  Qed.

End tests.
