From iris.proofmode Require Import tactics.
From Perennial Require Import NamedProps.

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

  Global Instance restore_impl_proper :
    Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) Restore.
  Proof. unseal; solve_proper. Qed.

  Theorem restore_sep R P P1 P2 Q :
    P ⊣⊢ P1 ∗ P2 →
    Restore R P Q -∗ P1 ∗ Restore R P2 (P1 ∗ Q).
  Proof.
    intros Hequiv.
    rewrite Hequiv.
    unseal.
    iIntros "[[HP1 HP2] #HPR]".
    iFrame "HP1 HP2".
    iIntros "!> HP2 [HP1 HQ]".
    iApply ("HPR" with "[$] [$]").
  Qed.

  Global Instance restore_IntoSep R P P1 P2 Q :
    IntoSep P P1 P2 →
    FromSep P P1 P2 →
    IntoSep (Restore R P Q) P1 (Restore R P2 (P1 ∗ Q)) | 20.
  Proof.
    rewrite /IntoSep /FromSep.
    iIntros (HP_split HQ_join) "HP".
    iApply (restore_sep with "HP").
    iSplit; auto.
    - iApply HP_split.
    - iApply HQ_join.
  Qed.

  Global Instance restore_is_splittable R P Q :
    IsSplittable P →
    IsSplittable (Restore R P Q).
  Proof. Qed.

  Global Instance restore_last_named_is_splittable R P name Q :
    IsSplittable (Restore R (named name P) Q).
  Proof. Qed.

  (* if we have emp, don't star onto it, just replace it *)
  Global Instance restore_IntoSep_emp R P P1 P2 :
    IntoSep P P1 P2 →
    FromSep P P1 P2 →
    IntoSep (Restore R P emp) P1 (Restore R P2 P1) | 19.
  Proof.
    iIntros (??).
    rewrite /IntoSep.
    iIntros "HP".
    iDestruct "HP" as "[$ H]".
    rewrite right_id //.
  Qed.

  Global Instance restore_IntoSep_persistent_1 R P P1 P2 Q `{BiAffine PROP} :
    IntoSep P P1 P2 →
    FromSep P P1 P2 →
    (* NOTE: need Persistent to be later so resolving IntoSep resolves P1
    first *)
    Persistent P1 →
    IntoSep (Restore R P Q) P1 (Restore R P2 Q) | 5.
  Proof.
    unseal.
    rewrite /IntoSep /FromSep.
    iIntros (HP_split HP_join ?) "[HP #HR]".
    iDestruct (HP_split with "HP") as "[#HP1 $]".
    iFrame "HP1".
    iIntros "!> HP2".
    iApply "HR".
    iApply (HP_join with "[$]").
  Qed.

  Global Instance restore_IntoExist R Q {A} P (Φ: A → PROP) name :
    IntoExist P Φ name →
    FromExist P Φ →
    IntoExist (Restore R P Q) (λ x, Restore R (Φ x) Q) name.
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

  Global Instance restore_is_exists R P Q :
    IsExistential P →
    IsExistential (Restore R P Q).
  Proof. Qed.

  Global Instance restore_finish_Persistent R P Q `{!Persistent P} `{BiAffine PROP} :
    IntoSep (Restore R P Q) P (Restore R emp Q).
  Proof.
    unseal.
    rewrite /IntoSep.
    iIntros "[#HP #HR]".
    iSpecialize ("HR" with "HP").
    iFrame "HP".
    rewrite /Restore_def; iFrame.
    rewrite left_id.
    iIntros "!> _".
    iFrame "#".
  Qed.

  Global Instance restore_finish_IntoSep R P Q :
    IntoSep (Restore R P Q) P (Restore R emp (P ∗ Q)) | 30.
  Proof.
    unseal.
    rewrite /IntoSep.
    iIntros "[$ #HR]".
    rewrite /Restore_def; iFrame.
    rewrite left_id.
    iIntros "!> _".
    iIntros "[? ?]".
    iApply ("HR" with "[$] [$]").
  Qed.

  (* if we have emp, don't star onto it, just replace it *)
  Global Instance restore_finish_IntoSep_emp R P :
    IntoSep (Restore R P emp) P (Restore R emp P) | 29.
  Proof.
    rewrite /IntoSep.
    iIntros "[$ HR]".
    rewrite right_id //.
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

Ltac iNamedRestorable i :=
  let j := iFresh in
  iDestruct (restore_intro with i) as j;
  iNamed j;
  (* we could do this last part with a tac_ theorem that always deleted j,
  combining these two steps (and also avoiding the need for a fresh name at
  all) *)
  let pat := constr:(intro_patterns.IIntuitionistic (intro_patterns.IIdent i)) in
  iDestruct (restore_elim with j) as pat; iClear j.

(* TODO: could use a tactic to reconstruct a Restorable using either hypotheses
or other Restorables *)

Section tests.
  Context {PROP:bi}.
  Context `{BiAffine PROP}.
  Implicit Types (P Q R:PROP).

  Definition all3 P1 P2 P3: PROP :=
    ("HP1" ∷ P1 ∗ "HP2" ∷ P2 ∗ "HP3" ∷ P3)%I.

  Theorem example1 P1 P2 P3 :
    all3 P1 P2 P3 -∗ P2 ∗ (P2 -∗ all3 P1 P2 P3).
  Proof.
    iIntros "H".
    iNamedRestorable "H".
    iFrame "HP2".
    iIntros "HP2".
    iApply "H"; iFrame.
  Qed.

  Definition absr P1 P2 P3 :=
    ("HP1" ∷ P1 ∗ "#HP2" ∷ □P2 ∗ "HP3" ∷ P3)%I.

  Theorem example2 P1 P2 P3 :
    absr P1 P2 P3 -∗ P2 ∗ P3 ∗ (P3 -∗ absr P1 P2 P3).
  Proof.
    iIntros "H".
    iNamedRestorable "H".
    iFrame "HP3".
    iSplitL ""; [ iFrame "#" | ].
    iIntros "HP3".
    iApply "H"; iFrame.
  Qed.

  Definition absr' P1 P2 (Φ: nat → PROP): PROP :=
    ("#HP1" ∷ □P1 ∗
     "Hn" ∷ ∃ n, "Hn1" ∷ Φ (n+1) ∗ "HP2" ∷ P2)%I.

  Theorem example3 P1 P2 Φ :
    absr' P1 P2 Φ -∗ P2 ∗ (P2 -∗ absr' P1 P2 Φ).
  Proof.
    iIntros "H".
    iNamedRestorable "H".
    iNamedRestorable "Hn".
    iSplitL "HP2"; [ iFrame | ].
    iIntros "HP2".
    (* TODO: slightly awkward because we have to restore up the hierarchy, using
       [iApply] again for composites *)
    iApply "H".
    iApply "Hn"; iFrame.
  Qed.

End tests.
