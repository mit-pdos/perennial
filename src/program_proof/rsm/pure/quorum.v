From iris.proofmode Require Import proofmode.
From Perennial.program_proof.rsm.pure Require Import fin_sets.

Set Default Proof Using "Type".

Open Scope Z_scope.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section def.
  Context `{Countable A}.
  Implicit Type c q : gset A.

  Definition cquorum_size c q :=
    size c / 2 < size q.

  Definition cquorum c q :=
    q ⊆ c ∧ cquorum_size c q.

  Definition fquorum_size c q :=
    (3 * size c + 3) / 4 ≤ size q ∧ size c ≠ O.

  Definition fquorum c q :=
    q ⊆ c ∧ fquorum_size c q.

  Definition hcquorum_size c q :=
    size c / 4 < size q.

  Definition hcquorum c q :=
    q ⊆ c ∧ hcquorum_size c q.

End def.

Section lemma.
  Context `{Countable A}.
  Implicit Type c q : gset A.

  Lemma quorums_overlapped_raw c q1 q2 :
    q1 ⊆ c ->
    q2 ⊆ c ->
    size c < size q1 + size q2 ->
    ∃ x, x ∈ q1 ∧ x ∈ q2.
  Proof.
    intros Hq1 Hq2 Hsize.
    apply dec_stable.
    intros Hcontra.
    assert (Hdisjoint : q1 ## q2) by set_solver.
    apply size_union in Hdisjoint.
    assert (Hsubseteq : q1 ∪ q2 ⊆ c) by set_solver.
    apply subseteq_size in Hsubseteq.
    rewrite Hdisjoint in Hsubseteq.
    lia.
  Qed.

  Lemma cquorum_non_empty_c c q :
    cquorum c q -> c ≠ ∅.
  Proof.
    intros [Hle Hsize].
    apply subseteq_size in Hle.
    rewrite /cquorum_size in Hsize.
    rewrite -size_non_empty_iff_L.
    lia.
  Qed.

  Lemma cquorum_elem_of c q x :
    x ∈ q ->
    cquorum c q ->
    x ∈ c.
  Proof. intros Helem [Hincl _]. set_solver. Qed.

  Lemma quorums_overlapped c q1 q2 :
    (cquorum c q1 ∨ fquorum c q1) ->
    (cquorum c q2 ∨ fquorum c q2) ->
    ∃ x, x ∈ q1 ∧ x ∈ q2.
  Proof.
    intros Hq1 Hq2.
    assert (size c ≠ O).
    { rewrite size_non_empty_iff_L.
      destruct Hq1 as [Hc1 | Hf1], Hq2 as [Hc2 | Hf2]; try by eapply cquorum_non_empty_c.
      destruct Hf1 as [_ [_ Hnz]].
      by rewrite -size_non_empty_iff_L.
    }
    revert Hq1 Hq2.
    rewrite /cquorum /cquorum_size /fquorum /fquorum_size.
    intros [[Hle1 Hsize1] | [Hle1 Hsize1]] [[Hle2 Hsize2] | [Hle2 Hsize2]];
      (apply (quorums_overlapped_raw c); [done | done | lia]).
  Qed.

  Lemma hcquorum_fquorum_overlapped c q1 q2 :
    hcquorum c q1 ->
    fquorum c q2 ->
    ∃ x, x ∈ q1 ∧ x ∈ q2.
  Proof.
    intros Hq1 Hq2.
    destruct Hq1 as [Hincl1 Hsize1].
    destruct Hq2 as [Hincl2 Hsize2].
    apply (quorums_overlapped_raw c).
    { apply Hincl1. }
    { apply Hincl2. }
    rewrite /hcquorum_size in Hsize1.
    rewrite /fquorum_size in Hsize2.
    lia.
  Qed.

  Lemma cquorums_overlapped c q1 q2 :
    cquorum c q1 ->
    cquorum c q2 ->
    ∃ x, x ∈ q1 ∧ x ∈ q2.
  Proof.
    intros Hq1 Hq2.
    by eapply quorums_overlapped; left.
  Qed.

  Lemma quorums_sufficient c qc qf :
    cquorum_size c qc ->
    fquorum_size c qf ->
    2 * size c < size qc + 2 * size qf.
  Proof.
    rewrite /cquorum_size /fquorum_size.
    intros Hsizec Hsizef.
    lia.
  Qed.

  Lemma cquorum_non_empty_q c q :
    cquorum c q -> q ≠ ∅.
  Proof.
    intros Hquorum.
    pose proof (quorums_overlapped c q q) as (x & Helem & _).
    { by left. }
    { by left. }
    set_solver.
  Qed.

  Lemma cquorum_refl c :
    (1 ≤ size c)%nat ->
    cquorum c c.
  Proof.
    split; first done.
    rewrite /cquorum_size.
    lia.
  Qed.

  Lemma fquorum_non_empty_q c q :
    fquorum c q -> q ≠ ∅.
  Proof.
    intros (Hincl & Hsize & Hnz).
    rewrite -size_non_empty_iff_L.
    lia.
  Qed.

End lemma.
