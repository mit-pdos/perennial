From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Export NamedProps List Integers Tactics.
(* TODO: I failed to get a reasonable setup with stdpp and ssreflect and such
without this, but it's really importing too much (we don't need the IPM here) *)
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Export wal.lib wal.highest.
From Perennial.program_proof Require Export wal.boundaries.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

Module slidingM.
  Record t :=
    mk { log: list update.t;
         start: u64;
         mutable: u64; }.
  Global Instance _eta : Settable _ := settable! mk <log; start; mutable>.
  Global Instance _witness : Inhabited t := populate!.

  Definition endPos (σ:t): u64 :=
    word.add σ.(start) (W64 $ Z.of_nat $ length σ.(log)).
  Definition memEnd σ : Z :=
    uint.Z σ.(start) + length σ.(log).
  Definition numMutable (σ:t): u64 :=
    word.sub σ.(mutable) σ.(start).
  Definition addrPosMap (σ:t): gmap u64 u64 :=
    compute_memLogMap σ.(log) σ.(start).
  Definition logIndex (σ:t) (pos: u64) : nat :=
    (uint.nat pos - uint.nat σ.(start))%nat.

  Definition wf (σ:t) :=
    uint.Z σ.(start) ≤ uint.Z σ.(mutable) ∧
    uint.Z σ.(start) + length σ.(log) < 2^64 ∧
    uint.Z σ.(mutable) - uint.Z σ.(start) <= length σ.(log).

  Theorem memEnd_ok σ :
    wf σ -> uint.Z (endPos σ) = memEnd σ.
  Proof.
    rewrite /wf /endPos /memEnd; intros.
    word.
  Qed.
End slidingM.

Definition memWrite_one memLog (u: update.t) : slidingM.t :=
  match find_highest_index (update.addr <$> memLog.(slidingM.log)) u.(update.addr) with
  | Some i => if decide (uint.Z memLog.(slidingM.mutable) - uint.Z memLog.(slidingM.start) ≤ i) then
                set slidingM.log <[i := u]> memLog
              else
                set slidingM.log (λ log, log ++ [u]) memLog
  | None => set slidingM.log (λ log, log ++ [u]) memLog
  end.

(* pure version of memWrite; equivalent to [log ++ upds], except for absorption *)
Definition memWrite memLog (upds: list update.t): slidingM.t :=
  foldl memWrite_one memLog upds.

Local Lemma memWrite_one_same_mutable_and_start memLog u :
  (memWrite_one memLog u).(slidingM.mutable) = memLog.(slidingM.mutable) ∧
  (memWrite_one memLog u).(slidingM.start) = memLog.(slidingM.start).
Proof.
  revert memLog.
  intros.
  rewrite /memWrite_one.
  destruct (find_highest_index _ _) eqn:?; auto.
  destruct (decide _); auto.
Qed.

Lemma memWrite_one_same_mutable memLog u :
  (memWrite_one memLog u).(slidingM.mutable) = memLog.(slidingM.mutable).
Proof.
  apply memWrite_one_same_mutable_and_start.
Qed.

Lemma memWrite_one_same_start memLog u :
  (memWrite_one memLog u).(slidingM.start) = memLog.(slidingM.start).
Proof.
  apply memWrite_one_same_mutable_and_start.
Qed.

Local Lemma memWrite_same_mutable_and_start memLog upds :
  (memWrite memLog upds).(slidingM.mutable) = memLog.(slidingM.mutable) ∧
  (memWrite memLog upds).(slidingM.start) = memLog.(slidingM.start).
Proof.
  revert memLog.
  induction upds; simpl; auto; intros.
  destruct (IHupds (memWrite_one memLog a)) as [-> ->].
  apply memWrite_one_same_mutable_and_start.
Qed.

Lemma memWrite_same_mutable memLog upds :
  (memWrite memLog upds).(slidingM.mutable) = memLog.(slidingM.mutable).
Proof.
  apply memWrite_same_mutable_and_start.
Qed.

Lemma memWrite_same_start memLog upds :
  (memWrite memLog upds).(slidingM.start) = memLog.(slidingM.start).
Proof.
  apply memWrite_same_mutable_and_start.
Qed.

Lemma memWrite_end memLog upds :
  slidingM.memEnd (memWrite memLog upds) ≤ slidingM.memEnd memLog + length upds.
Proof.
  revert memLog.
  induction upds; simpl; auto; intros.
  - lia.
  - etransitivity; [ apply IHupds | ].
    rewrite /memWrite_one.
    destruct (find_highest_index (update.addr <$> memLog.(slidingM.log)) a.(update.addr)).
    1: destruct (decide (uint.Z memLog.(slidingM.mutable) - uint.Z memLog.(slidingM.start) ≤ n)).
    all: rewrite /slidingM.memEnd ?length_app ?length_insert /=.
    all: try lia.
Qed.

Lemma memWrite_app1 memLog upds u :
  memWrite memLog (upds ++ [u]) = memWrite_one (memWrite memLog upds) u.
Proof.
  rewrite /memWrite foldl_app //=.
Qed.

Theorem find_highest_index_Some_split `{EqDecision A} (l: list A) (x: A) n :
  find_highest_index l x = Some n ->
  exists l1 l2, l = l1 ++ [x] ++ l2 ∧
           x ∉ l2 ∧
           length l1 = n.
Proof.
  revert n.
  induction l as [|a l' IHl]; simpl; intros.
  - congruence.
  - destruct (decide (x = a)); subst.
    {
      destruct (find_highest_index _ _) eqn:?.
      + inv H.
        destruct (IHl n0) as (l1 & l2 & (-> & Hnotin & <-)); auto.
        exists (a :: l1), l2; eauto.
      + inv H.
        exists [], l'.
        split; auto.
        eapply find_highest_index_none_not_in in Heqo; auto.
    }
    apply fmap_Some_1 in H as [n' [? ->]].
    eapply IHl in H as (l1 & l2 & (-> & Hnotin & <-)).
    exists (a::l1), l2; eauto.
Qed.

Theorem apply_upds_insert_other upds (z: Z) (a: u64) b d :
  z ≠ uint.Z a →
  apply_upds upds (<[uint.Z a := b]> d) !! z =
  apply_upds upds d !! z.
Proof.
  revert z a b d.
  induction upds; simpl; intros.
  - rewrite lookup_insert_ne; auto.
  - destruct a as [a b'].
    destruct (decide (uint.Z a = uint.Z a0)).
    + rewrite e.
      rewrite insert_insert_eq //.
    + rewrite insert_insert_ne; auto.
Qed.

Theorem apply_upds_lookup_insert_highest upds (a: u64) b d :
  a ∉ update.addr <$> upds →
  apply_upds upds (<[uint.Z a:=b]> d) !! uint.Z a = Some b.
Proof.
  revert a b d.
  induction upds; simpl; intros.
  - rewrite lookup_insert_eq //.
  - destruct a as [a b']; simpl in *.
    apply not_elem_of_cons in H as [Hneq Hnotin].
    rewrite apply_upds_insert_other; auto.
    apply not_inj; auto.
Qed.

Theorem apply_upds_insert_commute upds (a: u64) b d :
  a ∉ update.addr <$> upds →
  apply_upds upds (<[uint.Z a := b]> d) =
  <[uint.Z a := b]> (apply_upds upds d).
Proof.
  intros Hnotin.
  apply map_eq; intros z.
  destruct (decide (z = uint.Z a)); subst.
  2: {
    rewrite apply_upds_insert_other; auto.
    rewrite lookup_insert_ne; auto.
  }
  rewrite lookup_insert_eq.
  rewrite apply_upds_lookup_insert_highest; auto.
Qed.

Theorem memWrite_apply_upds memLog upds d :
  apply_upds (memWrite memLog upds).(slidingM.log) d =
  apply_upds (memLog.(slidingM.log) ++ upds) d.
Proof.
  revert d memLog.
  induction upds; simpl; intros.
  - rewrite app_nil_r //.
  - rewrite IHupds.
    rewrite cons_middle.
    rewrite app_assoc.
    rewrite !apply_upds_app.
    f_equal.
    destruct a as [a b]; simpl.
    rewrite /memWrite_one.
    destruct (find_highest_index _ _) eqn:?; simpl;
      try rewrite apply_upds_app //.
    destruct (decide _);
      try rewrite apply_upds_app //.
    simpl.
    eapply find_highest_index_Some_split in Heqo as (poss1 & poss2 & (Heq & Hnotin & Hlen)).
    apply fmap_app_inv in Heq as (upd1 & upd2' & (-> & Heq%eq_sym & ->)).
    simpl in Heq, Hnotin.
    apply fmap_cons_inv in Heq as (u & upd2 & (-> & -> & ->)).
    destruct u as [a b'].
    simpl in Hnotin.
    autorewrite with len in Hlen; subst.
    rewrite -> insert_app_r_alt by len.
    rewrite Nat.sub_diag.
    simpl.
    rewrite !apply_upds_app.
    simpl.
    generalize dependent (apply_upds upd1 d); intros d'.
    rewrite !apply_upds_insert_commute; auto.
    rewrite insert_insert_eq //.
Qed.

Lemma memWrite_one_NoDup σ u :
  NoDup (update.addr <$> σ.(slidingM.log)) →
  uint.Z σ.(slidingM.mutable) - uint.Z σ.(slidingM.start) = 0 →
  NoDup (update.addr <$> (memWrite_one σ u).(slidingM.log)).
Proof.
  intros Hnodup Hro_len.
  rewrite /memWrite_one.
  destruct (find_highest_index _) as [i|] eqn:Hlookup; simpl.
  - rewrite Hro_len.
    rewrite -> decide_True by word.
    simpl.
    rewrite list_fmap_insert.
    rewrite list_insert_id //.
    apply find_highest_index_ok' in Hlookup as [Hlookup _].
    auto.
  - rewrite fmap_app.
    apply NoDup_app.
    split_and!; auto.
    + simpl.
      intros x Hx ->%list_elem_of_singleton.
      apply list_elem_of_lookup in Hx as [txn_id Hx].
      eapply find_highest_index_none in Hlookup; eauto.
    + simpl.
      apply NoDup_singleton.
Qed.

Lemma memWrite_all_NoDup σ bufs:
  NoDup (update.addr <$> σ.(slidingM.log)) →
  uint.Z σ.(slidingM.mutable) - uint.Z σ.(slidingM.start) = 0 →
  NoDup (update.addr <$> (memWrite σ bufs).(slidingM.log)).
Proof.
  generalize dependent σ.
  induction bufs as [|u bufs]; simpl; intuition.
  apply IHbufs.
  - apply memWrite_one_NoDup; auto.
  - rewrite memWrite_one_same_start memWrite_one_same_mutable //.
Qed.

Theorem memWrite_memWrite_generic memLog upds :
  memWrite memLog upds =
  set slidingM.log
    (λ log,
      memWrite_generic
        (slidingM.logIndex memLog memLog.(slidingM.mutable)) log upds
    ) memLog.
Proof.
  destruct memLog.
  rewrite /set /=.
  rewrite -(rev_involutive upds).
  induction (rev upds) as [|upd updst Hind]; first by reflexivity.
  simpl.
  rewrite memWrite_app1 memWrite_generic_app Hind /=
    /memWrite_one /memWrite_one_generic /set /slidingM.logIndex /=.
  destruct (find_highest_index _ _) as [i|] eqn:Hhighest;
    last by reflexivity.
  destruct (decide _) as [Hcmp|Hcmp].
  {
    f_equal.
    rewrite decide_True; last by lia.
    reflexivity.
  }
  rewrite decide_False; last by word.
  reflexivity.
Qed.
