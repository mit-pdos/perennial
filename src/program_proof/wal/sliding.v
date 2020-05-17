From RecordUpdate Require Import RecordSet.
From Tactical Require Import SimplMatch.

From Perennial.Helpers Require Export NamedProps List Integers Tactics.
(* TODO: I failed to get a reasonable setup with stdpp and ssreflect and such
without this, but it's really importing too much (we don't need the IPM here) *)
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Export wal.lib wal.highest.

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
    word.add σ.(start) (U64 $ Z.of_nat $ length σ.(log)).
  Definition memEnd σ : Z :=
    int.val σ.(start) + length σ.(log).
  Definition numMutable (σ:t): u64 :=
    word.sub σ.(mutable) σ.(start).
  Definition addrPosMap (σ:t): gmap u64 u64 :=
    compute_memLogMap σ.(log) σ.(start).
  Definition logIndex (σ:t) (pos: u64) : nat :=
    (int.nat pos - int.nat σ.(start))%nat.

  Definition wf (σ:t) :=
    int.val σ.(start) ≤ int.val σ.(mutable) ∧
    int.val σ.(start) + length σ.(log) < 2^64 ∧
    int.val σ.(mutable) - int.val σ.(start) <= length σ.(log).

  Theorem memEnd_ok σ :
    wf σ -> int.val (endPos σ) = memEnd σ.
  Proof.
    rewrite /wf /endPos /memEnd; intros.
    word.
  Qed.
End slidingM.

Definition memWrite_one memLog (u: update.t) : slidingM.t :=
  match find_highest_index (update.addr <$> memLog.(slidingM.log)) u.(update.addr) with
  | Some i => if decide (int.val memLog.(slidingM.mutable) - int.val memLog.(slidingM.start) ≤ i) then
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
  destruct matches.
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
  induction l; simpl; intros.
  - congruence.
  - destruct matches in *; try inversion H; subst.
    + destruct (IHl n0) as (l1 & l2 & (-> & Hnotin & <-)); auto.
      exists (a :: l1), l2; eauto.
    + exists [], l.
      split; auto.
      eapply find_highest_index_none_not_in in Heqo; auto.
    + apply fmap_Some_1 in H as [n' [? ->]].
      eapply IHl in H as (l1 & l2 & (-> & Hnotin & <-)).
      exists (a::l1), l2; eauto.
Qed.

Theorem apply_upds_insert_other upds (z: Z) (a: u64) b d :
  z ≠ int.val a →
  apply_upds upds (<[int.val a := b]> d) !! z =
  apply_upds upds d !! z.
Proof.
  revert z a b d.
  induction upds; simpl; intros.
  - rewrite lookup_insert_ne; auto.
  - destruct a as [a b'].
    destruct (decide (int.val a = int.val a0)).
    + rewrite e.
      rewrite insert_insert //.
    + rewrite insert_commute; auto.
Qed.

Theorem apply_upds_lookup_insert_highest upds (a: u64) b d :
  a ∉ update.addr <$> upds →
  apply_upds upds (<[int.val a:=b]> d) !! int.val a = Some b.
Proof.
  revert a b d.
  induction upds; simpl; intros.
  - rewrite lookup_insert //.
  - destruct a as [a b']; simpl in *.
    apply not_elem_of_cons in H as [Hneq Hnotin].
    rewrite apply_upds_insert_other; auto.
    apply not_inj; auto.
Qed.

Theorem apply_upds_insert_commute upds (a: u64) b d :
  a ∉ update.addr <$> upds →
  apply_upds upds (<[int.val a := b]> d) =
  <[int.val a := b]> (apply_upds upds d).
Proof.
  intros Hnotin.
  apply map_eq; intros z.
  destruct (decide (z = int.val a)); subst.
  2: {
    rewrite apply_upds_insert_other; auto.
    rewrite lookup_insert_ne; auto.
  }
  rewrite lookup_insert.
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
    destruct matches; simpl;
      (* the non-aborption cases are easy *)
      try rewrite apply_upds_app; auto.
    eapply find_highest_index_Some_split in Heqo as (poss1 & poss2 & (Heq & Hnotin & Hlen)).
    apply fmap_app_inv in Heq as (upd1 & upd2' & (-> & Heq%eq_sym & ->)).
    simpl in Heq, Hnotin.
    apply fmap_cons_inv in Heq as (u & upd2 & (-> & -> & ->)).
    destruct u as [a b'].
    simpl in Hnotin.
    autorewrite with len in Hlen; subst.
    rewrite -> insert_app_r_alt by len.
    rewrite minus_diag.
    simpl.
    rewrite !apply_upds_app.
    simpl.
    generalize dependent (apply_upds upd1 d); intros d'.
    rewrite !apply_upds_insert_commute; auto.
    rewrite insert_insert //.
Qed.
