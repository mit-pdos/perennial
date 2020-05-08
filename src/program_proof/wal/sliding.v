From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From RecordUpdate Require Import RecordSet.
From Tactical Require Import SimplMatch.

From Perennial.Helpers Require Export NamedProps List.

From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Export wal.lib.
From Perennial.program_proof Require Import wal.highest.
From Perennial.program_proof Require Import disk_lib.

Module slidingM.
  Record t :=
    mk { log: list update.t;
         start: u64;
         mutable: u64; }.
  Global Instance _eta : Settable _ := settable! mk <log; start; mutable>.
  Global Instance _witness : Inhabited t := populate!.

  Definition endPos (σ:t): u64 :=
    word.add σ.(start) (U64 $ Z.of_nat $ length σ.(log)).
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

Lemma memWrite_same_mutable_and_start memLog upds :
  (memWrite memLog upds).(slidingM.mutable) = memLog.(slidingM.mutable) ∧
  (memWrite memLog upds).(slidingM.start) = memLog.(slidingM.start).
Proof.
  revert memLog.
  induction upds; simpl; auto; intros.
  destruct (IHupds (memWrite_one memLog a)) as [-> ->].
  rewrite /memWrite_one.
  destruct memLog as [log start mutable]; simpl.
  destruct (find_highest_index (update.addr <$> log) a.(update.addr)); simpl; auto.
  destruct (decide (int.val mutable - int.val start ≤ n)); simpl; auto.
Qed.

Lemma memWrite_same_mutable memLog upds :
  (memWrite memLog upds).(slidingM.mutable) = memLog.(slidingM.mutable).
Proof.
  apply memWrite_same_mutable_and_start.
Qed.

Lemma memWrite_app1 memLog upds u :
  memWrite memLog (upds ++ [u]) = memWrite_one (memWrite memLog upds) u.
Proof.
  rewrite /memWrite foldl_app //=.
Qed.
