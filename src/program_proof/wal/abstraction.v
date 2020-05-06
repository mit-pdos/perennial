From RecordUpdate Require Import RecordSet.

From stdpp Require Import gmap.
From iris.algebra Require Import ofe.

From Perennial.Helpers Require Import Tactics Integers.
From Perennial.program_proof Require Import disk_lib.
From Perennial.goose_lang Require Import ffi.disk.

Module update.
  Record t :=
    mk { addr: u64;
         b: Block; }.
  Global Instance _eta: Settable _ := settable! mk <addr; b>.
  Global Instance _witness: Inhabited t := populate!.
End update.

Canonical Structure updateO := leibnizO update.t.
Canonical Structure blockO := leibnizO Block.
(* TODO: this one is super general, can it go somewhere else? *)
Canonical Structure u64O := leibnizO u64.

Definition LogSz: Z := 511.
Hint Unfold LogSz : word.

Definition disk := gmap Z Block.

Definition txn_upds (txns: list (u64 * list update.t)) : list update.t :=
  concat (snd <$> txns).

Module log_state.
  Record t :=
    mk {
        d: disk;
        txns: list (u64 * list update.t);
        (* installed_lb promises what will be read after a cache miss *)
        installed_lb: nat;
        (* durable_lb promises what will be on-disk after a crash *)
        durable_lb: nat;
      }.
  Global Instance _eta: Settable _ := settable! mk <d; txns; installed_lb; durable_lb>.
  Global Instance _witness: Inhabited t := populate!.

  Definition updates σ : list update.t := txn_upds σ.(txns).
End log_state.

Definition addr_wf (a: u64) (d: disk) :=
  2 + LogSz ≤ int.val a ∧
  ∃ (b: Block), d !! (int.val a) = Some b.

Definition addrs_wf (updates: list update.t) (d: disk) :=
  forall i u, updates !! i = Some u -> addr_wf (u.(update.addr)) d.

Definition wal_wf (s : log_state.t) :=
  addrs_wf (log_state.updates s) s.(log_state.d) ∧
  (* monotonicity of txnids  *)
  (forall (pos1 pos2: u64) (txn_id1 txn_id2: nat),
      (txn_id1 < txn_id2)%nat ->
      fst <$> s.(log_state.txns) !! txn_id1 = Some pos1 ->
      fst <$> s.(log_state.txns) !! txn_id2 = Some pos2 ->
      (* can get the same handle for two transactions due to absorption or
        empty transactions *)
      int.val pos1 ≤ int.val pos2) ∧
  s.(log_state.installed_lb) ≤ s.(log_state.durable_lb) ≤ length s.(log_state.txns).
