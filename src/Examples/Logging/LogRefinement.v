From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement.
From RecoveryRefinement.Examples.Logging Require Import LogAPI LogImpl.
From RecoveryRefinement.Examples Require Import ExMach.WeakestPre ExMach.RefinementAdequacy.

Unset Implicit Arguments.

Canonical Structure BufStateC := leibnizC BufState.

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (Log.Op) (Log.l) Σ,
            !inG Σ (authR (optionUR (exclR (prodC natC natC)))),
            !inG Σ (authR (optionUR (exclR (listC (prodC natC natC))))),
            !inG Σ (authR (optionUR (exclR (listC natC)))),
            !inG Σ (authR (optionUR (exclR natC))),
            !inG Σ (authR (optionUR (exclR BufStateC)))}.
  Import ExMach.

  (* Definition ptr_map (ptr_val : nat) (pcurr: nat * nat) (pother: nat * nat) :=
    (ptr_addr d↦ ptr_val ∗
     (read_addrs ptr_val).1 d↦ pcurr.1 ∗
     (read_addrs ptr_val).2 d↦ pcurr.2 ∗
     (write_addrs ptr_val).1 d↦ pother.1 ∗
     (write_addrs ptr_val).2 d↦ pother.2)%I. *)

  Definition txn_map start (txn: nat * nat) :=
    (start m↦ txn.1 ∗ (1+start) m↦ txn.2)%I.

  Definition buffer_map (s:BufState) (txns: list (nat*nat)) :=
    (state m↦ enc_state s ∗
           match s with
           | Empty => emp
           | Txn1 => (∃ txn, ⌜txns = [txn]⌝ ∗
                                         txn_map txn1_start txn)
           | Txn2 => (∃ txn, ⌜txns = [txn]⌝ ∗
                                         txn_map txn2_start txn)
           | Txn12 => (∃ txn1 txn2, ⌜txns = [txn1; txn2]⌝ ∗
                                                       txn_map txn1_start txn1 ∗
                                                       txn_map txn2_start txn2)
           | Txn21 => ∃ txn1 txn2, ⌜txns = [txn1; txn2]⌝ ∗
                                                      txn_map txn2_start txn1 ∗
                                                      txn_map txn1_start txn2
     end)%I.

  Definition txn_free start :=
    (∃ txn, txn_map start txn)%I.

  Definition free_buffer_map (s:BufState) :=
    (match s with
     | Empty => txn_free txn1_start ∗ txn_free txn2_start
     | Txn1 => txn_free txn2_start
     | Txn2 => txn_free txn1_start
     | Txn12 => emp
     | Txn21 => emp
     end)%I.

  Record ghost_names :=
    { γslock : gname;
      γstate : gname;
      γtxns : gname;
      γdlock : gname;
      γlog : gname; }.

  Fixpoint flatten_txns (txns: list (nat*nat)) : list nat :=
    match txns with
    | nil => nil
    | (v1, v2) :: txns' => v1 :: v2 :: flatten_txns txns'
    end.

  Definition ExecInner names :=
    (∃ (s:BufState) (txns: list (nat*nat)) (log: list nat),
        own (names.(γstate)) (● (Excl' s)) ∗
            own (names.(γtxns)) (● (Excl' txns)) ∗
            own (names.(γlog)) (● (Excl' log)) ∗
            buffer_map s txns ∗
            source_state {| Log.mem_buf := flatten_txns txns;
                            Log.disk_log := log; |} ∗
            free_buffer_map s)%I.

  Definition StateLockInv names :=
    (∃ s txns,
        buffer_map s txns ∗
                   free_buffer_map s ∗
                   own (names.(γtxns)) (◯ (Excl' txns)))%I.

  Fixpoint log_map (i: nat) log :=
    (match log with
     | nil => emp
     | x::log' => log_idx i d↦ x ∗ log_map (1+i) log'
     end)%I.

  Definition ExecDiskInv :=
    (∃ (log: list nat),
        log_len d↦ length log ∗
                log_map 0 log)%I.

  Definition CrashInner :=
    (∃ (log: list nat),
        source_state {| Log.mem_buf := nil;
                        Log.disk_log := log; |} ∗
                     free_buffer_map Empty ∗
                     state_lock m↦ 0)%I.

  Definition lN : namespace := nroot.@"lock".
  Definition iN : namespace := nroot.@"inner".

  Definition ExecInv :=
    (source_ctx ∗ ∃ (names:ghost_names),
          is_lock lN names.(γslock) state_lock (StateLockInv names) ∗
                                    inv iN (ExecInner names ∗ ExecDiskInv))%I.

  Definition CrashInv :=
    (source_ctx ∗ inv iN CrashInner)%I.

End refinement_triples.
