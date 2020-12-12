From Perennial.algebra Require Import append_list.
From Perennial.Helpers Require Import Integers List Map.
From Perennial.program_proof.wal Require Import abstraction.

From Perennial.program_proof Require Import proof_prelude.

(*
txns: list (u64 * list update.t)
txn_id is referenced by pos, log < pos contains updates through and including upds
[txn_id: (pos, upds)]
*)

Class txns_ctxG Σ := { txns_ctx_alist :> alistG Σ (u64 * list update.t) }.
Definition txns_ctxΣ : gFunctors := #[alistΣ (u64 * list update.t)].

Instance subG_txns_ctx Σ : subG txns_ctxΣ Σ → txns_ctxG Σ.
Proof. solve_inG. Qed.

Section goose.
Context `{!heapG Σ} `{!txns_ctxG Σ}.
Implicit Types (γ:gname).

Definition txn_val γ txn_id (txn: u64 * list update.t): iProp Σ :=
  list_el γ txn_id txn.

Definition txn_pos γ txn_id (pos: u64) : iProp Σ :=
  ∃ upds, txn_val γ txn_id (pos, upds).

Definition txns_ctx γ txns : iProp Σ := list_ctx γ 1 txns.

Theorem alloc_txns_ctx E txns :
  ⊢ |={E}=> ∃ γtxns, txns_ctx γtxns txns.
Proof.
  iMod (alist_alloc txns) as (γtxns) "Hctx".
  iExists γtxns.
  rewrite /txns_ctx //=.
Qed.

Theorem txn_val_to_pos γ txn_id pos upds :
  txn_val γ txn_id (pos, upds) -∗ txn_pos γ txn_id pos.
Proof.
  rewrite /txn_pos.
  iIntros "Hval".
  iExists _; iFrame.
Qed.

Lemma txns_ctx_app {γ} txns' txns : txns_ctx γ txns ==∗ txns_ctx γ (txns ++ txns').
Proof.
  rewrite /txns_ctx.
  iIntros "Hctx".
  by iMod (alist_app _ txns' with "Hctx") as "[$ _]".
Qed.

Global Instance txn_pos_timeless γ txn_id pos :
  Timeless (txn_pos γ txn_id pos) := _.

Global Instance txn_pos_persistent γ txn_id pos :
  Persistent (txn_pos γ txn_id pos) := _.

Definition txns_are γ (start: nat) (txns_sub: list (u64*list update.t)) : iProp Σ :=
  list_subseq γ start txns_sub.

Global Instance txns_are_Persistent γ start txns_sub : Persistent (txns_are γ start txns_sub).
Proof. apply _. Qed.

Theorem txns_are_sound γ txns start txns_sub :
  txns_ctx γ txns -∗
  txns_are γ start txns_sub -∗
  ⌜subslice start (start + length txns_sub)%nat txns = txns_sub⌝.
Proof.
  iIntros "Hctx Htxns_are".
  iDestruct (alist_subseq_lookup with "Hctx Htxns_are") as "$".
Qed.

Lemma txns_are_nil γ start : ⊢ txns_are γ start [].
Proof.
  iApply list_subseq_nil.
Qed.

(** * some facts about txn_ctx *)
Theorem txn_map_to_is_txn txns (txn_id: nat) (pos: u64) upds :
  list_to_imap txns !! txn_id = Some (pos, upds) ->
  is_txn txns txn_id pos.
Proof.
  rewrite /is_txn.
  rewrite lookup_list_to_imap.
  by intros ->.
Qed.

Theorem alloc_txn_pos pos upds γ txns E :
  txns_ctx γ txns ={E}=∗
  txns_ctx γ (txns ++ [(pos, upds)]) ∗ txn_val γ (length txns) (pos, upds).
Proof.
  iIntros "Hctx".
  iMod (alist_app1 (pos,upds) with "Hctx") as "[Hctx Hval]".
  by iFrame.
Qed.

Theorem txns_ctx_complete γ txns txn_id txn :
  txns !! txn_id = Some txn ->
  txns_ctx γ txns -∗ txn_val γ txn_id txn.
Proof.
  iIntros (Hlookup) "Hctx".
  iDestruct (alist_lookup_el with "Hctx") as "Hel"; eauto.
Qed.

Theorem txns_ctx_complete' γ txns txn_id txn :
  txns !! txn_id = Some txn ->
  ▷ txns_ctx γ txns -∗ ▷ txn_val γ txn_id txn ∗ ▷ txns_ctx γ txns.
Proof.
  iIntros (Hlookup) "Hctx".
  iDestruct (txns_ctx_complete with "Hctx") as "#Hel"; eauto.
Qed.

Theorem txns_ctx_txn_pos γ txns txn_id pos :
  is_txn txns txn_id pos ->
  txns_ctx γ txns -∗ txn_pos γ txn_id pos.
Proof.
  intros [txn [Hlookup ->]]%fmap_Some_1.
  rewrite txns_ctx_complete; eauto.
  iIntros "Htxn_val".
  destruct txn as [pos upds].
  iExists _; iFrame.
Qed.

Theorem txn_val_valid_general γ txns txn_id txn :
  txns_ctx γ txns -∗
  txn_val γ txn_id txn -∗
  ⌜txns !! txn_id = Some txn⌝.
Proof.
  iIntros "Hctx Htxn".
  iDestruct (alist_lookup with "Hctx Htxn") as %Hlookup.
  eauto.
Qed.

Theorem txn_pos_valid_general γ txns txn_id pos :
  txns_ctx γ txns -∗
  txn_pos γ txn_id pos -∗
  ⌜is_txn txns txn_id pos⌝.
Proof.
  iIntros "Hctx Htxn".
  iDestruct "Htxn" as (upds) "Hval".
  iDestruct (alist_lookup with "Hctx Hval") as %Hlookup.
  iPureIntro.
  rewrite /is_txn Hlookup //.
Qed.

Global Instance txns_ctx_disc γ x: Discretizable (txns_ctx γ x).
Proof.
  rewrite /txns_ctx/list_ctx. apply _.
Qed.

End goose.
