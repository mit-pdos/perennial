From Perennial.algebra Require Import append_list.
From Perennial.Helpers Require Import Integers List Map.
From Perennial.program_proof.wal Require Import abstraction.

From Perennial.program_proof Require Import disk_prelude.

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

Lemma txns_are_unify γ txns start txns_sub1 txns_sub2 :
  txns_ctx γ txns -∗
  txns_are γ start txns_sub1 -∗
  txns_are γ start txns_sub2 -∗
  ⌜length txns_sub1 = length txns_sub2⌝ -∗
  ⌜txns_sub1 = txns_sub2⌝.
Proof.
  iIntros "Htxns_ctx Htxns_sub1 Htxns_sub2 %Hlen".
  iDestruct (txns_are_sound with "Htxns_ctx Htxns_sub1") as %<-.
  iDestruct (txns_are_sound with "Htxns_ctx Htxns_sub2") as %<-.
  rewrite <-Hlen.
  eauto.
Qed.

Lemma txns_are_nil γ start : ⊢ txns_are γ start [].
Proof.
  iApply list_subseq_nil.
Qed.

(** * some facts about txn_ctx *)
Theorem alloc_txn_pos pos upds γ txns :
  txns_ctx γ txns ==∗
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

(** * txns_ctx factory:

a way to remember that some [txn_val]s are valid even after a crash *)

(* the crux of this approach is this resource, which has an auth over the old
transactions in [γ] and connects them to the transactions in [γ']. [txn_val]s in
[γ] that are prior to the crash point can be used to get one in the new
generation. *)
Definition old_txn_factory γ crash_txn γ' : iProp Σ :=
  ∃ txns, txns_ctx γ txns ∗
  [∗ list] i↦txn ∈ (take (S crash_txn) txns), list_el γ' i txn.

Lemma txns_ctx_make_factory γ txns crash_txn γ' :
  txns_ctx γ txns -∗
  txns_ctx γ' (take (S crash_txn) txns) -∗
  old_txn_factory γ crash_txn γ' ∗ txns_ctx γ' (take (S crash_txn) txns).
Proof.
  rewrite {2 3}/txns_ctx /list_ctx /old_txn_factory.
  iIntros "Htxn [Hctx #Hels]".
  iFrame "#∗".
  iExists _; iFrame "#∗".
Qed.

Lemma old_txn_get γ γ' crash_txn txn_id txn :
  (txn_id ≤ crash_txn)%nat →
  old_txn_factory γ crash_txn γ' -∗
  txn_val γ txn_id txn -∗
  txn_val γ' txn_id txn.
Proof.
  iIntros (?) "Hfactory Hel".
  iDestruct "Hfactory" as (txns) "[Hctx Hels]".
  iDestruct (alist_lookup with "Hctx Hel") as %Hloookup.
  iDestruct (big_sepL_lookup with "Hels") as "$".
  rewrite -> lookup_take by lia. done.
Qed.

Lemma old_txn_get_pos γ γ' crash_txn txn_id pos :
  (txn_id ≤ crash_txn)%nat →
  old_txn_factory γ crash_txn γ' -∗
  txn_pos γ txn_id pos -∗
  txn_pos γ' txn_id pos.
Proof.
  iIntros (?) "Hfactory Hel".
  iDestruct "Hel" as (txn) "Hel".
  iExists txn.
  iApply (old_txn_get with "[$] [$]"); auto.
Qed.

Lemma old_txns_are_get γ γ' crash_txn start txns_sub :
  (start + length txns_sub ≤ S crash_txn)%nat →
  old_txn_factory γ crash_txn γ' -∗
  txns_are γ start txns_sub -∗
  txns_are γ' start txns_sub.
Proof.
  iIntros (Hbound) "Hfactory Htxns".
  iInduction txns_sub as [|txn txns] "IH" forall (start Hbound).
  - iApply txns_are_nil.
  - rewrite /txns_are /list_subseq.
    simpl in Hbound.
    rewrite !big_sepL_cons.
    iDestruct "Htxns" as "[Htxn Htxns]".
    rewrite Nat.add_0_r.
    iDestruct (old_txn_get with "Hfactory Htxn") as "#$"; first by lia.
    setoid_rewrite <- Nat.add_succ_comm.
    iApply ("IH" with "[%] [$] Htxns").
    lia.
Qed.
End goose.
