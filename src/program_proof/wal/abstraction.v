From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.program_proof Require Import proof_prelude.

Module update.
  Record t :=
    mk { addr: u64;
         b: Block; }.
  Global Instance _eta: Settable _ := settable! mk <addr; b>.
End update.

Definition LogSz: Z := 511.

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

  Definition updates σ : list update.t := txn_upds σ.(txns).

End log_state.

Definition addrs_wf (updates: list update.t) (d: disk) :=
  forall i u, updates !! i = Some u ->
              2 + LogSz ≤ int.val u.(update.addr) ∧
              ∃ (b: Block), d !! (int.val u.(update.addr)) = Some b.

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


Section heap.
Context `{!heapG Σ}.
Definition update_val (up:u64*Slice.t): val :=
  (#(fst up), (slice_val (snd up), #()))%V.

Theorem update_val_t u : val_ty (update_val u) (struct.t Update.S).
Proof.
  repeat constructor.
  destruct u; rewrite /blockT; val_ty.
Qed.

Definition updates_slice (bk_s: Slice.t) (bs: list update.t): iProp Σ :=
  ∃ bks, is_slice bk_s (struct.t Update.S) 1 (update_val <$> bks) ∗
   [∗ list] _ ↦ b_upd;upd ∈ bks;bs , let '(update.mk a b) := upd in
                                     is_block (snd b_upd) b ∗
                                     ⌜fst b_upd = a⌝.

Lemma updates_slice_len bk_s bs :
  updates_slice bk_s bs -∗ ⌜int.val bk_s.(Slice.sz) = length bs⌝.
Proof.
  iIntros "Hupds".
  iDestruct "Hupds" as (bks) "[Hbs Hbks]".
  iDestruct (is_slice_sz with "Hbs") as %Hbs_sz.
  iDestruct (big_sepL2_length with "Hbks") as %Hbks_len.
  rewrite fmap_length in Hbs_sz.
  iPureIntro.
  rewrite -Hbks_len.
  rewrite Hbs_sz.
  destruct bk_s; simpl.
  word.
Qed.

End heap.

Hint Resolve update_val_t : val_ty.
