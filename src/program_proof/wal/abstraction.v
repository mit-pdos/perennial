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

Definition disk := gmap Z Block.

Module log_state.
  Record t :=
    mk {
        disk: disk;
        updates: list update.t;
        (* positions that are a transaction boundary *)
        trans: gmap u64 bool;
        (* installed_to promises what will be read after a cache miss *)
        installed_to: u64;
        (* durable_to promises what will be on-disk after a crash *)
        durable_to: u64;
      }.
  Global Instance _eta: Settable _ := settable! mk <disk; updates; trans; installed_to; durable_to>.

  Definition last_pos (s: t): u64 := (length s.(updates)).
  
End log_state.

Section heap.
Context `{!heapG Σ}.
Definition update_val (up:u64*Slice.t): val :=
  (#(fst up), (slice_val (snd up), #()))%V.

Theorem update_val_t u : val_ty (update_val u) (struct.t Update.S).
Proof.
  repeat constructor.
  destruct u; rewrite /blockT; val_ty.
Qed.

(* TODO: this should probably also have a fraction *)
Definition is_block (s:Slice.t) (b:Block) :=
  is_slice_small s byteT 1 (Block_to_vals b).

Definition updates_slice (bk_s: Slice.t) (bs: list update.t): iProp Σ :=
  ∃ bks, is_slice_small bk_s (struct.t Update.S) 1 (update_val <$> bks) ∗
   [∗ list] _ ↦ b_upd;upd ∈ bks;bs , let '(update.mk a b) := upd in
                                     is_block (snd b_upd) b ∗
                                     ⌜fst b_upd = a⌝.

Lemma updates_slice_len bk_s bs :
  updates_slice bk_s bs -∗ ⌜int.val bk_s.(Slice.sz) = length bs⌝.
Proof.
  iIntros "Hupds".
  iDestruct "Hupds" as (bks) "[Hbs Hbks]".
  iDestruct (is_slice_small_sz with "Hbs") as %Hbs_sz.
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
