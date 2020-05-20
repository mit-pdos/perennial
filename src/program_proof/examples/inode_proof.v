From RecordUpdate Require Import RecordSet.

From Goose.github_com.mit_pdos.perennial_examples Require Import dir.
From Perennial.program_proof Require Import proof_prelude.

From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.program_proof Require Import marshal_proof.

Module inode.
  Record t :=
    mk { blocks: list Block; }.
  Global Instance _eta: Settable _ := settable! mk <blocks>.
  Global Instance _witness: Inhabited t := populate!.
  Definition size σ := length σ.(blocks).
End inode.

Section goose.
Context `{!heapG Σ}.
Context `{!lockG Σ}.

Let inodeN := nroot.@"inode".

Implicit Types (σ: inode.t).

Definition inode_linv (l:loc) σ : iProp Σ :=
  ∃ (addr: u64) (addr_s: Slice.t) (addrs: list u64) (hdr: Block),
    ⌜Block_to_vals hdr = b2val <$> encode ([EncUInt64 (U64 $ length addrs)] ++ (map EncUInt64 addrs))⌝ ∗
    int.val addr d↦ hdr ∗
    l ↦[inode.S :: "addr"] #addr ∗
    l ↦[inode.S :: "addrs"] (slice_val addr_s) ∗
    is_slice addr_s uint64T 1 addrs ∗
    (* TODO: this does not support reading lock-free; we could make it [∃ q,
    int.val a d↦{q} b], but that wouldn't support lock-free writes if we
    implemented those *)
    [∗ list] a;b ∈ addrs;σ.(inode.blocks), int.val a d↦ b
.

End goose.
