From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import dir.
From Perennial.program_proof Require Import proof_prelude.

From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.program_proof Require Import marshal_proof.

Module inode.
  Record t :=
    mk { addr: u64;
         blocks: list Block; }.
  Global Instance _eta: Settable _ := settable! mk <addr; blocks>.
  Global Instance _witness: Inhabited t := populate!.
  Definition size σ := length σ.(blocks).
End inode.

Section goose.
Context `{!heapG Σ}.
Context `{!lockG Σ}.

Let inodeN := nroot.@"inode".

Implicit Types (σ: inode.t).
Implicit Types (l:loc) (γ:gname) (P: inode.t → iProp Σ).

Definition inode_linv (l:loc) σ : iProp Σ :=
  ∃ (addr_s: Slice.t) (addrs: list u64) (hdr: Block),
    "%Hencoded" ∷ ⌜Block_to_vals hdr = b2val <$> encode ([EncUInt64 (U64 $ length addrs)] ++ (map EncUInt64 addrs))⌝ ∗
    "Hhdr" ∷ int.val σ.(inode.addr) d↦ hdr ∗
    "addr" ∷ l ↦[inode.S :: "addr"] #σ.(inode.addr) ∗
    "addrs" ∷ l ↦[inode.S :: "addrs"] (slice_val addr_s) ∗
    "Haddrs" ∷ is_slice addr_s uint64T 1 addrs ∗
    (* TODO: this does not support reading lock-free; we could make it [∃ q,
    int.val a d↦{q} b], but that wouldn't support lock-free writes if we
    implemented those *)
    "Hdata" ∷ [∗ list] a;b ∈ addrs;σ.(inode.blocks), int.val a d↦ b
.

Definition is_inode l γ P : iProp Σ :=
  ∃ (d:val) (lref: loc), "d" ∷ readonly (l ↦[inode.S :: "d"] d) ∗
                         "m" ∷ readonly (l ↦[inode.S :: "m"] #lref) ∗
                         "Hlock" ∷ is_lock inodeN γ #lref (∃ σ, inode_linv l σ ∗ P σ).

Definition is_inode_durable σ : iProp Σ :=
  ∃ (addrs: list u64) (hdr: Block),
    "%Hencoded" ∷ ⌜Block_to_vals hdr = b2val <$> encode ([EncUInt64 (U64 $ length addrs)] ++ (map EncUInt64 addrs))⌝ ∗
    "Hhdr" ∷ int.val σ.(inode.addr) d↦ hdr ∗
    "Hdata" ∷ [∗ list] a;b ∈ addrs;σ.(inode.blocks), int.val a d↦ b.

Theorem is_inode_crash l σ :
  IntoCrash (inode_linv l σ) (λ _, is_inode_durable σ).
Proof.
  hnf; iIntros "Hinv".
  iNamed "Hinv".
  iExists addrs, hdr.
  iFrame "% ∗".
  auto.
Qed.

End goose.
