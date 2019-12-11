From iris.proofmode Require Import coq_tactics reduction.
From Perennial.go_lang.examples Require Import append_log.
From Perennial.go_lang Require Import basic_triples.
From Perennial.go_lang Require Import slice encoding.
From Perennial.go_lang Require Import ffi.disk.
From Perennial.go_lang Require Import ffi.disk_prelude.
Import uPred.

Section heap.
Context `{!heapG Σ}.
Context `{!diskG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types stk : stuckness.

Definition is_hdr (sz disk_sz: u64): iProp Σ :=
  ∃ b, 0 d↦ b ∗
       ⌜take 8 (Block_to_vals b) = u64_le_bytes sz⌝ ∗
       ⌜take 8 (drop 8 (Block_to_vals b)) = u64_le_bytes disk_sz⌝.

Definition is_log (v:val) (vs:list Block): iProp Σ :=
  ∃ (sz: u64) (disk_sz: u64),
    ⌜v = (#sz, #disk_sz)%V⌝ ∗
    is_hdr sz disk_sz ∗
    disk_array 1 vs ∗ ⌜length vs = int.nat sz⌝ ∗
    (∃ (free: list Block), disk_array (1 + length vs) free ∗
    ⌜ (1 + length vs + length free)%Z = int.val disk_sz ⌝)
.

End heap.
