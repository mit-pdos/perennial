From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.

Definition LogSz := 511.

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Implicit Types (v:val).
Implicit Types (stk:stuckness) (E:coPset).

Implicit Types (upds: list update.t).

Definition circ_data upds: iProp Σ :=
  ⌜Z.of_nat (length upds) <= LogSz⌝ ∗
  ∃ hdr1 hdr2, 0 d↦ hdr1 ∗ 1 d↦ hdr2 ∗ 2 d↦∗ (update.b <$> upds).

(* TODO: write this abstraction relation *)
Definition is_circular (l:loc) (upds: list update.t): iProp Σ :=
  (∃ v, l ↦[struct.t circular.S] v) ∗ circ_data upds.

Theorem is_circular_data_extract l upds :
  is_circular l upds -∗ circ_data upds ∗ (circ_data upds -∗ is_circular l upds).
Proof.
  iIntros "[Hmem Hdata]".
  iFrame.
  iIntros "$".
Qed.

Theorem new_circular bs :
  0 d↦∗ bs ∗ ⌜length bs = Z.to_nat (2+LogSz)⌝ -∗ ∃ upds, circ_data upds.
Proof.
Admitted.

Theorem wp_recoverCircular upds :
  {{{ circ_data upds }}}
    recoverCircular #()
  {{{ l, RET #l; is_circular l upds }}}.
Proof.
Admitted.

Definition space_remaining upds: Z := LogSz - Z.of_nat (length upds).

Theorem wp_circular__SpaceRemaining l upds :
  {{{ is_circular l upds }}}
    circular__SpaceRemaining #l
  {{{ (x:u64), RET #x; ⌜int.val x = space_remaining upds⌝ ∗ is_circular l upds }}}.
Proof.
Admitted.

Theorem wpc_circular__SpaceRemaining stk k E1 E2 l upds :
  {{{ is_circular l upds }}}
    circular__SpaceRemaining #l
    @ stk; k; E1; E2
  {{{ (x:u64), RET #x; ⌜int.val x = space_remaining upds⌝ ∗ is_circular l upds }}}
  {{{ is_circular l upds }}}.
Proof.
Admitted.

Theorem wpc_circular__appendFreeSpace stk k E1 E2 l upds bufs upds' :
  0 < space_remaining upds ->
  {{{ is_circular l upds ∗ updates_slice bufs upds' }}}
    circular__appendFreeSpace #l (slice_val bufs)
    @ stk; k; E1; E2
                    (* TODO: need to break is_circular apart into the part
                    consumed by the header and the free space; the free space
                    gets modified here but not the in-memory state or existing
                    updates *)
  {{{ RET #(); is_circular l upds }}}
  {{{ circ_data upds }}}.
Proof.
Admitted.

Theorem wpc_circular__Append stk k E1 E2 l upds bufs upds' :
  0 < space_remaining upds ->
  {{{ is_circular l upds ∗ updates_slice bufs upds' }}}
    circular__Append #l (slice_val bufs)
    @ stk; k; E1; E2
  {{{ RET #(); is_circular l (upds ++ upds') }}}
  {{{ is_circular l upds ∨ is_circular l (upds ++ upds') }}}.
Proof.
Admitted.

Theorem wpc_circular__Empty stk k E1 E2 l upds :
  {{{ is_circular l upds }}}
    circular__Empty #()
    @ stk; k; E1; E2
  {{{ RET #(); is_circular l [] }}}
  {{{ circ_data upds ∨ circ_data [] }}}.
Proof.
Admitted.

End heap.
