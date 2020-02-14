From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.

Definition LogSz := 511.

Module circΣ.
  Record t :=
    mk { upds: list update.t;
         (* disk start - logical position of first update in upds *)
         start: u64;
       }.
  Global Instance _eta: Settable _ := settable! mk <upds; start>.
  Definition diskEnd (s:t): Z :=
    int.val s.(start) + Z.of_nat (length s.(upds)).
  Definition empty (s:t): t :=
    mk [] (diskEnd s).
End circΣ.

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Implicit Types (v:val).
Implicit Types (stk:stuckness) (E:coPset).

Implicit Types (σ: circΣ.t).
Notation upds := circΣ.upds.
Notation diskStart := circΣ.start.

Definition circ_data σ: iProp Σ :=
  ⌜Z.of_nat (length σ.(upds)) <= LogSz⌝ ∗
  ∃ hdr1 hdr2, 0 d↦ hdr1 ∗ 1 d↦ hdr2 ∗ 2 d↦∗ (update.b <$> σ.(upds)).

(* TODO: write this abstraction relation *)
Definition is_circular (l:loc) σ: iProp Σ :=
  (∃ v, l ↦[struct.t circular.S] v) ∗ circ_data σ.

Theorem new_circular bs :
  0 d↦∗ bs ∗ ⌜length bs = Z.to_nat (2+LogSz)⌝ -∗ ∃ σ, circ_data σ.
Proof.
Admitted.

Theorem wp_recoverCircular σ :
  {{{ circ_data σ }}}
    recoverCircular #()
  {{{ l, RET #l; is_circular l σ }}}.
Proof.
Admitted.

Definition space_remaining σ: Z := LogSz - Z.of_nat (length σ.(upds)).

Theorem wp_circular__SpaceRemaining l σ :
  {{{ is_circular l σ }}}
    circular__SpaceRemaining #l
  {{{ (x:u64), RET #x; ⌜int.val x = space_remaining σ⌝ ∗ is_circular l σ }}}.
Proof.
Admitted.

Theorem wpc_circular__SpaceRemaining stk k E1 E2 l σ :
  {{{ is_circular l σ }}}
    circular__SpaceRemaining #l
    @ stk; k; E1; E2
  {{{ (x:u64), RET #x; ⌜int.val x = space_remaining σ⌝ ∗ is_circular l σ }}}
  {{{ is_circular l σ }}}.
Proof.
Admitted.

Theorem wpc_circular__appendFreeSpace stk k E1 E2 l σ bufs σ' :
  0 < space_remaining σ ->
  {{{ is_circular l σ ∗ updates_slice bufs σ'.(upds) }}}
    circular__appendFreeSpace #l (slice_val bufs)
    @ stk; k; E1; E2
                    (* TODO: need to break is_circular apart into the part
                    consumed by the header and the free space; the free space
                    gets modified here but not the in-memory state or existing
                    updates *)
  {{{ RET #(); is_circular l σ }}}
  {{{ circ_data σ }}}.
Proof.
Admitted.

Theorem wpc_circular__Append stk k E1 E2 l σ bufs upds' :
  0 < space_remaining σ ->
  {{{ is_circular l σ ∗ updates_slice bufs upds' }}}
    circular__Append #l (slice_val bufs)
    @ stk; k; E1; E2
  {{{ RET #(); is_circular l (set circΣ.upds (.++ upds') σ) }}}
  {{{ is_circular l σ ∨ is_circular l (set circΣ.upds (.++ upds') σ) }}}.
Proof.
Admitted.

Theorem wpc_circular__Empty stk k E1 E2 l σ :
  {{{ is_circular l σ }}}
    circular__Empty #()
    @ stk; k; E1; E2
  {{{ RET #(); is_circular l (circΣ.empty σ) }}}
  {{{ circ_data σ ∨ circ_data (circΣ.empty σ) }}}.
Proof.
Admitted.

End heap.
