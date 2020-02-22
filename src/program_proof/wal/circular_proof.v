From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.Helpers Require Import GenHeap.

Definition LogSz := 511.

Module lowΣ.
  Record t :=
    mk { upds: list update.t;
         startpos: u64;
         endpos: u64;
       }.
  Global Instance _eta: Settable _ := settable! mk <upds; startpos; endpos>.
End lowΣ.

Module circΣ.
  Record t :=
    mk { upds: list update.t;
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
Context `{!inG Σ (authR mnatUR)}.
Implicit Types (v:val).
Implicit Types (stk:stuckness) (E:coPset).

Definition low_data (σ : lowΣ.t) : iProp Σ :=
  ⌜Z.of_nat (length σ.(lowΣ.upds)) = LogSz⌝ ∗
  ∃ hdr1 hdr2 (hdr2extra : list encodable),
    0 d↦ hdr1 ∗
    1 d↦ hdr2 ∗
    ⌜Block_to_vals hdr1 = b2val <$> encode ([EncUInt64 σ.(lowΣ.endpos)] ++ (map EncUInt64 (map update.addr (σ.(lowΣ.upds)))))⌝ ∗
    ⌜Block_to_vals hdr2 = b2val <$> encode ([EncUInt64 σ.(lowΣ.startpos)] ++ hdr2extra)⌝ ∗
    2 d↦∗ (update.b <$> σ.(lowΣ.upds)).

Definition circ_data (σ : circΣ.t) : iProp Σ :=
  ∃ lσ,
    low_data lσ ∗
    ⌜σ.(circΣ.start) = lσ.(lowΣ.startpos)⌝ ∗
    ⌜lσ.(lowΣ.endpos) = word.add lσ.(lowΣ.startpos) (length σ.(circΣ.upds))⌝ ∗
    [∗ list] i ↦ bupd ∈ σ.(circΣ.upds),
      ⌜lσ.(lowΣ.upds) !! Z.to_nat ((int.val σ.(circΣ.start) + i) `mod` LogSz)%Z = Some bupd⌝.

Definition circ_inner (γh : gen_heapG u64 update.t Σ) (γstart γend : gname) : iProp Σ :=
  ∃ mh σ,
    gen_heap_ctx (hG := γh) mh ∗
    circ_data σ ∗
    own γstart (● (Z.to_nat (int.val σ.(circΣ.start)) : mnat)) ∗
    own γend (● (plus (Z.to_nat (int.val σ.(circΣ.start))) (length σ.(circΣ.upds)) : mnat)) ∗
    ⌜ ∀ (i : nat),
      mh !! (word.add σ.(circΣ.start) i) = σ.(circΣ.upds) !! i ⌝.

Definition circN : namespace := nroot .@ "circ".

Definition is_circ (γh : gen_heapG u64 update.t Σ) (γstart γend : gname) : iProp Σ :=
  inv circN (circ_inner γh γstart γend).


(*
Definition is_circularAppender (l:loc) σ : iProp Σ :=
  circ_data σ ∗
  ∃ (diskAddrs : Slice.t),
  l ↦[struct.t circularAppender.S] diskAddrs ∗
  is_slice diskAddrs u64 (map update.addr σ.(circΣ.upds)).
*)

(*
Theorem new_circular bs :
  0 d↦∗ bs ∗ ⌜length bs = Z.to_nat (2+LogSz)⌝ -∗ ∃ σ, circ_data σ.
Proof.
Admitted.

(* XXX recoverCircular actually returns two things *)
Theorem wp_recoverCircular σ :
  {{{ circ_data σ }}}
    recoverCircular #()
  {{{ l, RET #l; is_circular l σ }}}.
Proof.
Admitted.

Definition space_remaining σ: Z := LogSz - Z.of_nat (length σ.(upds)).

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
*)

End heap.
