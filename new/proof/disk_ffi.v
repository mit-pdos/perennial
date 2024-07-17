From New.proof Require Import proof_prelude.
From Perennial.goose_lang.ffi.disk_ffi Require Import impl specs.
From Perennial.program_proof Require Import disk_lib.

#[global]
Existing Instances disk.disk_op disk.disk_model disk.disk_ty.
#[global]
Existing Instances disk.disk_semantics disk_interp.

Section proof.
Context `{!heapGS Σ}.

Definition own_block (s:slice.t) (q: dfrac) (b:disk.Block) :=
  own_slice s byteT q (disk.Block_to_vals b).

(* NOTE: disk_lib in the old proofs first proved more general specs that showed
this step is atomic, then derived this weaker statement. The more general specs
are needed when the disk points-to is itself in an invariant or crash borrow. *)

Lemma wp_Disk__Read (dv: val) (a: w64) dq (b: disk.Block) :
  {{{ uint.Z a d↦{dq} b }}}
    disk.Read #a
  {{{ (s: slice.t), RET (slice.val s);
      uint.Z a d↦{dq} b ∗
      own_block s (DfracOwn 1) b
  }}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  wp_apply (wp_Read with "[$Hb]").
  iIntros (s) "[Hb Hs]".
  replace (slice.slice_val s) with
    (slice.val (slice.mk s.(slice.Slice.ptr) s.(slice.Slice.sz) s.(slice.Slice.cap))).
  { iApply "HΦ".
    iFrame "Hb".
    admit. (* switching between slice definitions is hard *) }
  rewrite slice.val_unseal.
  destruct s; auto.
Admitted.

Lemma wp_Disk__Write (dv: val) (a: w64) dq (b: disk.Block) s :
  {{{ ∃ b0, uint.Z a d↦ b0 ∗ own_block s dq b }}}
    disk.Write #a (slice.val s)
  {{{ RET #();
      uint.Z a d↦{dq} b ∗ own_block s dq b
  }}}.
Proof.
Admitted.

End proof.
