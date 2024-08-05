From New.proof Require Import proof_prelude.
From Perennial.goose_lang.ffi.disk_ffi Require Import impl specs.

#[global]
Existing Instances disk_op disk_model.
#[global]
Existing Instances disk_semantics disk_interp.

Section proof.
Context `{!heapGS Σ}.

Definition own_block (s : slice.t) (q : dfrac) (b : impl.Block) :=
  own_slice s byteT q (impl.Block_to_vals b).

(* NOTE: disk_lib in the old proofs first proved more general specs that showed
this step is atomic, then derived this weaker statement. The more general specs
are needed when the disk points-to is itself in an invariant or crash borrow. *)

(* XXX: in order to build the Goose semantics example, the disk library is not
   split up into a primitive ffi (impl.v) and typed implementation (typed_impl.v
   for the old version). This breaks the code below, but the strategy of using
   the old typed specs to prove new typed specs may be discarded. *)
(*
Lemma wp_Disk__Read (dv: val) (a: w64) dq (b: impl.Block) :
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
Admitted. *)

End proof.
