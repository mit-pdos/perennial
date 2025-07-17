From New.proof Require Import proof_prelude.
From New.generatedproof Require Import bytes.

Module bytes.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.

#[global]
Program Instance is_pkg_init_bytes : IsPkgInit bytes := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_bytes.
#[local] Transparent is_pkg_init_bytes.

Lemma wp_Clone sl_b dq (b : list w8) :
  {{{
    is_pkg_init bytes ∗
    "Hsl_b" ∷ sl_b ↦*{dq} b
  }}}
  bytes @ "Clone" #sl_b
  {{{
    sl_b', RET #sl_b';
    "Hsl_b" ∷ sl_b ↦*{dq} b ∗
    "Hsl_b'" ∷ sl_b' ↦* b ∗
    "Hsl_b'_cap" ∷ own_slice_cap w8 sl_b'
  }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  iDestruct (own_slice_nil (DfracOwn 1)) as "?".
  iDestruct own_slice_cap_nil as "?".
  wp_if_destruct.
  { iApply "HΦ".
    iDestruct (own_slice_len with "Hsl_b") as %Hb_len.
    apply nil_length_inv in Hb_len. subst.
    iFrame "∗#". }
  wp_auto.
  wp_apply (wp_slice_append with "[$Hsl_b]") as "* (?&?&?)".
  { iFrame "#". }
  iApply "HΦ". iFrame.
Qed.

End proof.
End bytes.
