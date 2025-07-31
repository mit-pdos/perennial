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
    "Hsl_b'_cap" ∷ own_slice_cap w8 sl_b' (DfracOwn 1)
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

Lemma wp_Equal sl_b0 sl_b1 d0 d1 (b0 b1 : list w8) :
  {{{
    is_pkg_init bytes ∗
    "Hsl_b0" ∷ sl_b0 ↦*{d0} b0 ∗
    "Hsl_b1" ∷ sl_b1 ↦*{d1} b1
  }}}
  bytes @ "Equal" #sl_b0 #sl_b1
  {{{
    RET #(bool_decide (b0 = b1));
    "Hsl_b0" ∷ sl_b0 ↦*{d0} b0 ∗
    "Hsl_b1" ∷ sl_b1 ↦*{d1} b1
  }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  wp_apply (wp_StringFromBytes with "Hsl_b0") as "Hsl_b0".
  wp_apply (wp_StringFromBytes with "Hsl_b1") as "Hsl_b1".
  iApply "HΦ". iFrame.
Qed.

End proof.
End bytes.
