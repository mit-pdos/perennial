From New.proof Require Import proof_prelude errors.
From New.generatedproof Require Import bytes.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : bytes.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) bytes := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) bytes := build_get_is_pkg_init_wf.

Local Lemma wp_asciiSpace_init Φ :
  (∀ v, Φ v) -∗
  WP exception_do ((do: #()) ;;;
    let: "$r0" := (let: "$k0" := #(W64 9) in
    let: "$v1" := #(W8 1) in
    let: "$k2" := #(W64 10) in
    let: "$v3" := #(W8 1) in
    let: "$k4" := #(W64 11) in
    let: "$v5" := #(W8 1) in
    let: "$k6" := #(W64 12) in
    let: "$v7" := #(W8 1) in
    let: "$k8" := #(W64 13) in
    let: "$v9" := #(W8 1) in
    let: "$k10" := #(W64 32) in
    let: "$v11" := #(W8 1) in
    CompositeLiteral (go.ArrayType 256 go.uint8) (LiteralValue [KeyedElement (Some (KeyExpression go.int "$k0")) (ElementExpression go.uint8 "$v1"); KeyedElement (Some (KeyExpression go.int "$k2")) (ElementExpression go.uint8 "$v3"); KeyedElement (Some (KeyExpression go.int "$k4")) (ElementExpression go.uint8 "$v5"); KeyedElement (Some (KeyExpression go.int "$k6")) (ElementExpression go.uint8 "$v7"); KeyedElement (Some (KeyExpression go.int "$k8")) (ElementExpression go.uint8 "$v9"); KeyedElement (Some (KeyExpression go.int "$k10")) (ElementExpression go.uint8 "$v11")])) in
    do:  ((GlobalVarAddr bytes.asciiSpace #()) <-[go.ArrayType 256 go.uint8] "$r0"))
  {{ Φ }}.
Proof. Admitted.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop bytes get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    bytes.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init bytes }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ") as "Hown".
  { destruct Hinit as (-> & ?); done. }
  wp_apply wp_GlobalAlloc as "?".
  wp_apply wp_GlobalAlloc as "?".
  wp_apply wp_GlobalAlloc as "?".
  wp_apply wp_GlobalAlloc as "?".
  wp_apply (errors.wp_initialize' with "Hown") as "[Hown #?]" --no-auto; first naive_solver.
  wp_pures.
  wp_apply wp_New as "% _".
  wp_pures.
  wp_apply wp_New as "% _".
  wp_pures.
  wp_apply wp_New as "% _" --no-auto.
  wp_pures. wp_store.
  (* asciiSpace array literal - CompositeLiteral semantics can't handle KeyExpression *)
  iApply wp_asciiSpace_init. iIntros.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

Lemma wp_Clone sl_b dq (b : list w8) :
  {{{
    is_pkg_init bytes ∗
    "Hsl_b" ∷ sl_b ↦*{dq} b
  }}}
  @! bytes.Clone #sl_b
  {{{
    sl_b', RET #sl_b';
    "Hsl_b" ∷ sl_b ↦*{dq} b ∗
    "Hsl_b'" ∷ sl_b' ↦* b ∗
    "Hsl_b'_cap" ∷ own_slice_cap w8 sl_b' (DfracOwn 1)
  }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  wp_if_destruct.
  { iApply "HΦ".
    iDestruct (own_slice_len with "Hsl_b") as %[Hb_len ?].
    apply nil_length_inv in Hb_len. subst.
    iFrame "∗#".
    iDestruct own_slice_nil as "$".
    iDestruct own_slice_cap_nil as "$".
  }
  wp_apply wp_slice_literal as "% _".
  { iIntros. wp_auto. iFrame. }
  wp_apply (wp_slice_append with "[$Hsl_b]") as "* (?&?&?)".
  { iDestruct own_slice_empty as "$"; try done.
    iDestruct own_slice_cap_empty as "$"; try done. }
  wp_end.
Qed.

Lemma wp_Equal sl_b0 sl_b1 d0 d1 (b0 b1 : list w8) :
  {{{
    is_pkg_init bytes ∗
    "Hb0" ∷ sl_b0 ↦*{d0} b0 ∗
    "Hb1" ∷ sl_b1 ↦*{d1} b1
  }}}
  @! bytes.Equal #sl_b0 #sl_b1
  {{{
    RET #(bool_decide (b0 = b1));
    sl_b0 ↦*{d0} b0 ∗
    sl_b1 ↦*{d1} b1
  }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  wp_apply (wp_bytes_to_string with "Hb0") as "Hb0".
  wp_apply (wp_bytes_to_string with "Hb1") as "Hb1".
  iApply "HΦ". iFrame.
Qed.

End wps.
