Require Export New.golang.theory.
From New.generatedproof Require Import crypto.internal.fips140.subtle.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : subtle.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) unsafe := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) unsafe := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) alias := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) alias := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) subtle := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) subtle := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop subtle get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    subtle.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init subtle }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#".
Admitted.

(* If dst overlaps with x, then this would be a ∧.
   Want to write a precondition that allows dst to overlap x (and also y).
   Either own_slice is "∗", or they start at the same address and it's `∧`?
 *)
Lemma wp_XORBytes dst_sl x_sl y_sl (_old x y : list w8) :
  {{{ "Hdst" ∷ dst_sl ↦* _old ∗
      "Hx" ∷ x_sl ↦* x ∗
      "Hy" ∷ y_sl ↦* y }}}
    @! subtle.XORBytes #dst_sl #x_sl #y_sl
  {{{ (n : w64), RET #n; True }}}.
Proof.
  wp_start. wp_auto.
  change ([go.int; go.int]) with (replicate 2 go.int).
  wp_func_call. wp_call. wp_if_destruct.
  - wp_if_destruct.
    + wp_end.
Abort.

End wps.
