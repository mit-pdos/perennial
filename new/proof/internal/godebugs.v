From New.generatedproof Require Import internal.godebugs.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : godebugs.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) godebugs := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) godebugs := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop godebugs get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    godebugs.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init godebugs }}}.
Proof using W.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ") as "Hown".
  { destruct Hinit as (-> & ?); done. }
  wp_apply wp_GlobalAlloc as "?".
  wp_apply wp_GlobalAlloc as "?".
  (* FIXME: The above used aobut 24% of RAM on my 32GB laptop. *)
Qed.

End wps.
