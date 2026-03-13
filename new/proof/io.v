From New.generatedproof Require Import io.
From New.proof Require Import sync errors.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : io.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) io := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) io := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop io get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    io.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init io }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ") as "Hown".
  { destruct Hinit as (-> & ?); done. }
  do 11 (wp_apply wp_GlobalAlloc as "?").
  wp_apply (sync.wp_initialize' with "Hown") as "[Hown #?]" --no-auto; first naive_solver.
  wp_pures.
  wp_apply (errors.wp_initialize' with "Hown") as "[Hown #?]" --no-auto; first naive_solver.
  wp_pures.
  do 7 (wp_apply wp_New as "% _"; wp_pures).
  wp_apply wp_New as "% _" --no-auto.
  wp_pures. wp_store.
  (* remaining: Discard struct literal, blackHolePool sync.Pool literal, ErrClosedPipe errors.New *)
  all: admit.
Admitted.

End wps.
