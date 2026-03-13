From New.generatedproof Require Import fmt.
From New.proof Require Import io errors.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : fmt.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) fmt := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) fmt := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop fmt get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    fmt.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init fmt }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ") as "Hown".
  { destruct Hinit as (-> & ?); done. }
  do 5 (wp_apply wp_GlobalAlloc as "?").
  wp_apply (io.wp_initialize' with "Hown") as "[Hown #?]" --no-auto; first naive_solver.
  wp_pures.
  wp_apply (errors.wp_initialize' with "Hown") as "[Hown #?]" --no-auto; first naive_solver.
  (* remaining: ppFree/ssFree sync.Pool literals, space slice literal, errComplex/errBool errors.New *)
  all: admit.
Admitted.

End wps.
