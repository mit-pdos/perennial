Require Export New.generatedproof.errors.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : errors.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) errors := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) errors := build_get_is_pkg_init_wf.

Lemma wp_Unwrap (err : error.t) :
  {{{ True }}}
    @! errors.Unwrap #err
  {{{ RET #err; True }}}.
Proof.
  wp_start. wp_auto. destruct err.
  2:{ wp_auto. wp_end. }
  (* TODO: cases for err being not nil. *)
Admitted.

End wps.
