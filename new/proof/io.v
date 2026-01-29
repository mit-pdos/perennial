From New.generatedproof Require Import io.
From New.proof Require Import sync errors.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : io.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) io := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) io := build_get_is_pkg_init_wf.

End wps.
