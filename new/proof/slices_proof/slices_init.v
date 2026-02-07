From New.generatedproof Require Import slices.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : slices.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) slices := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) slices := build_get_is_pkg_init_wf.
End proof.
