From New.generatedproof Require Import sort.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : sort.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) sort := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) sort := build_get_is_pkg_init_wf.
End proof.
