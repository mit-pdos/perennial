From New.proof Require Import proof_prelude.
From New.proof Require Export std.
From New.generatedproof Require Export strings.
From Perennial Require Import base.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : strings.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) strings := build_get_is_pkg_init_wf.
End wps.
