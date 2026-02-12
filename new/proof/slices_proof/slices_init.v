From New.generatedproof Require Import slices.
From New.proof Require Import proof_prelude.
From New.proof.math_proof Require Import bits_init.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit slices := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf slices := build_get_is_pkg_init_wf.

End proof.
