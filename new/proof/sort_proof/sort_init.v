From New.generatedproof Require Import sort.
From New.proof Require Import proof_prelude.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit sort := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf sort := build_get_is_pkg_init_wf.

End proof.
