From New.proof Require Import proof_prelude.
From New.proof Require Export std.
From New.generatedproof Require Export strings.
From Perennial Require Import base.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf strings := build_get_is_pkg_init_wf.

End proof.
