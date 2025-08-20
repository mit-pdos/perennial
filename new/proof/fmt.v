From New.generatedproof Require Import fmt.
From New.proof Require Import proof_prelude.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit fmt := define_is_pkg_init True%I.

End proof.
