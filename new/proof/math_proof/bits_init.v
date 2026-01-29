From New.generatedproof Require Import math.bits.
From New.proof Require Import proof_prelude.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit bits := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf bits := build_get_is_pkg_init_wf.

End proof.
