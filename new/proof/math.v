From New.generatedproof Require Import math.
From New.proof Require Import proof_prelude.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx : GoContext}.

Local Notation deps := (ltac2:(build_pkg_init_deps 'math) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit math :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

End proof.
