From New.generatedproof Require Import fmt.
From New.proof Require Import proof_prelude.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} `{!GoContext}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'fmt).
#[global] Program Instance : IsPkgInit fmt :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

End proof.
