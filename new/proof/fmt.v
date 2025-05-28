From New.generatedproof Require Import fmt.
From New.proof Require Import proof_prelude.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!goGlobalsGS Σ}.

#[global] Program Instance : IsPkgInit fmt := ltac2:(build_pkg_init ()).

End proof.
