Require Import New.proof.github_com.goose_lang.std.
Require Import New.proof.proof_prelude.
Require Import New.generatedproof.github_com.tchajed.marshal.

Section heap.
Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!goGlobalsGS Σ}.

#[global]
Program Instance : IsPkgInit marshal := ltac2:(build_pkg_init ()).

End heap.
