Require Import New.code.github_com.mit_pdos.go_journal.common.
Require Import New.generatedproof.github_com.mit_pdos.go_journal.common.
Require Import New.proof.proof_prelude.
Require Import New.proof.github_com.goose_lang.primitive.disk.

Section proof.
Context `{!heapGS Σ} `{!goGlobalsGS Σ}.

#[global]
Program Instance : IsPkgInit common := ltac2:(build_pkg_init ()).

End proof.
