Require Import New.generatedproof.github_com.mit_pdos.go_journal.common.
Require Import New.proof.proof_prelude.
Require Import New.proof.github_com.goose_lang.primitive.disk.

Section proof.
Context `{!heapGS Σ} `{!globalsGS Σ}.

#[global]
Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'common).
#[global] Program Instance : IsPkgInit common :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

End proof.
