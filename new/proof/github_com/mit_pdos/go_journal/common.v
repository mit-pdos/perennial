Require Import New.generatedproof.github_com.mit_pdos.go_journal.common.
Require Import New.proof.proof_prelude.
Require Import New.proof.github_com.goose_lang.primitive.disk.

Section proof.
Context `{!heapGS Σ} `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit common := define_is_pkg_init True%I.

End proof.
