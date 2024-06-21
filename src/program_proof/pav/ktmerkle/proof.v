From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof Require Import std_proof.

Section defs.
Context `{!heapGS Σ}.

Lemma wp_testAgreement (servAddr adtrAddr : u64) :
  {{{ True }}}
  testAgreement #servAddr #adtrAddr
  {{{ RET #(); True }}}.
Proof.
  rewrite /testAgreement.

End defs.
