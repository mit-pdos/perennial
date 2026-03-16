From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_testNilDefault :
  test_fun_ok semantics.testNilDefault.
Proof.
  semantics_auto.
Qed.

Lemma wp_testNilVal :
  test_fun_ok semantics.testNilVal.
Proof.
  semantics_auto.
Qed.

End wps.
