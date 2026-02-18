From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "W".

Lemma wp_testParamsInterface :
  test_fun_ok semantics.testParamsInterface.
Proof. semantics_auto.  Qed.

Lemma wp_testEmptyInterface :
  test_fun_ok semantics.testEmptyInterface.
Proof. semantics_auto. Qed.

Lemma wp_testTypeAssertionInterface :
  test_fun_ok semantics.testTypeAssertionInterface.
Proof. semantics_auto. Qed.

End wps.
