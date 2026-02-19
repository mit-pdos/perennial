From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_testPrimitiveTypesEqual :
  test_fun_ok semantics.testPrimitiveTypesEqual.
Proof. semantics_auto. Qed.

Lemma wp_testDefinedStrTypesEqual :
  test_fun_ok semantics.testDefinedStrTypesEqual.
Proof. semantics_auto. Qed.

Lemma wp_testListTypesEqual :
  test_fun_ok semantics.testListTypesEqual.
Proof. semantics_auto. Qed.


End wps.
