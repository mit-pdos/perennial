From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_testOrCompare :
  test_fun_ok semantics.testOrCompare.
Proof. semantics_auto. Qed.
Lemma wp_testAndCompare :
  test_fun_ok semantics.testAndCompare.
Proof. semantics_auto. Qed.
Lemma wp_testShiftMod :
  test_fun_ok semantics.testShiftMod.
Proof. semantics_auto. Qed.

End wps.
