From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_testU64ToU32 :
  test_fun_ok semantics.testU64ToU32.
Proof. semantics_auto. Qed.

Lemma wp_testU32ToU64 :
  test_fun_ok semantics.testU32ToU64.
Proof. semantics_auto. Qed.

Lemma wp_testU32Len :
  test_fun_ok semantics.testU32Len.
Proof. semantics_auto. Qed.

Lemma wp_testU32NewtypeLen :
  test_fun_ok semantics.testU32NewtypeLen.
Proof. semantics_auto. Qed.

Lemma wp_testUint32Untyped :
  test_fun_ok semantics.testUint32Untyped.
Proof. semantics_auto. Qed.

End wps.
