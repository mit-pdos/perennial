From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_testStructUpdates :
  test_fun_ok semantics.testStructUpdates.
Proof. semantics_auto. Qed.

Lemma wp_testNestedStructUpdates :
  test_fun_ok semantics.testNestedStructUpdates.
Proof. semantics_auto. Qed.

Lemma wp_testStructConstructions :
  test_fun_ok semantics.testStructConstructions.
Proof.
  semantics_auto.
  wp_bind (GoOp GoEquals _ _).
Abort.

Lemma wp_testIncompleteStruct :
  test_fun_ok semantics.testIncompleteStruct.
Proof. semantics_auto. Qed.

Lemma wp_testStoreInStructVar :
  test_fun_ok semantics.testStoreInStructVar.
Proof. semantics_auto. Qed.

Lemma wp_testStoreInStructPointerVar :
  test_fun_ok semantics.testStoreInStructPointerVar.
Proof. semantics_auto. Qed.

Lemma wp_testStoreComposite :
  test_fun_ok semantics.testStoreComposite.
Proof. semantics_auto. Qed.

Lemma wp_testStoreSlice :
  test_fun_ok semantics.testStoreSlice.
Proof. semantics_auto. Qed.

Lemma wp_testStructFieldFunc :
  test_fun_ok semantics.testStructFieldFunc.
Proof. semantics_auto. Qed.

End wps.
