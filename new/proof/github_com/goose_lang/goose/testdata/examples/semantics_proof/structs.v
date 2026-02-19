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
  iSelect (x ↦ _)%I (fun H => iRename H into "x").
  destruct (decide (p4_ptr = x)).
  {
    subst.
    admit. (* TODO: how to combine typed_pointsto to get sum of fractions? *)
  }
  rewrite bool_decide_eq_false_2 //.
Admitted.

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
