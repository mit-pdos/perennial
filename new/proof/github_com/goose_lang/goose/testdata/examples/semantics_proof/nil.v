From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_testCompareSliceToNil :
  test_fun_ok semantics.testCompareSliceToNil.
Proof.
  iIntros (Φ) "HΦ".
  wp_func_call; wp_call.
  wp_auto.
  wp_apply wp_slice_make2 as "%sl [Hs Hcap]".
  { word. }
  iDestruct (own_slice_len with "Hs") as %Hlen.
  rewrite length_replicate in Hlen.
  (* TODO: need a lemma showing allocations are non-nil *)
Abort.

Lemma wp_testComparePointerToNil :
  test_fun_ok semantics.testComparePointerToNil.
Proof.
  semantics_auto.
  (* TODO: need a lemma showing points-tos are non-null *)
Abort.

Lemma wp_testCompareNilToNil :
  test_fun_ok semantics.testCompareNilToNil.
Proof. semantics_auto. Qed.

Lemma wp_testComparePointerWrappedToNil :
  test_fun_ok semantics.testComparePointerWrappedToNil.
Proof.
  semantics_auto.
  (* TODO: array points-to is non null *)
Abort.

Lemma wp_testComparePointerWrappedDefaultToNil :
  test_fun_ok semantics.testComparePointerWrappedDefaultToNil.
Proof.
  semantics_auto.
  (* why bool_decide only here? *)
  rewrite bool_decide_eq_true_2 //.
Qed.

Lemma wp_testInterfaceNilWithType :
  test_fun_ok semantics.testInterfaceNilWithType.
Proof. semantics_auto. Qed.

End wps.
