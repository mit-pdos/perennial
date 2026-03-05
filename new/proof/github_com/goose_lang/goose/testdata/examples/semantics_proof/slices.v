From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_testSliceRef :
  test_fun_ok semantics.testSliceRef.
Proof.
  semantics_auto.
  (* TODO: `steps` should apply wp_slice_make2 instead of unfolding it? *)
  rewrite /slice_index_ref /=.
  iDestruct (array_acc _ 0 with "p") as "[? p]"; try done.
  wp_auto. wp_end.
Qed.

End wps.
