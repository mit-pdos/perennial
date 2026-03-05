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
  (* TODO: finish this proof *)
Abort.

End wps.
