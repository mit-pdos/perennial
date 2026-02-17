From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_testStructUpdates :
  test_fun_ok semantics.testStructUpdates.
Proof.
  semantics_auto.
  wp_alloc x1 as "H"; wp_auto.
  repeat (wp_call_auto || wp_auto).
  wp_end.
Qed.


End wps.
