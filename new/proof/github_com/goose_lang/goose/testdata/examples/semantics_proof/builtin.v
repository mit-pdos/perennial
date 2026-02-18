From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_testMinUint64 :
  test_fun_ok semantics.testMinUint64.
Proof.
  semantics_auto.
  (* TODO: min *)
Abort.

Lemma wp_testMaxUint64 :
  test_fun_ok semantics.testMaxUint64.
Proof.
  semantics_auto.
  (* TODO: max *)
Abort.


End wps.
