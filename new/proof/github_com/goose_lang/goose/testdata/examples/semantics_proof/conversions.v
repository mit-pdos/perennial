From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_testByteSliceToString :
  test_fun_ok semantics.testByteSliceToString.
Proof.
  iIntros (Φ) "HΦ".
  wp_func_call; wp_call.
  wp_auto.
  wp_apply wp_slice_make2; [ word | ].
  iIntros (sl) "[Hs Hcap]".
  wp_auto.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  rewrite length_replicate in Hlen.
  steps.
  wp_apply (wp_store_slice_index with "[$Hs]") as "Hs".
  { len. }
  steps.
  wp_apply (wp_store_slice_index with "[$Hs]") as "Hs".
  { len. }
  steps.
  wp_apply (wp_store_slice_index with "[$Hs]") as "Hs".
  { len. }
  steps.
  (* missing semantics? *)
Abort.


End wps.
