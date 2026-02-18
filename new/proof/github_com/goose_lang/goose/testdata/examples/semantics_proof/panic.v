From New.proof.github_com.goose_lang.goose.testdata.examples.semantics_proof
       Require Import semantics_init.

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : semantics.Assumptions}.
Local Set Default Proof Using "All".

(* this doesn't formally mean anything but if panic is opaque it tells you the code
has a panic *)
Lemma wp_shouldPanic :
  ∀ (Φ: goose_lang.val → iProp Σ),
  (∀ Ψ (v: goose_lang.val), WP @! go.panic v {{ Ψ }}) -∗
  WP @! semantics.shouldPanic #() {{ Φ }}.
Proof.
  iIntros (Φ) "Hpanic".
  wp_func_call. wp_call.
  wp_apply "Hpanic".
Qed.

End wps.
