From Perennial.goose_lang Require Import notation typing exception proofmode.
From Perennial.goose_lang.new Require Export exception.

Set Default Proof Using "Type".

Section wps.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Lemma wp_do_execute_binded (v : val) (Φ : val → iProp Σ) :
  Φ v -∗
  WP (do: v) {{ v, (WP (exception_do (Val v)) {{ Φ }}) }}.
Proof.
  iIntros "HΦ".
  rewrite do_execute_unseal exception_do_unseal.
  wp_lam. wp_pures. wp_lam. wp_pures. by iFrame.
Qed.
End wps.
