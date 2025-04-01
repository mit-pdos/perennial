From New Require Export notation.
From New.golang.theory Require Export typing proofmode.
From Perennial Require Import base.

Set Default Proof Using "Type".

Section wps.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

(* use new goose's to_val for the return value *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ #() -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "Hwp HΦ".
  wp_apply (lifting.wp_fork with "[$Hwp]").
  replace (LitV LitUnit) with #().
  { iFrame "HΦ". }
  rewrite to_val_unseal //.
Qed.

(* use new goose's to_val for the return value *)
Lemma wp_ArbitraryInt s E Φ :
  ▷ (∀ (x: w64), Φ #x) -∗ WP ArbitraryInt @ s; E {{ Φ }}.
Proof.
  iIntros "HΦ".
  wp_apply (lifting.wp_ArbitraryInt).
  iIntros (x) "_".
  replace (LitV x) with #x.
  { iApply "HΦ". }
  rewrite to_val_unseal //.
Qed.

End wps.
