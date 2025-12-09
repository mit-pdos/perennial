From New.golang.theory Require Export proofmode.
From Perennial Require Import base.

Set Default Proof Using "Type".

Section wps.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {core_sem : go.CoreSemantics}.

(* use new goose's to_val for the return value *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ #() -∗ WP Fork e @ s; E {{ Φ }}.
Proof using core_sem.
  iIntros "Hwp HΦ".
  wp_apply (lifting.wp_fork with "[$Hwp]").
  replace (LitV LitUnit) with #().
  { iFrame "HΦ". }
  rewrite go.into_val_unfold //.
Qed.

(* use new goose's to_val for the return value *)
Lemma wp_ArbitraryInt s E Φ :
  ▷ (∀ (x: w64), Φ #x) -∗ WP ArbitraryInt @ s; E {{ Φ }}.
Proof using core_sem.
  iIntros "HΦ".
  wp_apply (lifting.wp_ArbitraryInt).
  iIntros (x) "_".
  replace (LitV x) with #x.
  { iApply "HΦ". }
  rewrite go.into_val_unfold //.
Qed.

End wps.
