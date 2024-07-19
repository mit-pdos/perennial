From Perennial.goose_lang Require Import proofmode.
From Perennial.goose_lang.lib Require Export rand.impl.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Theorem wp_RandomUint64 s E :
  {{{ True }}}
    rand.RandomUint64 #() @ s; E
  {{{ (r: u64), RET #r; True }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_rec. wp_pures.
  wp_apply wp_ArbitraryInt.
  done.
Qed.

End goose_lang.
