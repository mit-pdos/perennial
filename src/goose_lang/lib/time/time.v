From Perennial.goose_lang Require Import proofmode.
From Perennial.goose_lang.lib Require Export time.impl.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Theorem wp_Sleep (duration : u64) :
  {{{ True }}}
    time.Sleep #duration
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec. wp_pures.
  by iApply "HΦ".
Qed.

Theorem wp_TimeNow :
  {{{ True }}}
    time.TimeNow #()
  {{{ (t : u64), RET #t; True }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec. wp_pures.
  by iApply "HΦ".
Qed.

End goose_lang.
