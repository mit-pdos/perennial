From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang Require Import crash_borrow.

Section proof.

Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

(* TODO: try making the final crash_borrow maintain (P -∗ Qc) by
   construction? *)
Lemma wpc_transformer {E} e P Q Qc :
  goose_lang.(language.to_val) e = None →
  {{{ P }}}
      e @ E
  {{{ r, RET r; Q r }}}
  {{{ Qc }}}
  -∗
  ∀ R R' Qc',
  {{{
        "Hcrash" ∷ crash_borrow R (|={E}=> Qc') ∗
        "Hacc" ∷ (R ={E}=∗ P ∗ (∀ r, Q r ={E}=∗ R')) ∗
        "HcrashWand" ∷ (Qc ={E}=∗ Qc') ∗
        "HcrashOk" ∷ □(R' ={E}=∗ Qc')
  }}}
      e @ E
  {{{
      r, RET r; crash_borrow R' (|={E}=> Qc')
  }}}.
Proof.
  intros.
  iIntros "#Hwpc*!#*". iNamed 1. iIntros "HΦ".
  wp_apply (wpc_wp _ _ _ _ True).
  wpc_apply (wpc_crash_borrow_open_modify with "Hcrash").
  { done. }
  iSplit; first done.
  iIntros "HR".
  iApply wpc_fupd.
  iMod ("Hacc" with "HR") as "[HP Hclose]".
  wpc_apply ("Hwpc" with "HP").
  iSplit.
  { iIntros "Hc". iSplitR; first done. by iMod ("HcrashWand" with "Hc") as "$". }
  iNext.
  iIntros "* HQ".
  iExists R'. iMod ("Hclose" with "HQ") as "HR".
  iModIntro. iFrame. iIntros "Hcrash".
  iSplit; first done. iApply "HΦ".
  iFrame.
Qed.

End proof.
