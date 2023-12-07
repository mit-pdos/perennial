From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang Require Import crash_borrow.

Section proof.

Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

(* TODO: try making the final crash_borrow maintain (P -∗ Qc) by
   construction? *)
Lemma wpc_transformer e P Q Qc :
  goose_lang.(language.to_val) e = None →
  □ (P ={⊤}=∗ Qc) -∗
  □ (∀ r, Q r ={⊤}=∗ Qc) -∗
  ({{{ P }}}
      e @ ⊤
  {{{ r, RET r; Q r }}}
  {{{ Qc }}})
  ∗-∗
  (∀ R R' Qc',
  {{{
        "Hcrash" ∷ crash_borrow R (|={⊤}=> Qc') ∗
        "Hacc" ∷ (R ={⊤}=∗ P ∗ (Qc ={⊤}=∗ Qc') ∧ (∀ r, Q r ={⊤}=∗ R' r)) ∗
        "#HcrashOk" ∷ □(∀ r, R' r ={⊤}=∗ Qc')
  }}}
      e @ ⊤
  {{{
      r, RET r; crash_borrow (R' r) (|={⊤}=> Qc')
  }}}).
Proof.
  intros. iIntros "#HPQ #HQQ".
  iSplit.
  { (* wpc spec → normal wp spec *)
    iIntros "#Hwpc *!#*". iNamed 1. iIntros "HΦ".
    wp_apply (wpc_wp _ _ _ _ True).
    wpc_apply (wpc_crash_borrow_open_modify with "Hcrash").
    { done. }
    iSplit; first done.
    iIntros "HR".
    iApply wpc_fupd.
    iMod ("Hacc" with "HR") as "[HP Hclose]".
    wpc_apply ("Hwpc" with "HP").
    iSplit.
    { iIntros "Hc". iSplitR; first done. iLeft in "Hclose".
      by iMod ("Hclose" with "Hc") as "$". }
    iNext.
    iIntros "* HQ".
    iExists (R' r). iRight in "Hclose". iMod ("Hclose" with "HQ") as "HR".
    iModIntro. iFrame.
    iSplit.
    { iModIntro. iIntros "HR". iApply "HcrashOk". iFrame. }
    iIntros "Hcrash".
    iSplit; first done. iApply "HΦ".
    iFrame.
  }
  { (* normal wp spec → wpc spec *)
    iIntros "#Hwp !# * HP HΦ".
    iApply wpc_cfupd.
    wpc_apply (wpc_crash_borrow_inits with "[] HP HPQ").
    { admit. } (* FIXME: pre_borrow *)
    iIntros "Hcrash".
    wpc_apply (wpc_step_strong_mono _ _ _ _ _ Q _ True _ with "[Hcrash]").
    1-3: done.
    2:{
      iSplit.
      { iRight in "HΦ". iNext. iIntros "* HQ". iModIntro.
        by iApply "HΦ". }
      { iIntros "_ !#". iLeft in "HΦ". iIntros ">HQ".
        by iDestruct ("HΦ" with "HQ") as "$". }
    }
    iApply wp_wpc.
    wp_apply ("Hwp" with "[$Hcrash]").
    {
      iSplitL.
      {
        iIntros "$".
        iModIntro.
        iSplit.
        { iIntros "$ !> //". }
        iIntros "* HQ !>".
        iExact "HQ".
      }
      iFrame "HQQ".
    }
    iIntros (?) "Hcrash".
    admit. (* FIXME: sort of a "post_borrow" problem *)
  }
Admitted.

Lemma wpc_crash_borrow_open_cancel_unproven E1 e Φ Φc P Pc:
  language.to_val e = None →
  crash_borrow P Pc -∗
  (Φc ∧ (P -∗ WPC e @ E1
                    {{λ v, Φ v}}
                    {{ Φc ∗ Pc }})) -∗
  WPC e @ E1 {{ Φ }} {{ Φc }}.
Proof.
Admitted.

Lemma wpc_transformer2 e P Q Qc :
  goose_lang.(language.to_val) e = None →
  □ (P ={⊤}=∗ Qc) -∗
  □ (∀ r, Q r ={⊤}=∗ Qc) -∗
  (∀ R R' Qc',
  {{{
        "Hcrash" ∷ crash_borrow R (|={⊤}=> Qc') ∗
        "Hacc" ∷ (R ={⊤}=∗ P ∗ (Qc ={⊤}=∗ Qc') ∧ (∀ r, Q r ={⊤}=∗ R' r)) ∗
        "#HcrashOk" ∷ □(∀ r, R' r ={⊤}=∗ Qc')
  }}}
      e @ ⊤
  {{{
      r, RET r; crash_borrow (R' r) (|={⊤}=> Qc')
  }}}) -∗
  ({{{ P }}}
      (let: "r" := (Skip;; e) in "r") @ ⊤
  {{{ r, RET r; Q r }}}
  {{{ Qc }}}).
Proof.
  intros. iIntros "#HPQ #HQQ".
  (* normal wp spec → wpc spec *)
  iIntros "#Hwp !# * HP HΦ".
  iApply wpc_cfupd.
  wpc_bind (Skip).
  wpc_apply (wpc_crash_borrow_generate_pre with "[-]").
  { done. }
  wpc_pures.
  { iLeft in "HΦ". iMod ("HPQ" with "HP") as "HQ".
    iModIntro. iApply "HΦ". iFrame. }
  2:{ iLeft in "HΦ". iMod ("HPQ" with "HP") as "HQ".
      iModIntro. iApply "HΦ". iFrame. }
  clear Hcrash.
  iModIntro.
  iIntros "Hpre".
  wpc_apply (wpc_crash_borrow_inits with "Hpre HP HPQ").
  iIntros "Hcrash".
  (* wpc_bind (e). *)
  wpc_apply (wpc_step_strong_mono _ _ _ _ _ Q _ True _ with "[Hcrash]").
  1-3: done.
  2:{
    Search crash_borrow.
    iSplit.
    { iRight in "HΦ". iNext. iIntros "* HQ". iModIntro.
      by iApply "HΦ". }
    { iIntros "_ !#". iLeft in "HΦ". iIntros ">HQ".
      by iDestruct ("HΦ" with "HQ") as "$". }
  }
  iApply wp_wpc.
  wp_apply ("Hwp" with "[$Hcrash]").
  {
    iSplitL.
    {
      iIntros "$".
      iModIntro.
      iSplit.
      { iIntros "$ !> //". }
      iIntros "* HQ !>".
      iExact "HQ".
    }
    iFrame "HQQ".
  }
  iIntros (?) "Hcrash".
  iApply (wpc_wp _ _ _ _ True).
  wpc_apply (wpc_crash_borrow_open_cancel_unproven with "Hcrash").
  { done. }
  iSplit; first done.
  iIntros "HQ".
  wpc_pures.
  { iSplit; first done. by iApply "HQQ". }
  iModIntro.
  iFrame.
Qed.

End proof.
