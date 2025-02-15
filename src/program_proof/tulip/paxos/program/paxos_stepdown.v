From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr paxos_log.
From Perennial.program_proof.tulip.paxos.invariance Require Import prepare.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section stepdown.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__stepdown px (nidme term : u64) termc nids γ :
    nidme ∈ nids ->
    uint.Z termc ≤ uint.Z term < 2 ^ 64 ->
    is_paxos_fname px nidme γ -∗
    know_paxos_file_inv γ nids -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__stepdown #px #term
    {{{ RET #(); own_paxos_following_with_termc px nidme term nids γ }}}.
  Proof.
    iIntros (Hnidme Hlt) "#Hfname #Hinvfile #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) stepdown(term uint64) {                                @*)
    (*@     px.iscand = false                                                   @*)
    (*@     px.isleader = false                                                 @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hcand". iNamed "Hleader".
    do 2 wp_storeField.
    wp_loadField.
    wp_pures.
    case_bool_decide as Hne; wp_pures.
    { iApply "HΦ". inv Hne. by iFrame "∗ # %". }

    (*@     if px.termc == term {                                               @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_storeField.

    (*@     px.termc = term                                                     @*)
    (*@     // Logical action: Prepare(@term).                                  @*)
    (*@     logPrepare(px.fname, term)                                          @*)
    (*@ }                                                                       @*)
    iNamed "Hfname".
    wp_loadField.
    wp_apply wp_logPrepare.
    iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
    { solve_ndisj. }
    iNamed "Hdurable".
    iInv "Hinv" as "> HinvO" "HinvC".
    iInv "Hinvfile" as "> HinvfileO" "HinvfileC".
    iDestruct (big_sepS_elem_of_acc with "HinvfileO") as "[Hnodefile HinvfileO]".
    { apply Hnidme. }
    iNamed "Hnodefile".
    iApply ncfupd_mask_intro; first solve_ndisj.
    iIntros "Hmask".
    iDestruct (node_wal_fname_agree with "Hfnameme Hwalfname") as %->.
    iFrame "Hfile %".
    iIntros (bs' failed) "Hfile".
    destruct failed.
    { (* Case: Write failed. Close the invariant without any updates. *)
      iMod "Hmask" as "_".
      iDestruct ("HinvfileO" with "[Hfile Hwalfile]") as "HinvfileO".
      { iFrame "∗ # %". }
      iMod ("HinvfileC" with "HinvfileO") as "_".
      iMod ("HinvC" with "HinvO") as "_".
      set dst := PaxosDurable termc terml log lsnc.
      iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
      by iIntros "!> %Hcontra".
    }
    (* Case: Write succeeded. *)
    iDestruct "Hfile" as "[Hfile %Hbs']".
    iMod (paxos_inv_prepare (uint.nat term) with "Hwalfile Htermc Hterml Hlogn HinvO")
      as "(Hwalfile & Htermc & Hterml & Hlogn & HinvO & Hlsnp & #Hpromise)".
    { apply Hnidme. }
    { clear -Hlt Hne. apply u64_val_ne in Hne. word. }
    iDestruct ("HinvfileO" with "[Hfile Hwalfile]") as "HinvfileO".
    { iFrame "∗ # %".
      iPureIntro.
      apply Forall_app_2; first apply Hvdwal.
      rewrite Forall_singleton /=.
      word.
    }
    iMod "Hmask" as "_".
    iMod ("HinvfileC" with "HinvfileO") as "_".
    iMod ("HinvC" with "HinvO") as "_".
    set dst := PaxosDurable term terml log lsnc.
    iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
    iIntros "!> _".
    wp_pures.
    iApply "HΦ".
    iFrame "HisleaderP HiscandP".
    assert (Htermlc' : uint.Z terml ≤ uint.Z term) by word.
    iFrame "∗ # %".
    iClear "Hpreped Hlsnp".
    by case_decide.
  Qed.

End stepdown.
