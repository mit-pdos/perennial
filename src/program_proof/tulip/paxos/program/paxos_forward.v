From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section forward.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__forward
    (px : loc) (nid lsn : u64) (nidme termc : u64) (loga : list byte_string) nids γ :
    nid ≠ nidme ->
    nid ∈ nids ->
    length loga = uint.nat lsn ->
    (is_accepted_proposal_lb γ nid (uint.nat termc) loga ∨
     safe_ledger_above γ nids (uint.nat termc) loga) -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_leading_with_termc px nidme termc nids γ }}}
      Paxos__forward #px #nid #lsn
    {{{ (forwarded : bool), RET #forwarded; own_paxos_leading_with_termc px nidme termc nids γ }}}.
  Proof.
    iIntros (Hnotme Hnid Hlena) "#Haoc #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) forward(nid uint64, lsn uint64) bool {                 @*)
    (*@     lsnpeer, ok := px.lsnpeers[nid]                                     @*)
    (*@                                                                         @*)
    iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl".
    subst terml.
    wp_loadField.
    wp_apply (wp_MapGet with "Hlsnpeers").
    iIntros (lsnpeer ok) "[%Hok Hlsnpeers]".
    wp_pures.

    (*@     if !ok || lsnpeer < lsn {                                           @*)
    (*@         // Advance the peer's matching LSN.                             @*)
    (*@         px.lsnpeers[nid] = lsn                                          @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    (* Not sure how to properly handle TC resolution here. *)
    unshelve wp_apply (wp_or_pure (negb ok)).
    { shelve. }
    { apply _. }
    { shelve. }
    { wp_pures. by destruct ok; case_bool_decide. }
    { iIntros (_). by  wp_pures. }
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_MapInsert with "Hlsnpeers"); first done.
      iIntros "Hlsnpeers".
      wp_pures.
      iInv "Hinv" as "> HinvO" "HinvC".
      iAssert (⌜(length loga ≤ length log)%nat⌝)%I as %Hle.
      { iDestruct "Haoc" as "[Hacpted | Hcmted]".
        { (* Case: [loga] is accepted by [nid]. *)
          iDestruct (accepted_proposal_growing_proposal_impl_prefix with "Hacpted Hps HinvO")
            as %Hprefix.
          { apply Hnid. }
          iPureIntro.
          by apply prefix_length.
        }
        (* Case: [loga] has already be committed at this or an early term. *)
        iDestruct "Hcmted" as (p) "[Hsafe %Hple]".
        destruct (decide (p = uint.nat termc)) as [-> | Hne].
        { (* Case: [loga] committed in the current term. *)
          iDestruct "Hsafe" as (nidx) "Hsafe".
          iNamed "Hsafe".
          iDestruct (accepted_proposal_growing_proposal_impl_prefix with "Hvacpt Hps HinvO")
            as %Hprefix.
          { apply Hmember. }
          iPureIntro.
          by apply prefix_length.
        }
        (* Case: [loga] committed in an early term. *)
        assert (Hlt : (p < uint.nat termc)%nat) by lia.
        iNamed "Hpx".
        iDestruct (safe_ledger_prefix_base_ledger_impl_prefix with "Hsafe Hgebase HinvO")
          as %Hprefix.
        { apply Hlt. }
        iPureIntro.
        by apply prefix_length.
      }
      iMod ("HinvC" with "HinvO") as "_".
      iApply "HΦ".
      iFrame "Hpx Hcand".
      iFrame "∗ #".
      iModIntro.
      iAssert (safe_peer_lsns γ nids (uint.nat termc) (<[nid := lsn]> lsnpeers))%I as "Haocm'".
      { iDestruct "Haoc" as "[Hacpted | Hcmted]".
        { iNamed "Haocm".
          iExists (<[nid := true]> aocm).
          iApply big_sepM2_insert_2; last done.
          iFrame "Hacpted".
          iPureIntro. lia.
        }
        { iNamed "Haocm".
          iExists (<[nid := false]> aocm).
          iApply big_sepM2_insert_2; last done.
          iFrame "Hcmted".
          iPureIntro. lia.
        }
      }
      iFrame "Haocm'".
      iPureIntro.
      split; first done.
      split.
      { apply map_Forall_insert_2; [lia | apply Hlelog]. }
      { rewrite dom_insert_L. set_solver. }
    }

    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame "Hpx Hcand".
    by iFrame "∗ # %".
  Qed.

End forward.
