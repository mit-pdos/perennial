From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr paxos_leading.
From Perennial.program_proof.tulip.paxos.invariance Require Import extend.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section submit.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Submit (px : loc) (c : string) nidme γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
    <<< ∀∀ cpool, own_cpool_half γ cpool >>>
      Paxos__Submit #px #(LitString c) @ ↑paxosNS
    <<< own_cpool_half γ ({[c]} ∪ cpool) >>>
    (* TODO: return a receipt for checking committedness from the client. *)
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term); True }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> _ HAU".
    wp_rec.

    (*@ func (px *Paxos) Submit(v string) (uint64, uint64) {                    @*)
    (*@     px.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    iNamed "Hinv".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked [Hpx Hcomm]]".

    (*@     if !px.leading() {                                                  @*)
    (*@         px.mu.Unlock()                                                  @*)
    (*@         return 0, 0                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__leading with "Hpx").
    iIntros (isleader) "Hpx".
    destruct isleader; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").
      wp_pures.
      iInv "Hinv" as "> HinvO" "HinvC".
      iMod "HAU" as (cpoolcli) "[Hcpoolcli HAU]".
      iNamed "HinvO".
      iDestruct (cpool_agree with "Hcpool Hcpoolcli") as %->.
      iMod (cpool_update ({[c]} ∪ cpool) with "Hcpool Hcpoolcli") as "[Hcpool Hcpoolcli]".
      { set_solver. }
      iMod ("HAU" with "Hcpoolcli") as "HΦ".
      iMod ("HinvC" with "[-HΦ]") as "_".
      { iFrame "∗ # %". }
      by iApply "HΦ".
    }

    (*@     lsn := uint64(len(px.log))                                          @*)
    (*@     px.log = append(px.log, v)                                          @*)
    (*@     term := px.termc                                                    @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_apply wp_slice_len.
    wp_loadField.
    wp_apply (wp_SliceAppend with "Hlog").
    iIntros (logP') "Hlog".
    wp_storeField.
    wp_loadField.

    (*@     // Logical action: Extend(@px.termc, @px.log).                      @*)
    (*@                                                                         @*)
    iApply ncfupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod "HAU" as (cpoolcli) "[Hcpoolcli HAU]".
    iAssert (|==> own_cpool_half γ ({[c]} ∪ cpoolcli) ∗ paxos_inv γ nids)%I
      with "[Hcpoolcli HinvO]" as "HcpoolU".
    { iNamed "HinvO".
      iDestruct (cpool_agree with "Hcpool Hcpoolcli") as %->.
      iMod (cpool_update ({[c]} ∪ cpool) with "Hcpool Hcpoolcli") as "[Hcpool Hcpoolcli]".
      { set_solver. }
      by iFrame "∗ # %".
    }
    iMod "HcpoolU" as "[Hcpoolcli HinvO]".
    iDestruct (cpool_witness c with "Hcpoolcli") as "#Hc".
    { set_solver. }
    iNamed "Hleader". iNamed "Honlyl".
    subst terml.
    iNamed "Hnids".
    iMod (paxos_inv_extend [c] with "[] Hps Htermc Hterml Hlogn HinvO")
      as "(Hps & Htermc & Hterml & Hlogn & HinvO & #Hacpted')".
    { set_solver. }
    { by iApply big_sepL_singleton. }
    iMod ("HAU" with "Hcpoolcli") as "HΦ".
    iMod ("HinvC" with "HinvO") as "_".
    iModIntro.

    (*@     // Potential batch optimization: Even though we update @px.log here, but it @*)
    (*@     // should be OK to not immediately write them to disk, but wait until those @*)
    (*@     // entries are sent in @LeaderSession. To prove the optimization, we'll need @*)
    (*@     // to decouple the "batched entries" from the actual entries @px.log, and @*)
    (*@     // relate only @px.log to the invariant.                            @*)
    (*@                                                                         @*)
    (*@     px.mu.Unlock()                                                      @*)
    (*@     return lsn, term                                                    @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked".
      iDestruct (terml_eq_termc_impl_not_nominiated with "Hcand") as %->; first done.
      set log' := log ++ [c].
      iAssert (own_paxos_leader px nidme termc termc log' true nids γ)%I
        with "[$HisleaderP $HlsnpeersP $Hlsnpeers $Hps $Haocm]" as "Hleader".
      { iPureIntro.
        split; first done.
        split; last done.
        apply (map_Forall_impl _ _ _ Hlelog).
        intros _ lsn Hlsn.
        rewrite length_app /=.
        clear -Hlsn. lia.
      }
      iNamed "Hcand".
      iFrame "Hleader".
      set logc' := take (uint.nat lsnc) log'.
      iAssert (safe_ledger_above γ nids (uint.nat termc) logc')%I as "Hcmted'".
      { subst logc'.
        rewrite (take_prefix_le _ log' (uint.nat lsnc) _); last first.
        { by apply prefix_app_r. }
        { clear -Hlsncub. word. }
        done.
      }
      iFrame "Hcmted'".
      iFrame "∗ # %".
      iSplit.
      { iDestruct "Hgebase" as (vlb) "[Hvlb %Hprefix]".
        iFrame "Hvlb".
        iPureIntro.
        trans log; [apply Hprefix | by apply prefix_app_r].
      }
      iSplit.
      { by case_decide. }
      iPureIntro.
      rewrite length_app /=.
      clear -Hlsncub. lia.
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

End submit.
