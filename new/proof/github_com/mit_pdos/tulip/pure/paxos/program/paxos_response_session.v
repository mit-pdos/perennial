From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr paxos_lttermc paxos_gttermc paxos_stepdown paxos_nominated paxos_collect
  paxos_ascend paxos_leading paxos_forward paxos_push paxos_commit paxos_receive
  decode_response.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section response_sesion.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__ResponseSession
    (px : loc) (nid : u64) (nidme : u64)
    (addrpeer : chan) (addrm : gmap u64 chan) γ :
    addrm !! nid = Some addrpeer ->
    is_paxos_with_addrm px nidme addrm γ -∗
    {{{ True }}}
      Paxos__ResponseSession #px #nid
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Haddrpeer) "#Hpx".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) ResponseSession(nid uint64) {                          @*)
    (*@     for {                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.

    (*@         data, ok := px.Receive(nid)                                     @*)
    (*@         if !ok {                                                        @*)
    (*@             // Try to re-establish a connection on failure.             @*)
    (*@             primitive.Sleep(params.NS_RECONNECT)                        @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Receive with "Hpx").
    { apply Haddrpeer. }
    iIntros (dataP ok) "Hdata".
    wp_pures.
    destruct ok; wp_pures; last first.
    { wp_apply wp_Sleep.
      wp_pures.
      by iApply "HΦ".
    }
    iDestruct "Hdata" as (data resp) "(Hdata & #Hresp & %Hdataenc)".

    (*@         resp := message.DecodePaxosResponse(data)                       @*)
    (*@         kind := resp.Kind                                               @*)
    (*@                                                                         @*)
    iDestruct (own_slice_to_small with "Hdata") as "Hdata".
    rewrite Hdataenc.
    wp_apply (wp_DecodeResponse with "Hdata").
    iIntros (entsP) "Hents".
    destruct resp as [nid' term terme ents | nid' term lsneq]; wp_pures.
    { (* Case: RequestVote. *)
      
      (*@         px.mu.Lock()                                                    @*)
      (*@                                                                         @*)
      iNamed "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked [Hpx Hcomm]]".

      (*@         if px.lttermc(resp.Term) {                                      @*)
      (*@             // Skip the outdated message.                               @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_pures.
      wp_apply (wp_Paxos__lttermc with "Hpx").
      iIntros (outdated) "Hpx".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").
        wp_pures.
        by iApply "HΦ".
      }

      (*@         // In the current design, the response would never contain a term higher @*)
      (*@         // than that in a request, and that means this check is actually not @*)
      (*@         // used. However, it is kept for two reasons: First, if adding an @*)
      (*@         // UPDATE-TERM becomes necessary (for performance or liveness reason), @*)
      (*@         // then this check would then be useful. Second, in the proof, with this @*)
      (*@         // check and the one above we obtain @px.termc = @resp.Term, which is @*)
      (*@         // very useful. If we ever want to eliminate this check in the future, @*)
      (*@         // we will have to find a way to encode ``responses terms never go higher @*)
      (*@         // than request terms'' in the proof.                           @*)
      (*@         if px.gttermc(resp.Term) {                                      @*)
      (*@             // Proceed to a new term on receiving a higher-term message. @*)
      (*@             px.stepdown(resp.Term)                                      @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_pures.
      iDestruct "Hpx" as (termc) "[Hpx %Hgttermc]".
      wp_apply (wp_Paxos__gttermc with "Hpx").
      iIntros (invalid) "[Hpx %Hlttermc]".
      wp_if_destruct.
      { wp_pures.
        wp_apply (wp_Paxos__stepdown with "Hfname Hinvfile Hinv Hpx").
        { apply Hnidme. }
        { clear -Hgttermc. word. }
        iIntros "Hpx".
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }
      assert (termc = term) as ->.
      { clear -Hgttermc Hlttermc. word. }
      wp_pures.

      (*@         if kind == message.MSG_PAXOS_REQUEST_VOTE {                     @*)
      (*@             if !px.nominated() {                                        @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__nominated with "Hpx").
      iIntros (iscand) "Hpx".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").
        wp_pures.
        by iApply "HΦ".
      }
      iAssert (∃ lsnc, own_paxos_nominated_with_termc_lsnc px nidme term lsnc (dom addrm) γ)%I
        with "[Hpx]" as (lsnc) "Hpx".
      { iNamed "Hpx". iFrame. }

      (*@             // Ideally, we should not need to include the node ID in the @*)
      (*@             // response, since the entire session is used exclusively by @nid @*)
      (*@             // (i.e., in reality @resp.NodeID should always be the same as @*)
      (*@             // @nid). In the proof, we could maintain a persistent mapping from @*)
      (*@             // channels to node IDs. However, it seems like the current network @*)
      (*@             // semantics does not guarantee *freshness* of creating a channel @*)
      (*@             // through @Connect, and hence such invariant cannot be established. @*)
      (*@             px.collect(resp.NodeID, resp.TermEntries, resp.Entries)     @*)
      (*@             px.ascend()                                                 @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@                                                                         @*)
      iNamed "Hresp".
      iAssert (⌜lsne = lsnc⌝)%I as %->.
      { iNamed "Hpx". iNamed "Hcand". iNamed "Honlyc". iNamed "Hpx".
        iDestruct (prepare_lsn_eq with "Hlsne Hlsnprc") as %Heq.
        rewrite length_take_le in Heq; last first.
        { clear -Hlsncub. lia. }
        clear -Heq.
        iPureIntro.
        clear -Heq.
        word.
      }
      wp_pures.
      wp_apply (wp_Paxos__collect with "Hpromise Hinv [$Hpx $Hents]").
      { apply Hinnids. }
      { apply Hents. }
      iIntros "Hpx".
      wp_apply (wp_Paxos__ascend with "Hfname Hinvfile Hinv Hpx").
      { apply Hnidme. }
      iIntros "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: AppendEntries. *)

      (*@         px.mu.Lock()                                                    @*)
      (*@                                                                         @*)
      iNamed "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked [Hpx Hcomm]]".

      (*@         if px.lttermc(resp.Term) {                                      @*)
      (*@             // Skip the outdated message.                               @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_pures.
      wp_apply (wp_Paxos__lttermc with "Hpx").
      iIntros (outdated) "Hpx".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").
        wp_pures.
        by iApply "HΦ".
      }

      (*@         // In the current design, the response would never contain a term higher @*)
      (*@         // than that in a request, and that means this check is actually not @*)
      (*@         // used. However, it is kept for two reasons: First, if adding an @*)
      (*@         // UPDATE-TERM becomes necessary (for performance or liveness reason), @*)
      (*@         // then this check would then be useful. Second, in the proof, with this @*)
      (*@         // check and the one above we obtain @px.termc = @resp.Term, which is @*)
      (*@         // very useful. If we ever want to eliminate this check in the future, @*)
      (*@         // we will have to find a way to encode ``responses terms never go higher @*)
      (*@         // than request terms'' in the proof.                           @*)
      (*@         if px.gttermc(resp.Term) {                                      @*)
      (*@             // Proceed to a new term on receiving a higher-term message. @*)
      (*@             px.stepdown(resp.Term)                                      @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_pures.
      iDestruct "Hpx" as (termc) "[Hpx %Hgttermc]".
      wp_apply (wp_Paxos__gttermc with "Hpx").
      iIntros (invalid) "[Hpx %Hlttermc]".
      wp_if_destruct.
      { wp_pures.
        wp_apply (wp_Paxos__stepdown with "Hfname Hinvfile Hinv Hpx").
        { apply Hnidme. }
        { clear -Hgttermc. word. }
        iIntros "Hpx".
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }
      assert (termc = term) as ->.
      { clear -Hgttermc Hlttermc. word. }
      wp_pures.

      (*@         } else if kind == message.MSG_PAXOS_APPEND_ENTRIES {            @*)
      (*@             if !px.leading() {                                          @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__leading__with_termc with "Hpx").
      iIntros (isleader) "Hpx".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").
        wp_pures.
        by iApply "HΦ".
      }
      wp_pures.

      (*@             // Same as the reason above, the check below is performed merely for @*)
      (*@             // the sake of proof.                                       @*)
      (*@             if resp.NodeID == px.nidme {                                @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      iNamed "Hnids".
      wp_loadField.
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }
      rename Heqb into Hnotme.
      wp_pures.

      (*@             forwarded := px.forward(resp.NodeID, resp.MatchedLSN)       @*)
      (*@             if !forwarded {                                             @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      iNamed "Hresp".
      wp_apply (wp_Paxos__forward with "Haoc Hinv Hpx").
      { apply Hnotme. }
      { apply Hinnids. }
      { apply Hlogacpt. }
      iIntros (forwarded) "Hpx".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }

      (*@             lsnc, pushed := px.push()                                   @*)
      (*@             if !pushed {                                                @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__push with "Hinv Hpx").
      { apply Hnidme. }
      iIntros (lsnc pushed) "[Hpx #Hpushed]".
      wp_if_destruct.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }
      iDestruct "Hpushed" as (logc) "[Hcmted %Hlenlogc]".

      (*@             px.commit(lsnc)                                             @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@         }                                                               @*)
      (*@     }                                                                   @*)
      (*@ }                                                                       @*)
      wp_apply (wp_Paxos__commit with "Hcmted Hfname Hinvfile Hinv [Hpx]").
      { apply Hnidme. }
      { apply Hlenlogc. }
      { iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl".
        iDestruct (terml_eq_termc_impl_not_nominiated with "Hcand") as %->.
        { apply Hleqc. }
        subst terml.
        iFrame "Hcand Hpx HisleaderP".
        by iFrame "∗ # %".
      }
      iIntros "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
      { iNamed "Hpx". iFrame. }
      wp_pures.
      by iApply "HΦ".
    }
  Qed.

End response_sesion.
