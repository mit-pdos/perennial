From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr paxos_lttermc paxos_stepdown paxos_heartbeat paxos_gettermc
  paxos_latest paxos_prepare paxos_accept paxos_learn
  decode_request encode_prepare_response encode_accept_response.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section request_session.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__RequestSession (px : loc) (addrme trml : chan) nidme addrm γ :
    addrm !! nidme = Some addrme ->
    is_paxos_with_addrm px nidme addrm γ -∗
    {{{ True }}}
      Paxos__RequestSession #px (connection_socket addrme trml)
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Haddrme) "#Hinv".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) RequestSession(conn grove_ffi.Connection) {            @*)
    (*@     for {                                                               @*)
    (*@         ret := grove_ffi.Receive(conn)                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.
    wp_apply wp_Receive.
    iNamed "Hinv". iNamed "Hnids".
    iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvnetO".
    assert (is_Some (listens !! addrme)) as [msl Hmsl].
    { rewrite -elem_of_dom -Himgaddrm elem_of_map_img. by eauto. }
    iDestruct (big_sepM_lookup_acc with "Hlistens") as "[Hlst HlistensC]"; first apply Hmsl.
    iNamed "Hlst".
    iFrame "Hms".
    iIntros (err retdata) "[Hms Herr]".
    iDestruct ("HlistensC" with "[$Hms]") as "Hlistens"; first iFrame "# %".
    iMod "Hmask" as "_".
    iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_"; first done.
    iIntros "!>" (retdataP) "Hretdata".

    (*@         if ret.Err {                                                    @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_pures.
    destruct err; wp_pures.
    { by iApply "HΦ". }
    iDestruct "Herr" as "%Hmsg".
    assert (∃ req, retdata = encode_pxreq req ∧ req ∈ reqs) as (req & Hreq & Hinreqs).
    { specialize (Henc retdata).
      apply (elem_of_map_2 msg_data (D := gset (list u8))) in Hmsg.
      specialize (Henc Hmsg).
      by rewrite elem_of_map in Henc.
    }

    (*@         req  := message.DecodePaxosRequest(ret.Data)                    @*)
    (*@         kind := req.Kind                                                @*)
    (*@                                                                         @*)
    iDestruct (own_slice_to_small with "Hretdata") as "Hretdata".
    rewrite Hreq.
    wp_apply (wp_DecodeRequest with "Hretdata").
    iIntros (entsaP) "Hentsa".
    destruct req as [term lsnc |]; wp_pures.
    { (* Case: RequestVote. *)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.

      (*@         px.mu.Lock()                                                    @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked [Hpx Hcomm]]".
      wp_apply (wp_Paxos__lttermc with "Hpx").
      iIntros (outdated) "Hpx".

      (*@         if px.lttermc(req.Term) {                                       @*)
      (*@             // Skip the oudated message.                                @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             // We can additionally send an UPDATE-TERM message, but not sure if @*)
      (*@             // that's necessary, since eventually the new leader would reach out @*)
      (*@             // to every node.                                           @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      destruct outdated; wp_pures.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").
        wp_pures.
        by iApply "HΦ".
      }

      (*@         // Potentially proceed to a new term on receiving a higher-term message. @*)
      (*@         px.stepdown(req.Term)                                           @*)
      (*@                                                                         @*)
      iDestruct "Hpx" as (termc) "[Hpx %Hgetermc]".
      wp_apply (wp_Paxos__stepdown with "Hfname Hinvfile Hinv Hpx").
      { apply Hnidme. }
      { clear -Hgetermc. word. }
      iIntros "Hpx".

      (*@         px.heartbeat()                                                  @*)
      (*@                                                                         @*)
      wp_pures.
      wp_apply (wp_Paxos__heartbeat__following_with_termc with "Hpx").
      iIntros "Hpx".

      (*@         termc := px.gettermc()                                          @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__gettermc__following with "Hpx").
      iIntros "Hpx".
      wp_pures.

      (*@         if kind == message.MSG_PAXOS_REQUEST_VOTE {                     @*)
      (*@             if px.latest() {                                            @*)
      (*@                 // The log has already matched up the current term, meaning the @*)
      (*@                 // leader has already successfully been elected. Simply ignore @*)
      (*@                 // this request.                                        @*)
      (*@                 px.mu.Unlock()                                          @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__latest with "Hpx").
      iIntros (latest) "Hpx".
      destruct latest; wp_pures.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
        { iNamed "Hpx". iFrame. }
        wp_pures.
        by iApply "HΦ".
      }
      iDestruct "Hpx" as (terml) "[Hpx %Hcnel]".

      (*@             terml, ents := px.prepare(req.CommittedLSN)                 @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             data := message.EncodePaxosRequestVoteResponse(px.nidme, termc, terml, ents) @*)
      (*@             // Request [REQUEST-VOTE, @termc, @lsnc] and                @*)
      (*@             // Response [REQUEST-VOTE, @termc, @terml, @ents] means:    @*)
      (*@             // (1) This node will not accept any proposal with term below @termc. @*)
      (*@             // (2) The largest-term entries after LSN @lsnc this node has @*)
      (*@             // accepted before @termc is (@terml, @ents).               @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__prepare with "Hpx").
      { apply Hcnel. }
      iIntros (entsP ents logpeer) "(Hpx & Hents & #Hpastd & %Hents)".
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
      { iNamed "Hpx". iFrame. }
      wp_loadField.
      wp_apply (wp_EncodePrepareResponse with "Hents").
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      iNamed "Hinv".
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' (dom addrm) γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := RequestVoteResp _ _ _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        rewrite 2!set_map_union_L 2!set_map_singleton.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: AppendEntries. *)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.

      (*@         px.mu.Lock()                                                    @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked [Hpx Hcomm]]".
      wp_apply (wp_Paxos__lttermc with "Hpx").
      iIntros (outdated) "Hpx".

      (*@         if px.lttermc(req.Term) {                                       @*)
      (*@             // Skip the oudated message.                                @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             // We can additionally send an UPDATE-TERM message, but not sure if @*)
      (*@             // that's necessary, since eventually the new leader would reach out @*)
      (*@             // to every node.                                           @*)
      (*@             continue                                                    @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      destruct outdated; wp_pures.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").
        wp_pures.
        by iApply "HΦ".
      }

      (*@         // Potentially proceed to a new term on receiving a higher-term message. @*)
      (*@         px.stepdown(req.Term)                                           @*)
      (*@                                                                         @*)
      iDestruct "Hpx" as (termc) "[Hpx %Hgetermc]".
      wp_apply (wp_Paxos__stepdown with "Hfname Hinvfile Hinv Hpx").
      { apply Hnidme. }
      { clear -Hgetermc. word. }
      iIntros "Hpx".

      (*@         px.heartbeat()                                                  @*)
      (*@                                                                         @*)
      wp_pures.
      wp_apply (wp_Paxos__heartbeat__following_with_termc with "Hpx").
      iIntros "Hpx".

      (*@         termc := px.gettermc()                                          @*)
      (*@                                                                         @*)
      wp_apply (wp_Paxos__gettermc__following with "Hpx").
      iIntros "Hpx".
      wp_pures.

      (*@         } else if kind == message.MSG_PAXOS_APPEND_ENTRIES {            @*)
      (*@             lsn := px.accept(req.LSNEntries, req.Term, req.Entries)     @*)
      (*@             px.learn(req.LeaderCommit, req.Term)                        @*)
      (*@             px.mu.Unlock()                                              @*)
      (*@             data := message.EncodePaxosAppendEntriesResponse(px.nidme, termc, lsn) @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@         }                                                               @*)
      (*@     }                                                                   @*)
      (*@ }                                                                       @*)
      iNamed "Hsafe".
      wp_apply (wp_Paxos__accept with "Hpfb Hpfg Hfname Hinvfile Hinv [$Hpx $Hentsa]").
      { apply Hnidme. }
      { apply Hlogleader. }
      { apply Hents. }
      iIntros (lsna loga) "(Hpx & #Haoc & %Hlenloga)".
      wp_pures.
      wp_apply (wp_Paxos__learn with "Hlogcmt Hfname Hinvfile Hinv Hpx").
      { apply Hnidme. }
      { apply Hlogcmt. }
      iIntros "Hpx".
      wp_loadField.

      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
      { iNamed "Hpx". iFrame. }
      wp_loadField.
      wp_apply (wp_EncodeAcceptResponse).
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      iNamed "Hinv".
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' (dom addrm) γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := AppendEntriesResp _ _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        rewrite 2!set_map_union_L 2!set_map_singleton.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
  Qed.

End request_session.
