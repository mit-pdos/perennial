From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr paxos_leading paxos_heartbeated paxos_heartbeat paxos_resethb
  paxos_nominate paxos_nominated paxos_gettermc paxos_getlsnc
  paxos_send encode_prepare_request.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section election_session.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__ElectionSession (px : loc) (nidme : u64) γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
      Paxos__ElectionSession #px
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hpx" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) ElectionSession() {                                    @*)
    (*@     for {                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.

    (*@         delta := primitive.RandomUint64() % params.NS_ELECTION_TIMEOUT_DELTA @*)
    (*@         primitive.Sleep(params.NS_ELECTION_TIMEOUT_BASE + delta)        @*)
    (*@                                                                         @*)
    wp_apply wp_RandomUint64.
    iIntros (dt) "_".
    wp_apply wp_Sleep.

    (*@         px.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    iNamed "Hpx".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked [Hpx Hcomm]]".
    wp_pures.

    (*@         if px.leading() {                                               @*)
    (*@             px.mu.Unlock()                                              @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__leading with "Hpx").
    iIntros (isleader) "Hpx".
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
      { iNamed "Hpx". iFrame. }
      wp_pures.
      by iApply "HΦ".
    }
    subst isleader.

    (*@         if px.heartbeated() {                                           @*)
    (*@             px.resethb()                                                @*)
    (*@             px.mu.Unlock()                                              @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__heartbeated with "Hpx").
    iIntros (hb) "Hpx".
    wp_if_destruct.
    { wp_apply (wp_Paxos__resethb with "Hpx").
      iIntros "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
      { iNamed "Hpx". iFrame. }
      wp_pures.
      by iApply "HΦ".
    }
    subst hb.

    (*@         var termc uint64                                                @*)
    (*@         var lsnc uint64                                                 @*)
    (*@         if px.nominated() {                                             @*)
    (*@             termc = px.gettermc()                                       @*)
    (*@             lsnc = px.getlsnc()                                         @*)
    (*@         } else {                                                        @*)
    (*@             termc, lsnc = px.nominate()                                 @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first done.
    iIntros (termcP) "HtermcP".
    wp_apply wp_ref_of_zero; first done.
    iIntros (lsncP) "HlsncP".
    wp_pures.
    iDestruct (own_paxos_expose_termc with "Hpx") as (termc) "Hpx".
    wp_apply (wp_Paxos__nominated with "Hpx").
    iIntros (iscand) "Hpx".
    set P := (∃ (termc lsnc : u64),
                 "Hpx"      ∷ own_paxos px nidme (dom addrm) γ ∗
                 "HtermcP"  ∷ termcP ↦[uint64T] #termc ∗
                 "HlsncP"   ∷ lsncP ↦[uint64T] #lsnc ∗
                 "#Hlsnprc" ∷ is_prepare_lsn γ (uint.nat termc) (uint.nat lsnc))%I.
    wp_apply (wp_If_join P with "[Hpx HtermcP HlsncP]").
    { iSplit; iIntros (->).
      { wp_apply (wp_Paxos__gettermc__nominated with "Hpx").
        iIntros "Hpx".
        wp_store.
        wp_apply (wp_Paxos__getlsnc__nominated with "Hpx").
        iIntros (lsnc) "[Hpx #Hlsnprc]".
        wp_store.
        iModIntro.
        iSplit; first done.
        iNamed "Hpx".
        iFrame "∗ #".
      }
      { iDestruct (own_paxos_hide_termc with "Hpx") as "Hpx".
        clear termc.
        wp_apply (wp_Paxos__nominate with "Hnids Hfname Hinvfile Hinv Hpx").
        { apply Hnidme. }
        iIntros (termc lsnc) "[Hpx #Hlsnprc]".
        wp_pures.
        do 2 wp_store.
        iModIntro.
        iSplit; first done.
        iFrame "∗ #".
      }
    }
    clear termc. subst P.
    iNamed 1.

    (*@         px.mu.Unlock()                                                  @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").

    (*@         for _, nidloop := range(px.peers) {                             @*)
    (*@             nid := nidloop                                              @*)
    (*@             go func() {                                                 @*)
    (*@                 data := message.EncodePaxosRequestVoteRequest(termc, lsnc) @*)
    (*@                 px.Send(nid, data)                                      @*)
    (*@             }()                                                         @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hnids".
    wp_loadField.
    iMod (readonly_load with "Hpeers") as (q) "HpeersR".
    iMod (readonly_alloc_1 with "HtermcP") as "#HtermcP".
    iMod (readonly_alloc_1 with "HlsncP") as "#HlsncP".
    wp_apply (wp_forSlice (λ _, emp)%I with "[] [$HpeersR]").
    { (* Loop body. *)
      clear Φ.
      iIntros (i nid Φ) "!> (HP & %Hbound & %Hnid) HΦ".
      iNamed "HP".
      wp_pures.
      wp_apply wp_fork.
      { wp_apply (wp_load_ro with "HlsncP").
        wp_apply (wp_load_ro with "HtermcP").
        wp_apply wp_EncodePrepareRequest.
        iIntros (dataP data) "[Hdata %Hdataenc]".
        iNamed "Haddrm".
        assert (is_Some (addrm !! nid)) as [addrpeer Haddrpeer].
        { rewrite -elem_of_dom.
          apply list_elem_of_lookup_2 in Hnid.
          set_solver.
        }
        wp_apply (wp_Paxos__Send with "[] Hdata"); first apply Haddrpeer.
        { iFrame "# %". }
        iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iNamed "HinvnetO".
        assert (is_Some (listens !! addrpeer)) as [ms Hms].
        { rewrite -elem_of_dom -Himgaddrm elem_of_map_img. by eauto. }
        iDestruct (big_sepM_delete with "Hlistens") as "[Hlst Hlistens]"; first apply Hms.
        iNamed "Hlst".
        iFrame "Hms".
        iIntros (sent) "Hms".
        destruct sent; last first.
        { iDestruct (big_sepM_insert_2 _ _ addrpeer ms with "[Hms] Hlistens") as "Hlistens".
          { iFrame "∗ # %". }
          rewrite insert_delete_id; last apply Hms.
          iMod "Hmask" as "_".
          iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_".
          { done. }
          done.
        }
        iDestruct "Hms" as (trml) "[Hms #Htrml]".
        set ms' := _ ∪ ms.
        iDestruct (big_sepM_insert_2 _ _ addrpeer ms' with "[Hms] Hlistens") as "Hlistens".
        { iFrame "Hms".
          set req := RequestVoteReq _ _ in Hdataenc.
          iExists ({[req]} ∪ reqs).
          iSplit.
          { rewrite set_map_union_L set_map_singleton_L.
            by iApply big_sepS_insert_2.
          }
          iSplit.
          { iApply big_sepS_insert_2; last done.
            iFrame "Hlsnprc".
          }
          iPureIntro.
          rewrite 2!set_map_union_L 2!set_map_singleton_L.
          set_solver.
        }
        rewrite insert_delete_eq.
        iMod "Hmask" as "_".
        iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_".
        { iPureIntro.
          rewrite dom_insert_L Himgaddrm.
          apply (elem_of_map_img_2 (SA := gset chan)) in Haddrpeer.
          set_solver.
        }
        done.
      }
      by iApply "HΦ".
    }
    iIntros "_".
    wp_pures.
    by iApply "HΦ".
  Qed.

End election_session.
