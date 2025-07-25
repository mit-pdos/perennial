From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr paxos_leading paxos_obtain paxos_gettermc paxos_getlsnc paxos_send
  encode_accept_request.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section leader_session.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__LeaderSession (px : loc) (nidme : u64) γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
      Paxos__LeaderSession #px
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hpx" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) LeaderSession() {                                      @*)
    (*@     for {                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.

    (*@         px.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    iNamed "Hpx".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked [Hpx Hcomm]]".
    wp_loadField.
    wp_apply (wp_Cond__Wait with "[-HΦ]").
    { by iFrame "Hcv Hlock Hlocked ∗". }
    iIntros "(Hlocked & Hpx & Hcomm)".

    (*@         if !px.leading() {                                              @*)
    (*@             px.mu.Unlock()                                              @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__leading with "Hpx").
    iIntros (isleader) "Hpx".
    destruct isleader; wp_pures; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").
      wp_pures.
      by iApply "HΦ".
    }

    (*@         // TODO: Write @px.log to disk before sending out APPEND-ENTRIES. @*)
    (*@                                                                         @*)
    (*@         for _, nidloop := range(px.peers) {                             @*)
    (*@                                                                         @*)
    set P := (λ (_ : u64), own_paxos_leading px nidme (dom addrm) γ)%I.
    iNamed "Hnids".
    wp_loadField.
    iMod (readonly_load with "Hpeers") as (q) "HpeersR".
    wp_apply (wp_forSlice P with "[] [$HpeersR $Hpx]").
    { (* Loop body. *)
      clear Φ.
      iIntros (i nid Φ) "!> (Hpx & %Hbound & %Hnid) HΦ".

      (*@             nid := nidloop                                              @*)
      (*@             lsne, ents := px.obtain(nid)                                @*)
      (*@             termc := px.gettermc()                                      @*)
      (*@             lsnc  := px.getlsnc()                                       @*)
      (*@                                                                         @*)
      wp_pures.
      subst P. simpl.
      iAssert (∃ termc, own_paxos_leading_with_termc px nidme termc (dom addrm) γ)%I
        with "Hpx" as (termc) "Hpx".
      wp_apply (wp_Paxos__obtain with "Hpx").
      iIntros (lsne entsP ents loga) "(Hpx & Hents & #Hpfb & #Hpfg & %Hlenloga & %Hents)".
      wp_pures.
      wp_apply (wp_Paxos__gettermc__leading with "Hpx").
      iIntros "Hpx".
      wp_apply (wp_Paxos__getlsnc with "Hpx").
      iIntros (lsnc logc) "(Hpx & #Hlogc & %Hlenlogc)".
      wp_pures.

      (*@             go func() {                                                 @*)
      (*@                 data := message.EncodePaxosAppendEntriesRequest(termc, lsnc, lsne, ents) @*)
      (*@                 px.Send(nid, data)                                      @*)
      (*@             }()                                                         @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_apply (wp_fork with "[Hents]").
      { iModIntro.
        clear Φ.
        wp_apply (wp_EncodeAcceptRequest with "Hents").
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
          set req := AppendEntriesReq _ _ _ _ in Hdataenc.
          iExists ({[req]} ∪ reqs).
          iSplit.
          { rewrite set_map_union_L set_map_singleton_L.
            by iApply big_sepS_insert_2.
          }
          iSplit.
          { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
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
      iApply "HΦ".
      iFrame.
    }

    (*@         px.mu.Unlock()                                                  @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iIntros "[Hpx _]".
    wp_loadField.
    subst P.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hpx $Hcomm]").
    { iNamed "Hpx". iFrame. }
    wp_pures.
    by iApply "HΦ".
  Qed.

End leader_session.
