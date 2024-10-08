From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section connect.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Connect
    (px : loc) (nid : u64) (nidme : u64) (addrm : gmap u64 chan) (addrpeer : chan) γ :
    addrm !! nid = Some addrpeer ->
    is_paxos_with_addrm px nidme addrm γ -∗
    {{{ True }}}
      Paxos__Connect #px #nid
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros (Haddrpeer) "#Hpx".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) Connect(nid uint64) bool {                             @*)
    (*@     addr := px.addrm[nid]                                               @*)
    (*@     ret := grove_ffi.Connect(addr)                                      @*)
    (*@     if !ret.Err {                                                       @*)
    (*@         px.mu.Lock()                                                    @*)
    (*@         px.conns[nid] = ret.Connection                                  @*)
    (*@         px.mu.Unlock()                                                  @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    iNamed "Hpx". iNamed "Haddrm".
    wp_loadField.
    wp_apply (wp_MapGet with "Haddrm").
    iIntros (addrpeer' ok) "[%Hok _]".
    destruct ok; last first.
    { apply map_get_false in Hok as [Hok _].
      by rewrite Haddrpeer in Hok.
    }
    apply map_get_true in Hok.
    rewrite Haddrpeer in Hok.
    symmetry in Hok. inv Hok.
    wp_pures.
    wp_apply wp_Connect.
    iIntros (err trml) "Htrml".
    wp_pures.
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked [Hpx Hcomm]]".
      iNamed "Hcomm".
      wp_loadField.
      wp_apply (map.wp_MapInsert with "Hconns").
      iIntros "Hconns".
      wp_loadField.
      (* Seal [trml c↦ ∅] in the network invariant and obtain [is_terminal γ trml]. *)
      iApply ncfupd_wp.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iNamed "HinvnetO".
      iMod (terminal_update trml with "Hterminals") as "[Hterminals #Htrmlrcpt]".
      iMod ("HinvnetC" with "[$Hlistens Hconnects Hterminals Htrml]") as "_".
      { iModIntro.
        iExists (<[trml := ∅]> connects).
        rewrite dom_insert_L.
        iFrame "Hterminals %".
        iApply (big_sepM_insert_2 with "[Htrml] Hconnects").
        iExists ∅.
        iFrame.
        iSplit; first by rewrite big_sepS_empty.
        iPureIntro.
        by rewrite 2!set_map_empty.
      }
      iModIntro.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $HconnsP $Hpx Hconns]").
      { iModIntro.
        iExists (<[nid := (trml, addrpeer)]> conns).
        rewrite fmap_insert.
        iFrame "Hconns".
        iSplit.
        { by iApply big_sepM_insert_2. }
        iPureIntro.
        by apply map_Forall_insert_2.
      }
      wp_pures.
      by iApply "HΦ".
    }
    by iApply "HΦ".
  Qed.

End connect.
