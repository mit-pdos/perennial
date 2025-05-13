From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr paxos_get_connection paxos_connect.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section send.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Send
    (px : loc) (nid : u64) (dataP : Slice.t) (data : list u8) (nidme : u64)
    (addrm : gmap u64 chan) (addrpeer : chan) γ :
    addrm !! nid = Some addrpeer ->
    is_paxos_with_addrm px nidme addrm γ -∗
    {{{ own_slice dataP byteT (DfracOwn 1) data }}}
    <<< ∀∀ ms, addrpeer c↦ ms >>>
      Paxos__Send #px #nid (to_val dataP) @ ∅
    <<< ∃∃ (ok : bool),
            if ok 
            then ∃ trml, addrpeer c↦ ({[Message trml data]} ∪ ms) ∗ is_terminal γ trml
            else addrpeer c↦ ms
    >>>
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Haddrpeer) "#Hpx".
    iIntros (Φ) "!> Hdata HAU".
    wp_rec.

    (*@ func (px *Paxos) Send(nid uint64, data []byte) {                        @*)
    (*@     conn, ok := px.GetConnection(nid)                                   @*)
    (*@     if !ok {                                                            @*)
    (*@         px.Connect(nid)                                                 @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__GetConnection with "Hpx").
    { apply Haddrpeer. }
    iIntros (trml ok) "#Htrmlrcpt".
    wp_pures.
    destruct ok; wp_pures; last first.
    { wp_apply (wp_Paxos__Connect with "Hpx").
      { apply Haddrpeer. }
      iIntros (ok) "Hok".
      wp_pures.
      (* Open the AU without updating. *)
      iMod (ncfupd_mask_subseteq (⊤ ∖ ∅)) as "Hclose"; first solve_ndisj.
      iMod "HAU" as (ms) "[Hms HAU]".
      iMod ("HAU" $! false with "Hms") as "HΦ".
      iMod "Hclose" as "_".
      by iApply "HΦ".
    }

    (*@     err := grove_ffi.Send(conn, data)                                   @*)
    (*@     if err {                                                            @*)
    (*@         px.Connect(nid)                                                 @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iDestruct (own_slice_to_small with "Hdata") as "Hdata".
    wp_apply (wp_Send with "Hdata").
    iMod "HAU" as (ms) "[Hms HAU]".
    iFrame "Hms".
    iIntros "!>" (sent) "Hms".
    iMod ("HAU" $! sent with "[Hms]") as "HΦ".
    { rewrite union_comm_L. by destruct sent; first iFrame. }
    iModIntro.
    iIntros (err) "[%Herr Hdata]".
    wp_pures.
    wp_if_destruct.
    { wp_apply (wp_Paxos__Connect with "Hpx").
      { apply Haddrpeer. }
      iIntros (ok) "_".
      wp_pures.
      by iApply "HΦ".
    }
    by iApply "HΦ".
  Qed.

End send.
