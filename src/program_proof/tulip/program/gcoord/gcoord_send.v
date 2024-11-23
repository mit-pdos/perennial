From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_get_connection gcoord_connect.

Section encode.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeTxnReadRequest (ts : u64) (key : string) :
    {{{ True }}}
      EncodeTxnReadRequest #ts #(LitString key)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_txnreq (ReadReq ts key)⌝
    }}}.
  Proof.
  Admitted.

End encode.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Send
    (gcoord : loc) (rid : u64) (dataP : Slice.t) (data : list u8)
    (addrm : gmap u64 chan) (addr : chan) gid γ :
    addrm !! rid = Some addr ->
    is_gcoord_with_addrm gcoord gid addrm γ -∗
    {{{ own_slice dataP byteT (DfracOwn 1) data }}}
    <<< ∀∀ ms, addr c↦ ms >>>
      GroupCoordinator__Send #gcoord #rid (to_val dataP) @ ∅
    <<< ∃∃ (ok : bool),
            if ok
            then ∃ trml, addr c↦ ({[Message trml data]} ∪ ms) ∗ is_terminal γ gid trml
            else addr c↦ ms
    >>>
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Haddr) "#Hgcoord".
    iIntros (Φ) "!> Hdata HAU".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Send(rid uint64, data []byte) {         @*)
    (*@     conn, ok := gcoord.GetConnection(rid)                               @*)
    (*@     if !ok {                                                            @*)
    (*@         gcoord.Connect(rid)                                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupCoordinator__GetConnection with "Hgcoord").
    { apply Haddr. }
    iIntros (trml ok) "#Htrmlrcpt".
    wp_pures.
    destruct ok; wp_pures; last first.
    { wp_apply (wp_GroupCoordinator__Connect with "Hgcoord").
      { apply Haddr. }
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
    (*@         gcoord.Connect(rid)                                             @*)
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
    { wp_apply (wp_GroupCoordinator__Connect with "Hgcoord").
      { apply Haddr. }
      iIntros (ok) "_".
      wp_pures.
      by iApply "HΦ".
    }
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__SendRead
    (gcoord : loc) (rid : u64) (ts : u64) (key : string) addrm gid γ :
    safe_read_req gid (uint.nat ts) key ->
    rid ∈ dom addrm ->
    is_gcoord_with_addrm gcoord gid addrm γ -∗
    {{{ True }}}
      GroupCoordinator__SendRead #gcoord #rid #ts #(LitString key)
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Hrid Hsafe) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) SendRead(rid, ts uint64, key string) {  @*)
    (*@     gcoord.Send(rid, message.EncodeTxnRead(ts, key))                    @*)
    (*@ }                                                                       @*)
    wp_apply (wp_EncodeTxnReadRequest).
    iIntros (dataP data) "[Hdata %Hdataenc]".
    iNamed "Hgcoord".
    iNamed "Haddrm".
    assert (is_Some (addrm !! rid)) as [addrpeer Haddrpeer].
    { by apply elem_of_dom. }
    wp_apply (wp_GroupCoordinator__Send with "[] Hdata"); first apply Haddrpeer.
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
      rewrite insert_delete; last apply Hms.
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_".
      { done. }
      iIntros "!> _".
      wp_pures.
      by iApply "HΦ".
    }
    iDestruct "Hms" as (trml) "[Hms #Htrml]".
    set ms' := _ ∪ ms.
    iDestruct (big_sepM_insert_2 _ _ addrpeer ms' with "[Hms] Hlistens") as "Hlistens".
    { iFrame "Hms".
      set req := ReadReq _ _ in Hdataenc.
      iExists ({[req]} ∪ reqs).
      iSplit.
      { rewrite set_map_union_L set_map_singleton_L.
        by iApply big_sepS_insert_2.
      }
      iSplit.
      { iApply big_sepS_insert_2; [done | done]. }
      iPureIntro.
      rewrite 2!set_map_union_L 2!set_map_singleton_L /= -Hdataenc.
      set_solver.
    }
    rewrite insert_delete_insert.
    iMod "Hmask" as "_".
    iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_".
    { iPureIntro.
      rewrite dom_insert_L Himgaddrm.
      apply (elem_of_map_img_2 (SA := gset chan)) in Haddrpeer.
      set_solver.
    }
    iIntros "!> _".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__SendFastPrepare
    (gcoord : loc) (rid : u64) (ts : u64) (pwrsP : loc) (ptgsP : Slice.t) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendFastPrepare #gcoord #rid #ts #pwrsP (to_val ptgsP)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendFastPrepare(rid, ts uint64, pwrs tulip.KVMap, ptgs []uint64) { @*)
    (*@     gcoord.Send(rid, message.EncodeTxnFastPrepare(ts, pwrs, ptgs))      @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendValidate
    (gcoord : loc) (rid : u64) (ts : u64) (rank : u64) (pwrsP : loc) (ptgsP : Slice.t) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendValidate #gcoord #rid #ts #rank #pwrsP (to_val ptgsP)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendValidate(rid, ts, rank uint64, pwrs tulip.KVMap, ptgs []uint64) { @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendPrepare
    (gcoord : loc) (rid : u64) (tsW : u64) (rank : u64) gid γ :
    let ts := uint.nat tsW in
    is_group_prepare_proposal γ gid ts 1%nat true -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendPrepare #gcoord #rid #tsW #rank
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendPrepare(rid, ts, rank uint64) {     @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendUnprepare
    (gcoord : loc) (rid : u64) (tsW : u64) (rank : u64) gid γ :
    let ts := uint.nat tsW in
    is_group_prepare_proposal γ gid ts 1%nat false -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendUnprepare #gcoord #rid #tsW #rank
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendUnprepare(rid, ts, rank uint64) {   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendQuery
    (gcoord : loc) (rid : u64) (ts : u64) (rank : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendQuery #gcoord #rid #ts #rank
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendQuery(rid, ts, rank uint64) {       @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendRefresh
    (gcoord : loc) (rid : u64) (ts : u64) (rank : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendRefresh #gcoord #rid #ts #rank
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendRefresh(rid, ts, rank uint64) {     @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendCommit
    (gcoord : loc) (rid : u64) (tsW : u64) (pwrsP : loc) q (pwrs : dbmap) gid γ :
    let ts := uint.nat tsW in
    safe_commit γ gid ts pwrs -∗
    is_gcoord gcoord gid γ -∗
    {{{ own_map pwrsP q pwrs }}}
      GroupCoordinator__SendCommit #gcoord #rid #tsW #pwrsP
    {{{ RET #(); own_map pwrsP q pwrs }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendCommit(rid, ts uint64, pwrs tulip.KVMap) { @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendAbort (gcoord : loc) (rid : u64) (tsW : u64) gid γ :
    let ts := uint.nat tsW in
    safe_abort γ ts -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendAbort #gcoord #rid #tsW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendAbort(rid, ts uint64) {             @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
