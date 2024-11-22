From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import prelude group_reader group_preparer.

(* Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. *)

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type GroupCoordinator struct {                                          @*)
  (*@     // Replica addresses. Read-only.                                    @*)
  (*@     rps     map[uint64]grove_ffi.Address                                @*)
  (*@     // Mutex protecting fields below.                                   @*)
  (*@     mu      *sync.Mutex                                                 @*)
  (*@     // Condition variable used to notify arrival of responses.          @*)
  (*@     cv      *sync.Cond                                                  @*)
  (*@     // Timestamp of the currently active transaction.                   @*)
  (*@     ts       uint64                                                     @*)
  (*@     // ID of the replica believed to be the leader of this group.       @*)
  (*@     leader   uint64                                                     @*)
  (*@     // Group reader.                                                    @*)
  (*@     grd      *GroupReader                                               @*)
  (*@     // Group preparer.                                                  @*)
  (*@     gpp      *GroupPreparer                                             @*)
  (*@     // IDs of the finalizing transactions. Using unit as range would suffice. @*)
  (*@     tsfinals map[uint64]bool                                            @*)
  (*@     // Connections to replicas.                                         @*)
  (*@     conns    map[uint64]grove_ffi.Connection                            @*)
  (*@ }                                                                       @*)
  Definition own_gcoord_ts gcoord ts : iProp Σ :=
    ∃ (tsW : u64),
      "HtsW" ∷ gcoord ↦[GroupCoordinator :: "ts"] #tsW ∗
      "%Hts" ∷ ⌜uint.nat tsW = ts⌝.

  Definition own_gcoord_greader gcoord ts γ : iProp Σ :=
    ∃ (grdP : loc),
      "HgrdP" ∷ gcoord ↦[GroupCoordinator :: "grd"] #grdP ∗
      "Hgrd"  ∷ own_greader grdP ts γ.

  Definition own_gcoord_gpreparer gcoord ts gid γ : iProp Σ :=
    ∃ (gppP : loc),
      "HgppP" ∷ gcoord ↦[GroupCoordinator :: "gpp"] #gppP ∗
      "Hgpp"  ∷ own_gpreparer gppP ts gid γ.

  Definition own_gcoord_finalizer gcoord (rids : gset u64) : iProp Σ :=
    ∃ (idxleader : u64) (tsfinalsP : loc) (tsfinals : gmap u64 bool),
      "Hleader"    ∷ gcoord ↦[GroupCoordinator :: "idxleader"] #idxleader ∗
      "HtsfinalsP" ∷ gcoord ↦[GroupCoordinator :: "tsfinals"] #tsfinalsP ∗
      "Htsfinals"  ∷ own_map tsfinalsP (DfracOwn 1) tsfinals ∗
      "%Hleader"   ∷ ⌜(uint.nat idxleader < size rids)⌝.

  Definition own_gcoord_core gcoord ts gid rids γ : iProp Σ :=
    "Hts"  ∷ own_gcoord_ts gcoord ts ∗
    "Hgrd" ∷ own_gcoord_greader gcoord ts γ ∗
    "Hgpp" ∷ own_gcoord_gpreparer gcoord ts gid γ ∗
    "Hgfl" ∷ own_gcoord_finalizer gcoord rids.

  Definition own_gcoord_comm gcoord (addrm : gmap u64 chan) : iProp Σ :=
    ∃ (connsP : loc) (conns : gmap u64 (chan * chan)),
      let connsV := fmap (λ x, connection_socket x.1 x.2) conns in
      "HconnsP" ∷ gcoord ↦[GroupCoordinator :: "conns"] #connsP ∗
      "Hconns"  ∷ map.own_map connsP (DfracOwn 1) (connsV, #()) ∗
      (* "#Htrmls" ∷ ([∗ map] x ∈ conns, is_terminal γ x.1) ∗ *)
      "%Haddrpeers" ∷ ⌜map_Forall (λ rid x, addrm !! rid = Some x.2) conns⌝.

  Definition own_gcoord_with_ts gcoord addrm ts gid γ : iProp Σ :=
    "Hgcoord" ∷ own_gcoord_core gcoord ts gid (dom addrm) γ ∗
    "Hcomm"   ∷ own_gcoord_comm gcoord addrm.

  Definition own_gcoord gcoord addrm gid γ : iProp Σ :=
    ∃ ts, "Hgcoord" ∷ own_gcoord_with_ts gcoord addrm ts gid γ.

  Definition is_gcoord_addrm gcoord (addrm : gmap u64 chan) : iProp Σ :=
    ∃ (addrmP : loc) (rpsP : Slice.t) (rps : list u64),
      "#HaddrmP"   ∷ readonly (gcoord ↦[GroupCoordinator :: "addrm"] #addrmP) ∗
      "#Haddrm"    ∷ own_map addrmP DfracDiscarded addrm ∗
      "#HrpsP"     ∷ readonly (gcoord ↦[GroupCoordinator :: "rps"] (to_val rpsP)) ∗
      "#Hrps"      ∷ readonly (own_slice_small rpsP uint64T (DfracOwn 1) rps) ∗
      "%Hdomaddrm" ∷ ⌜dom addrm = list_to_set rps⌝ ∗
      "%Hnodup"    ∷ ⌜NoDup rps⌝.

  Definition is_gcoord_with_addrm gcoord gid (addrm : gmap u64 chan) γ : iProp Σ :=
    ∃ (muP : loc) (cvP : loc),
      "#HmuP"   ∷ readonly (gcoord ↦[GroupCoordinator :: "mu"] #muP) ∗
      "#Hlock"  ∷ is_lock tulipNS #muP (own_gcoord gcoord addrm gid γ) ∗
      "#HcvP"   ∷ readonly (gcoord ↦[GroupCoordinator :: "cv"] #cvP) ∗
      "Hcv"     ∷ is_cond cvP #muP ∗
      "#Haddrm" ∷ is_gcoord_addrm gcoord addrm.

  Definition is_gcoord gcoord gid γ : iProp Σ :=
    ∃ addrm, "Hgcoord" ∷ is_gcoord_with_addrm gcoord gid addrm γ.

End repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__attachedWith (gcoord : loc) (tsW : u64) tscur rids gid γ :
    let ts := uint.nat tsW in
    {{{ own_gcoord_core gcoord tscur gid rids γ }}}
      GroupCoordinator__attachedWith #gcoord #tsW
    {{{ (ok : bool), RET #ok;
        if ok
        then own_gcoord_core gcoord ts gid rids γ
        else own_gcoord_core gcoord tscur gid rids γ
    }}}.
  Proof.
    iIntros (ts Φ) "Hgcoord HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) attachedWith(ts uint64) bool {          @*)
    (*@     return gcoord.ts == ts                                              @*)
    (*@ }                                                                       @*)
    iNamed "Hgcoord".
    rename tsW into tsargW. iNamed "Hts".
    wp_loadField.
    wp_pures.
    case_bool_decide as Htsarg.
    { iApply "HΦ". inv Htsarg. by iFrame "∗ # %". }
    { iApply "HΦ". by iFrame "∗ # %". }
  Qed.

  Theorem wp_GroupCoordinator__AttachedWith (gcoord : loc) (ts : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__AttachedWith #gcoord #ts
    {{{ (attached : bool), RET #attached; True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) AttachedWith(ts uint64) bool {          @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     b := gcoord.attachedWith(ts)                                        @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return b                                                            @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 2 iNamed "Hgcoord".
    wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
    iIntros (b) "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked". by destruct b; iFrame. }
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__ValueResponded gcoord (rid : u64) key gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__ValueResponded #gcoord #rid #(LitString key)
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) ValueResponded(rid uint64, key string) bool { @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     done := gcoord.grd.responded(rid, key)                              @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return done                                                         @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 3 iNamed "Hgcoord". iNamed "Hgrd".
    wp_loadField.
    wp_pures.
    wp_apply (wp_GroupReader__responded with "Hgrd").
    iIntros (responded) "Hgrd".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked". by iFrame "∗ # %". }
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__WaitUntilValueReady
    (gcoord : loc) (tsW : u64) (key : string) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__WaitUntilValueReady #gcoord #tsW #(LitString key)
    {{{ (value : dbval) (valid : bool), RET (dbval_to_val value, #valid); 
        if valid then fast_or_quorum_read γ key ts value else True
    }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) WaitUntilValueReady(ts uint64, key string) (tulip.Value, bool) { @*)
    (*@     var value tulip.Value                                               @*)
    (*@     var valid bool                                                      @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first done.
    iIntros (valueP) "HvalueP".
    wp_apply wp_ref_of_zero; first done.
    iIntros (validP) "HvalidP".

    (*@     gcoord.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    wp_pures.

    (*@     for {                                                               @*)
    (*@                                                                         @*)
    set P := (λ (cont : bool), ∃ (value : dbval) (valid : bool),
      "Hgcoord" ∷ own_gcoord gcoord addrm gid γ ∗
      "HvalueP" ∷ valueP ↦[boolT * (stringT * unitT)%ht] dbval_to_val value ∗
      "HvalidP" ∷ validP ↦[boolT] #valid ∗
      "Hlocked" ∷ locked #muP ∗
      "#Hread"  ∷ if (negb cont) && valid then fast_or_quorum_read γ key ts value else True)%I.
    wp_apply (wp_forBreak P with "[] [Hgcoord HvalueP HvalidP Hlocked]"); last first; first 1 last.
    { iFrame. by iExists None. }
    { clear Φ.

      (*@         if !gcoord.attachedWith(ts) {                                   @*)
      (*@             valid = false                                               @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      iDestruct"Hgcoord" as (tscur) "Hgcoord".
      do 2 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
      iIntros (attached) "Hgcoord".
      wp_pures.
      destruct attached; wp_pures; last first.
      { wp_store. iApply "HΦ". by iFrame. }

      (*@         v, ok := gcoord.grd.read(key)                                   @*)
      (*@         if ok {                                                         @*)
      (*@             value = v                                                   @*)
      (*@             valid = true                                                @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      iNamed "Hgcoord". iNamed "Hgrd".
      wp_loadField.
      wp_apply (wp_GroupReader__read with "Hgrd").
      iIntros (v ok) "[Hgrd #Hreadv]".
      wp_pures.
      destruct ok; wp_pures.
      { wp_apply (wp_StoreAt with "HvalueP").
        { by destruct v; auto. }
        iIntros "HvalueP".
        wp_store.
        iApply "HΦ".
        by iFrame "∗ #".
      }
    
      (*@         gcoord.cv.Wait()                                                @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply (wp_Cond__Wait with "[-HΦ HvalueP HvalidP]").
      { by iFrame "Hcv Hlock Hlocked ∗ # %". }
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    subst P. iNamed 1.

    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ HvalueP HvalidP]").
    { by iFrame "Hlock Hlocked Hgcoord". }

    (*@     return value, valid                                                 @*)
    (*@ }                                                                       @*)
    do 2 wp_load.
    wp_pures.
    iApply "HΦ".
    by destruct valid.
  Qed.

  Theorem wp_GroupCoordinator__SendRead
    (gcoord : loc) (rid : u64) (ts : u64) (key : string) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendRead #gcoord #rid #ts #(LitString key)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendRead(rid, ts uint64, key string) {  @*)
    (*@     gcoord.Send(rid, message.EncodeTxnRead(ts, key))                    @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__ReadSession 
    (gcoord : loc) (rid : u64) (ts : u64) (key : string) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__ReadSession #gcoord #rid #ts #(LitString key)
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) ReadSession(rid uint64, ts uint64, key string) { @*)
    (*@     for !gcoord.ValueResponded(rid, key) && gcoord.AttachedWith(ts) {   @*)
    (*@         gcoord.SendRead(rid, ts, key)                                   @*)
    (*@         primitive.Sleep(params.NS_RESEND_READ)                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_pures.
    wp_apply (wp_forBreak_cond (λ _, True)%I with "[] []"); last first; first 1 last.
    { done. }
    { clear Φ.
      iIntros (Φ) "!> _ HΦ".
      wp_apply (wp_GroupCoordinator__ValueResponded with "Hgcoord").
      iIntros (resped) "_".
      wp_pures.
      destruct resped; wp_pures.
      { by iApply "HΦ". }
      wp_apply (wp_GroupCoordinator__AttachedWith with "Hgcoord").
      iIntros (attached) "_".
      destruct attached; wp_pures; last first.
      { by iApply "HΦ". }
      wp_apply (wp_GroupCoordinator__SendRead with "Hgcoord").
      wp_apply wp_Sleep.
      wp_pures.
      by iApply "HΦ".
    }

    (*@     // Either replica @rid has already responded with its value, or the value @*)
    (*@     // for @key has already been determined. In either case, the corresponding @*)
    (*@     // read session could terminate.                                    @*)
    (*@ }                                                                       @*)
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__Read
    (gcoord : loc) (tsW : u64) (key : string) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Read #gcoord #tsW #(LitString key)
    {{{ (value : dbval) (ok : bool), RET (dbval_to_val value, #ok); 
        if ok then fast_or_quorum_read γ key ts value else True
    }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Read(ts uint64, key string) (tulip.Value, bool) { @*)
    (*@     // Spawn a session with each replica in the group.                  @*)
    (*@     for ridloop := range(gcoord.addrm) {                                  @*)
    (*@         rid := ridloop                                                  @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.ReadSession(rid, ts, key)                            @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iPoseProof "Hgcoord" as "Hgcoord'".
    do 2 iNamed "Hgcoord". iNamed "Haddrm".
    iRename "Hgcoord'" into "Hgcoord".
    wp_loadField.
    wp_apply (wp_MapIter_fold _ _ _ (λ _, True)%I with "Haddrm []").
    { done. }
    { clear Φ.
      iIntros (mx rid c Φ) "!> _ HΦ".
      wp_pures.
      wp_apply wp_fork.
      { by wp_apply (wp_GroupCoordinator__ReadSession with "Hgcoord"). }
      by iApply "HΦ".
    }
    iIntros "_".

    (*@     v, ok := gcoord.WaitUntilValueReady(ts, key)                        @*)
    (*@     return v, ok                                                        @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupCoordinator__WaitUntilValueReady with "Hgcoord").
    iIntros (v ok) "#Hread".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__NextPrepareAction
    (gcoord : loc) (rid : u64) (tsW : u64) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__NextPrepareAction #gcoord #rid #tsW
    {{{ (action : gppaction) (ok : bool), RET (#(gppaction_to_u64 action), #ok); 
        if ok then safe_gppaction γ ts gid action else True
    }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) NextPrepareAction(rid uint64, ts uint64) (uint64, bool) { @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 2 iNamed "Hgcoord".
    wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
    iIntros (ok) "Hgcoord".
    wp_pures.

    (*@     if !gcoord.attachedWith(ts) {                                       @*)
    (*@         gcoord.mu.Unlock()                                              @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct ok; wp_pures; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      (* [GPPFastPrepare] just a placeholder *)
      by iApply ("HΦ" $! GPPFastPrepare).
    }

    (*@     action := gcoord.gpp.action(rid)                                    @*)
    (*@                                                                         @*)
    iNamed "Hgcoord". iNamed "Hgpp".
    wp_loadField.
    wp_apply (wp_GroupPreparer__action with "Hgpp").
    iIntros (action) "[Hgpp #Hsafea]".
    wp_pures.

    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }

    (*@     return action, true                                                 @*)
    (*@ }                                                                       @*)
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__WaitUntilPrepareDone
    (gcoord : loc) (tsW : u64) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__WaitUntilPrepareDone #gcoord #tsW
    {{{ (tphase : txnphase) (valid : bool), RET (#(txnphase_to_u64 tphase), #valid); 
        if valid then safe_txnphase γ ts gid tphase else True
    }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) WaitUntilPrepareDone(ts uint64) (uint64, bool) { @*)
    (*@     var phase uint64                                                    @*)
    (*@     var valid bool                                                      @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first done.
    iIntros (phaseP) "HphaseP".
    wp_apply wp_ref_of_zero; first done.
    iIntros (validP) "HvalidP".

    (*@     gcoord.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    wp_pures.

    (*@     for {                                                               @*)
    (*@                                                                         @*)
    set P := (λ (cont : bool), ∃ (pphase : gppphase) (valid : bool),
      "Hgcoord" ∷ own_gcoord gcoord addrm gid γ ∗
      "HphaseP" ∷ phaseP ↦[uint64T] #(gppphase_to_u64 pphase) ∗
      "HvalidP" ∷ validP ↦[boolT] #valid ∗
      "Hlocked" ∷ locked #muP ∗
      "#Hsafep" ∷ (if (negb cont) && valid
                   then safe_gpreparer_phase γ ts gid pphase ∗ ⌜gpp_ready pphase⌝
                   else True))%I.
    wp_apply (wp_forBreak P with "[] [Hgcoord HphaseP HvalidP Hlocked]"); last first; first 1 last.
    { iFrame. by iExists GPPValidating. }
    { clear Φ.

      (*@         if !gcoord.attachedWith(ts) {                                   @*)
      (*@             valid = false                                               @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      iDestruct"Hgcoord" as (tscur) "Hgcoord".
      do 2 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
      iIntros (attached) "Hgcoord".
      wp_pures.
      destruct attached; wp_pures; last first.
      { wp_store. iApply "HΦ". by iFrame. }

      (*@         ready := gcoord.gpp.ready()                                     @*)
      (*@         if ready {                                                      @*)
      (*@             phase = gcoord.gpp.getPhase()                               @*)
      (*@             valid = true                                                @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      iNamed "Hgcoord". do 2 iNamed "Hgpp".
      wp_loadField.
      wp_apply (wp_GroupPreparer__ready_external with "Hgpp").
      iIntros "Hgpp".
      case_bool_decide; wp_pures.
      { wp_loadField.
        wp_apply (wp_GroupPreparer__getPhase with "Hgpp").
        iIntros "[Hgpp #Hsafegpp]".
        do 2 wp_store.
        iApply "HΦ".
        by iFrame "∗ # %".
      }

      (*@         gcoord.cv.Wait()                                                @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply (wp_Cond__Wait with "[-HΦ HphaseP HvalidP]").
      { by iFrame "Hcv Hlock Hlocked ∗ # %". }
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    subst P. iNamed 1. simpl.

    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ HphaseP HvalidP]").
    { by iFrame "Hlock Hlocked Hgcoord". }

    (*@     if !valid {                                                         @*)
    (*@         // TXN_PREPARED here is just a placeholder.                     @*)
    (*@         return tulip.TXN_PREPARED, false                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_load. wp_pures.
    destruct valid; wp_pures; last first.
    { by iApply ("HΦ" $! TxnPrepared). }
    iDestruct "Hsafep" as "[Hsafep %Hready]".

    (*@     if phase == GPP_COMMITTED {                                         @*)
    (*@         return tulip.TXN_COMMITTED, true                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_load. wp_pures.
    case_bool_decide; wp_pures.
    { iApply ("HΦ" $! TxnCommitted). by destruct pphase. }

    (*@     if phase == GPP_ABORTED {                                           @*)
    (*@         return tulip.TXN_ABORTED, true                                  @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_load. wp_pures.
    case_bool_decide; wp_pures.
    { iApply ("HΦ" $! TxnAborted). by destruct pphase. }

    (*@     return tulip.TXN_PREPARED, true                                     @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! TxnPrepared). by destruct pphase.
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
    (gcoord : loc) (rid : u64) (tsW : u64) (pwrsP : loc) gid γ :
    let ts := uint.nat tsW in
    (∃ wrs, is_txn_committed γ ts wrs) -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendCommit #gcoord #rid #tsW #pwrsP
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendCommit(rid, ts uint64, pwrs tulip.KVMap) { @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__SendAbort (gcoord : loc) (rid : u64) (tsW : u64) gid γ :
    let ts := uint.nat tsW in
    is_txn_aborted γ ts -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__SendAbort #gcoord #rid #tsW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *GroupCoordinator) SendAbort(rid, ts uint64) {             @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_GroupCoordinator__PrepareSession
    (gcoord : loc) (rid : u64) (tsW : u64) (ptgsP : Slice.t) (pwrsP : loc) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__PrepareSession #gcoord #rid #tsW (to_val ptgsP) #pwrsP
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec. wp_pures.

    (*@ func (gcoord *GroupCoordinator) PrepareSession(rid uint64, ts uint64, ptgs []uint64, pwrs map[string]tulip.Value) { @*)
    (*@     for {                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I with "[] []"); last first; first 1 last.
    { done. }
    { clear Φ.

      (*@         act, attached := gcoord.NextPrepareAction(rid, ts)              @*)
      (*@                                                                         @*)
      iIntros (Φ) "!> _ HΦ".
      wp_apply (wp_GroupCoordinator__NextPrepareAction with "Hgcoord").
      iIntros (action ok) "#Hsafea".
      wp_pures.

      (*@         if !attached {                                                  @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      destruct ok; wp_pures; last by iApply "HΦ".

      (*@         if act == GPP_FAST_PREPARE {                                    @*)
      (*@             gcoord.SendFastPrepare(rid, ts, pwrs, ptgs)                 @*)
      (*@         } else if act == GPP_VALIDATE {                                 @*)
      (*@             gcoord.SendValidate(rid, ts, 1, pwrs, ptgs)                 @*)
      (*@         } else if act == GPP_PREPARE {                                  @*)
      (*@             gcoord.SendPrepare(rid, ts, 1)                              @*)
      (*@         } else if act == GPP_UNPREPARE {                                @*)
      (*@             gcoord.SendUnprepare(rid, ts, 1)                            @*)
      (*@         } else if act == GPP_QUERY {                                    @*)
      (*@             gcoord.SendQuery(rid, ts, 1)                                @*)
      (*@         } else if act == GPP_REFRESH {                                  @*)
      (*@             // Keep sending keep-alive message until the transaction terminated. @*)
      (*@             gcoord.SendRefresh(rid, ts, 1)                              @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      (*@         if act == GPP_REFRESH {                                         @*)
      (*@             primitive.Sleep(params.NS_SEND_REFRESH)                     @*)
      (*@         } else {                                                        @*)
      (*@             // The optimal time to sleep is the time required to arrive at a @*)
      (*@             // prepare decision. Waking up too frequently means sending @*)
      (*@             // unnecessary messages, too infrequently means longer latency when @*)
      (*@             // messages are lost.                                       @*)
      (*@             //                                                          @*)
      (*@             // This might not be optimal for slow-path prepare. Consider @*)
      (*@             // optimize this with CV wait and timeout.                  @*)
      (*@             primitive.Sleep(params.NS_RESEND_PREPARE)                   @*)
      (*@         }                                                               @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      case_bool_decide as Hfp; wp_pures.
      { wp_apply (wp_GroupCoordinator__SendFastPrepare with "Hgcoord").
        wp_pures.
        rewrite Hfp /=.
        case_bool_decide; first done.
        wp_apply wp_Sleep. wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hvd; wp_pures.
      { wp_apply (wp_GroupCoordinator__SendValidate with "Hgcoord").
        wp_pures.
        rewrite Hvd /=.
        case_bool_decide; first done.
        wp_apply wp_Sleep. wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hprep; wp_pures.
      { inv Hprep. destruct action; try done. simpl.
        wp_apply (wp_GroupCoordinator__SendPrepare with "Hsafea Hgcoord").
        wp_pures.
        wp_apply wp_Sleep. wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hunprep; wp_pures.
      { inv Hunprep. destruct action; try done. simpl.
        wp_apply (wp_GroupCoordinator__SendUnprepare with "Hsafea Hgcoord").
        wp_pures.
        wp_apply wp_Sleep. wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hqr; wp_pures.
      { wp_apply (wp_GroupCoordinator__SendQuery with "Hgcoord").
        wp_pures.
        rewrite Hqr /=.
        case_bool_decide; first done.
        wp_apply wp_Sleep. wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hrf; wp_pures.
      { wp_apply (wp_GroupCoordinator__SendRefresh with "Hgcoord").
        wp_pures.
        rewrite Hrf /=.
        case_bool_decide; last done.
        wp_apply wp_Sleep. wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide; first done.
      wp_apply wp_Sleep. wp_pures.
      by iApply "HΦ".

      (*@     // The coordinator is no longer associated with @ts, this could happen only @*)
      (*@     // after the prepare decision for @ts on @rid is made. Hence, this session @*)
      (*@     // can terminate.                                                   @*)
      (*@ }                                                                       @*)
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__Prepare
    (gcoord : loc) (tsW : u64) (ptgsP : Slice.t) (pwrsP : loc) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Prepare #gcoord #tsW (to_val ptgsP) #pwrsP
    {{{ (phase : txnphase) (valid : bool), RET (#(txnphase_to_u64 phase), #valid); 
        if valid then safe_txnphase γ ts gid phase else True
    }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Prepare(ts uint64, ptgs []uint64, pwrs tulip.KVMap) (uint64, bool) { @*)
    (*@     // Spawn a prepare session with each replica.                       @*)
    (*@     for ridloop := range(gcoord.addrm) {                                  @*)
    (*@         rid := ridloop                                                  @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.PrepareSession(rid, ts, ptgs, pwrs)                  @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iPoseProof "Hgcoord" as "Hgcoord'".
    do 2 iNamed "Hgcoord". iNamed "Haddrm".
    iRename "Hgcoord'" into "Hgcoord".
    wp_loadField.
    wp_apply (wp_MapIter_fold _ _ _ (λ _, True)%I with "Haddrm []").
    { done. }
    { clear Φ.
      iIntros (mx rid c Φ) "!> _ HΦ".
      wp_pures.
      wp_apply wp_fork.
      { by wp_apply (wp_GroupCoordinator__PrepareSession with "Hgcoord"). }
      by iApply "HΦ".
    }
    iIntros "_".

    (*@     st, valid := gcoord.WaitUntilPrepareDone(ts)                        @*)
    (*@     return st, valid                                                    @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupCoordinator__WaitUntilPrepareDone with "Hgcoord").
    iIntros (phase valid) "#Hsafep".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__GetLeader (gcoord : loc) gid addrm γ :
    is_gcoord_with_addrm gcoord gid addrm γ -∗
    {{{ True }}}
      GroupCoordinator__GetLeader #gcoord
    {{{ (leader : u64), RET #leader; ⌜leader ∈ dom addrm⌝ }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) GetLeader() uint64 {                    @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     leader := gcoord.leader                                             @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return leader                                                       @*)
    (*@ }                                                                       @*)
    iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 3 iNamed "Hgcoord". iNamed "Hgfl".
    do 2 wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked Hts Hgrd Hgpp Hcomm ∗ %". }
    wp_pures.
    iNamed "Haddrm".
    wp_loadField.
    iMod (readonly_load with "Hrps") as (q) "Hrpsro".
    assert (is_Some (rps !! uint.nat idxleader)) as [leader Hlead].
    { apply lookup_lt_is_Some.
      assert (length rps = size (dom addrm)); last word.
      by rewrite Hdomaddrm size_list_to_set.
    }
    wp_apply (wp_SliceGet with "[$Hrpsro]").
    { done. }
    iIntros "_".
    iApply "HΦ".
    iPureIntro.
    apply elem_of_list_lookup_2 in Hlead.
    by rewrite Hdomaddrm elem_of_list_to_set.
  Qed.

  Theorem wp_GroupCoordinator__ChangeLeader (gcoord : loc) gid addrm γ :
    is_gcoord_with_addrm gcoord gid addrm γ -∗
    {{{ True }}}
      GroupCoordinator__ChangeLeader #gcoord
    {{{ (leader : u64), RET #leader; ⌜leader ∈ dom addrm⌝ }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) ChangeLeader() uint64 {                 @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     leader := (gcoord.leader + 1) % uint64(len(gcoord.addrm))             @*)
    (*@     gcoord.leader = leader                                              @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return leader                                                       @*)
    (*@ }                                                                       @*)
    iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 3 iNamed "Hgcoord". iNamed "Hgfl".
    iNamed "Haddrm".
    do 2 wp_loadField.
    wp_apply wp_slice_len.
    wp_storeField.
    iMod (readonly_load with "Hrps") as (q) "Hrpsro".
    iDestruct (own_slice_small_sz with "Hrpsro") as %Hlenrps.
    wp_loadField.
    set idxleader' := word.modu _ _.
    assert (Hltrps : (uint.nat idxleader' < length rps)%nat).
    { assert (size (dom addrm) = length rps) as Hszaddrm.
      { by rewrite Hdomaddrm size_list_to_set. }
      rewrite word.unsigned_modu_nowrap; [word | lia].
    }
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hrpsro]").
    { iFrame "Hlock Hlocked Hts Hgrd Hgpp Hcomm ∗ %".
      iPureIntro.
      rewrite Hdomaddrm size_list_to_set; [lia | done].
    }
    wp_pures.
    wp_loadField.
    assert (is_Some (rps !! uint.nat idxleader')) as [leader Hlead].
    { by apply lookup_lt_is_Some. }
    wp_apply (wp_SliceGet with "[$Hrpsro]").
    { done. }
    iIntros "_".
    iApply "HΦ".
    apply elem_of_list_lookup_2 in Hlead.
    by rewrite Hdomaddrm elem_of_list_to_set.
  Qed.

  Theorem wp_GroupCoordinator__processFinalizationResult
    (gcoord : loc) (ts : u64) (res : u64) rids :
    {{{ own_gcoord_finalizer gcoord rids }}}
      GroupCoordinator__processFinalizationResult #gcoord #ts #res
    {{{ RET #(); own_gcoord_finalizer gcoord rids }}}.
  Proof.
    iIntros (Φ) "Hgcoord HΦ".
    wp_rec. wp_pures.

    (*@ func (gcoord *GroupCoordinator) processFinalizationResult(ts uint64, res uint64) { @*)
    (*@     if res == tulip.REPLICA_WRONG_LEADER {                              @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@     delete(gcoord.tsfinals, ts)                                         @*)
    (*@ }                                                                       @*)
    case_bool_decide as Hwrong; wp_pures.
    { by iApply "HΦ". }
    iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_MapDelete with "Htsfinals").
    iIntros "Htsfinals".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ %".
  Qed.

  Theorem wp_GroupCoordinator__Finalized (gcoord : loc) (tsW : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Finalized #gcoord #tsW
    {{{ (finalized : bool), RET #finalized; True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Finalized(ts uint64) bool {             @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     _, ok := gcoord.tsfinals[ts]                                        @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return !ok                                                          @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 3 iNamed "Hgcoord". iNamed "Hgfl".
    wp_loadField.
    wp_apply (wp_MapGet with "Htsfinals").
    iIntros (v ok) "[%Hok Htsfinals]".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked Hts Hgrd Hgpp Hcomm ∗ %". }
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__RegisterFinalization (gcoord : loc) (tsW : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__RegisterFinalization #gcoord #tsW
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) RegisterFinalization(ts uint64) {       @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     gcoord.tsfinals[ts] = true                                          @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 3 iNamed "Hgcoord". iNamed "Hgfl".
    wp_loadField.
    wp_apply (wp_MapInsert with "Htsfinals"); first done.
    iIntros "Htsfinals".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked Hts Hgrd Hgpp Hcomm ∗ %". }
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__Commit (gcoord : loc) (tsW : u64) (pwrsP : loc) gid γ :
    let ts := uint.nat tsW in
    (∃ wrs, is_txn_committed γ ts wrs) -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Commit #gcoord #tsW #pwrsP
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts) "#Hcmted #Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Commit(ts uint64, pwrs tulip.KVMap) {   @*)
    (*@     gcoord.RegisterFinalization(ts)                                     @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupCoordinator__RegisterFinalization with "Hgcoord").
    iNamed "Hgcoord".
    wp_apply (wp_GroupCoordinator__GetLeader with "Hgcoord").
    iIntros (leader Hleader).
    wp_apply wp_ref_to; first by auto.
    iIntros (leaderP) "HleaderP".
    wp_pures.

    (*@     var leader = gcoord.GetLeader()                                     @*)
    (*@     for !gcoord.Finalized(ts) {                                         @*)
    (*@         gcoord.SendCommit(leader, ts, pwrs)                             @*)
    (*@         primitive.Sleep(params.NS_RESEND_COMMIT)                        @*)
    (*@         // Retry with different leaders until success.                  @*)
    (*@         leader = gcoord.ChangeLeader()                                  @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    set P := (λ _ : bool, ∃ leader' : u64, leaderP ↦[uint64T] #leader' ∗ ⌜leader' ∈ dom addrm⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [$HleaderP]"); last first; first 1 last.
    { done. }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      wp_apply (wp_GroupCoordinator__Finalized with "[]").
      { iFrame "Hgcoord". }
      iIntros (finalized) "_".
      wp_pures.
      destruct finalized; wp_pures.
      { by iApply "HΦ". }
      iDestruct "HP" as (leader') "[HleaderP %Hin]".
      wp_load.
      wp_apply (wp_GroupCoordinator__SendCommit with "Hcmted").
      { iFrame "Hgcoord". }
      wp_apply wp_Sleep.
      wp_apply (wp_GroupCoordinator__ChangeLeader).
      { iFrame "Hgcoord". }
      iIntros (leadernew Hleadernew).
      wp_store.
      iApply "HΦ".
      by iFrame.
    }
    iIntros "_".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__Abort (gcoord : loc) (tsW : u64) gid γ :
    let ts := uint.nat tsW in
    is_txn_aborted γ ts -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Abort #gcoord #tsW
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts) "#Habted #Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Abort(ts uint64) {                      @*)
    (*@     gcoord.RegisterFinalization(ts)                                     @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupCoordinator__RegisterFinalization with "Hgcoord").
    iNamed "Hgcoord".
    wp_apply (wp_GroupCoordinator__GetLeader with "Hgcoord").
    iIntros (leader Hleader).
    wp_apply wp_ref_to; first by auto.
    iIntros (leaderP) "HleaderP".
    wp_pures.

    (*@     var leader = gcoord.GetLeader()                                     @*)
    (*@     for !gcoord.Finalized(ts) {                                         @*)
    (*@         gcoord.SendAbort(leader, ts)                                    @*)
    (*@         primitive.Sleep(params.NS_RESEND_ABORT)                         @*)
    (*@         // Retry with different leaders until success.                  @*)
    (*@         leader = gcoord.ChangeLeader()                                  @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    set P := (λ _ : bool, ∃ leader' : u64, leaderP ↦[uint64T] #leader' ∗ ⌜leader' ∈ dom addrm⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [$HleaderP]"); last first; first 1 last.
    { done. }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      wp_apply (wp_GroupCoordinator__Finalized with "[]").
      { iFrame "Hgcoord". }
      iIntros (finalized) "_".
      wp_pures.
      destruct finalized; wp_pures.
      { by iApply "HΦ". }
      iDestruct "HP" as (leader') "[HleaderP %Hin]".
      wp_load.
      wp_apply (wp_GroupCoordinator__SendAbort with "Habted").
      { iFrame "Hgcoord". }
      wp_apply wp_Sleep.
      wp_apply (wp_GroupCoordinator__ChangeLeader).
      { iFrame "Hgcoord". }
      iIntros (leadernew Hleadernew).
      wp_store.
      iApply "HΦ".
      by iFrame.
    }
    iIntros "_".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
