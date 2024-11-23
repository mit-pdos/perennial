From Perennial.program_proof.tulip.invariance Require Import
  read commit abort cancel linearize preprepare unprepare prepare.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import prelude group_coordinator.
From Perennial.goose_lang.trusted.github_com.mit_pdos.tulip Require Import trusted_proph.

Section res.
  Context `{!heapGS Σ}.

  Definition txnmap_auth (τ : gname) (m : dbmap) : iProp Σ.
  Admitted.

  Definition txnmap_ptsto (τ : gname) (k : dbkey) (v : dbval) : iProp Σ.
  Admitted.

  Definition txnmap_ptstos (τ : gname) (m : dbmap) : iProp Σ :=
    [∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v.

  Lemma txnmap_alloc m :
    ⊢ |==> ∃ τ, txnmap_auth τ m ∗ ([∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v).
  Admitted.

  Lemma txnmap_lookup τ m k v :
    txnmap_auth τ m -∗
    txnmap_ptsto τ k v -∗
    ⌜m !! k = Some v⌝.
  Admitted.

  Lemma txnmap_update {τ m k v1} v2 :
    txnmap_auth τ m -∗
    txnmap_ptsto τ k v1 ==∗
    txnmap_auth τ (<[k := v2]> m) ∗ txnmap_ptsto τ k v2.
  Admitted.

  Lemma txnmap_subseteq τ m1 m2 :
    txnmap_auth τ m1 -∗
    txnmap_ptstos τ m2 -∗
    ⌜m2 ⊆ m1⌝.
  Admitted.

  Definition local_gid_token (α : gname) (gid : u64) : iProp Σ.
  Admitted.

  Lemma local_gid_tokens_alloc (gids : gset u64) :
    ⊢ |==> ∃ α, [∗ set] gid ∈ gids, local_gid_token α gid.
  Admitted.

  Lemma local_gid_token_ne (α : gname) (gid1 gid2 : u64) :
    local_gid_token α gid1 -∗
    local_gid_token α gid2 -∗
    ⌜gid2 ≠ gid1⌝.
  Admitted.

End res.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type Txn struct {                                                       @*)
  (*@     // Timestamp of this transaction.                                   @*)
  (*@     ts      uint64                                                      @*)
  (*@     // Buffered write set.                                              @*)
  (*@     wrs     map[uint64]map[string]tulip.Value                           @*)
  (*@     // Participant group of this transaction. Initialized in prepare time. @*)
  (*@     ptgs    []uint64                                                    @*)
  (*@     // Group coordinators for performing reads, prepare, abort, and commit. @*)
  (*@     gcoords map[uint64]*gcoord.GroupCoordinator                         @*)
  (*@     // Global prophecy variable (for verification purpose).             @*)
  (*@     proph   primitive.ProphId                                           @*)
  (*@ }                                                                       @*)
  Definition txn_wrs (wrsP : loc) q (wrs : dbmap) : iProp Σ :=
    ∃ (pwrsmP : gmap u64 loc) (pwrsm : gmap u64 dbmap),
      "HpwrsmP"  ∷ own_map wrsP (DfracOwn 1) pwrsmP ∗
      "Hpwrsm"   ∷ ([∗ map] p; m ∈ pwrsmP; pwrsm, own_map p q m) ∗
      "%Hwrsg"   ∷ ⌜map_Forall (λ g m, m = wrs_group g wrs) pwrsm⌝ ∗
      "%Hdomwrs" ∷ ⌜dom pwrsmP = gids_all⌝.

  Definition own_txn_wrs txn q (wrs : dbmap) : iProp Σ :=
    ∃ (wrsP : loc) (wrspP : loc),
      "HwrsP"  ∷ txn ↦[Txn :: "wrs"] #wrsP ∗
      "Hwrs"   ∷ txn_wrs wrsP q wrs ∗
      "HwrspP" ∷ txn ↦[Txn :: "wrsp"] #wrspP ∗
      "Hwrsp"  ∷ own_map wrspP (DfracOwn 1) wrs.

  Definition own_txn_ptgs txn (ptgs : list u64) : iProp Σ :=
    ∃ (ptgsS : Slice.t),
      "HptgsS" ∷ txn ↦[Txn :: "ptgs"] (to_val ptgsS) ∗
      "Hptgs"  ∷ own_slice ptgsS uint64T (DfracOwn 1) ptgs ∗
      "%Hnd"   ∷ ⌜NoDup ptgs⌝.

  Definition own_txn_ts txn (tid : nat) : iProp Σ :=
    ∃ (tsW : u64),
      "HtsW"     ∷ txn ↦[Txn :: "ts"] #tsW ∗
      "%Htsword" ∷ ⌜uint.nat tsW = tid⌝.

  Definition own_txn_gcoords txn γ : iProp Σ :=
    ∃ (gcoordsP : loc) (gcoords : gmap u64 loc),
      "HgcoordsP"    ∷ txn ↦[Txn :: "gcoords"] #gcoordsP ∗
      "Hgcoords"     ∷ own_map gcoordsP (DfracOwn 1) gcoords ∗
      "#Hgcoordsabs" ∷ ([∗ map] gid ↦ gcoord ∈ gcoords, is_gcoord gcoord gid γ) ∗
      "%Hdomgcoords" ∷ ⌜dom gcoords = gids_all⌝.

  Definition own_txn_internal txn tid γ : iProp Σ :=
    ∃ (proph : proph_id),
      "Hts"      ∷ own_txn_ts txn tid ∗
      "Hwrs"     ∷ own_txn_wrs txn (DfracOwn 1) ∅ ∗
      "Hgcoords" ∷ own_txn_gcoords txn γ ∗
      "Hptgs"    ∷ own_txn_ptgs txn [] ∗
      "HprophP"  ∷ txn ↦[Txn :: "proph"] #proph ∗
      "#Hinv"    ∷ know_tulip_inv_with_proph γ proph.

  Definition own_txn_uninit txn γ : iProp Σ :=
    ∃ tid, "Htxn" ∷ own_txn_internal txn tid γ.

  Definition own_txn_init txn tid γ : iProp Σ :=
    "Htxn"  ∷ own_txn_internal txn tid γ ∗
    "%Hvts" ∷ ⌜valid_ts tid⌝.

  Definition own_txn txn tid rds γ τ : iProp Σ :=
    ∃ (proph : proph_id) wrs,
      "Htxn"     ∷ own_txn_ts txn tid ∗
      "Hwrs"     ∷ own_txn_wrs txn (DfracOwn 1) wrs ∗
      "Hgcoords" ∷ own_txn_gcoords txn γ ∗
      "Hptgs"    ∷ own_txn_ptgs txn [] ∗
      (* diff from [own_txn_init] *)
      "Htxnmap"  ∷ txnmap_auth τ (wrs ∪ rds) ∗
      "HprophP"  ∷ txn ↦[Txn :: "proph"] #proph ∗
      "#Hinv"    ∷ know_tulip_inv_with_proph γ proph ∗
      (* diff from [own_txn_init] *)
      "#Hlnrz"   ∷ ([∗ map] key ↦ value ∈ rds, is_lnrz_hist_at γ key (pred tid) value) ∗
      "%Hdomr"   ∷ ⌜dom rds ⊆ keys_all⌝ ∗
      (* diff from [own_txn_init] *)
      "%Hincl"   ∷ ⌜dom wrs ⊆ dom rds⌝ ∗
      "%Hvts"    ∷ ⌜valid_ts tid⌝ ∗
      (* diff from [own_txn_init] *)
      "%Hvwrs"   ∷ ⌜valid_wrs wrs⌝.

    Definition own_txn_stable txn tid rds wrs γ τ : iProp Σ :=
    ∃ (proph : proph_id),
      "Htxn"     ∷ own_txn_ts txn tid ∗
      (* diff from [own_txn] *)
      "Hwrs"     ∷ own_txn_wrs txn DfracDiscarded wrs ∗
      "Hgcoords" ∷ own_txn_gcoords txn γ ∗
      "Hptgs"    ∷ own_txn_ptgs txn [] ∗
      "Htxnmap"  ∷ txnmap_auth τ (wrs ∪ rds) ∗
      "HprophP"  ∷ txn ↦[Txn :: "proph"] #proph ∗
      "#Hinv"    ∷ know_tulip_inv_with_proph γ proph ∗
      "#Hlnrz"   ∷ ([∗ map] key ↦ value ∈ rds, is_lnrz_hist_at γ key (pred tid) value) ∗
      "%Hdomr"   ∷ ⌜dom rds ⊆ keys_all⌝ ∗
      (* diff from [own_txn] and [wrs] is exposed *)
      "#Htxnwrs" ∷ is_txn_wrs γ tid wrs ∗
      "%Hincl"   ∷ ⌜dom wrs ⊆ dom rds⌝ ∗
      "%Hvts"    ∷ ⌜valid_ts tid⌝ ∗
      "%Hvwrs"   ∷ ⌜valid_wrs wrs⌝.

  Definition own_txn_prepared txn tid rds wrs γ τ : iProp Σ :=
    ∃ (proph : proph_id) ptgs,
      "Htxn"     ∷ own_txn_ts txn tid ∗
      "Hwrs"     ∷ own_txn_wrs txn DfracDiscarded wrs ∗
      "Hgcoords" ∷ own_txn_gcoords txn γ ∗
      (* diff from [own_txn_stable] *)
      "Hptgs"    ∷ own_txn_ptgs txn ptgs ∗
      "Htxnmap"  ∷ txnmap_auth τ (wrs ∪ rds) ∗
      "HprophP"  ∷ txn ↦[Txn :: "proph"] #proph ∗
      "#Hinv"    ∷ know_tulip_inv_with_proph γ proph ∗
      "#Hlnrz"   ∷ ([∗ map] key ↦ value ∈ rds, is_lnrz_hist_at γ key (pred tid) value) ∗
      "#Htxnwrs" ∷ is_txn_wrs γ tid wrs ∗
      "%Hdomr"   ∷ ⌜dom rds ⊆ keys_all⌝ ∗
      "%Hincl"   ∷ ⌜dom wrs ⊆ dom rds⌝ ∗
      "%Hvts"    ∷ ⌜valid_ts tid⌝ ∗
      "%Hvwrs"   ∷ ⌜valid_wrs wrs⌝ ∗
      (* diff from [own_txn_stable] *)
      "%Hptgs"   ∷ ⌜list_to_set ptgs = ptgroups (dom wrs)⌝.

End repr.

Section proph.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Lemma wp_ResolveRead p (tid : u64) (key : string) (ts : nat) :
    ⊢
    {{{ ⌜uint.nat tid = ts⌝ }}}
    <<< ∀∀ acs, own_txn_proph p acs >>>
      ResolveRead #p #tid #(LitString key) @ ∅
    <<< ∃ acs', ⌜acs = ActRead ts key :: acs'⌝ ∗ own_txn_proph p acs' >>>
    {{{ RET #(); True }}}.
  Admitted.

  Lemma wp_ResolveAbort p (tid : u64) (ts : nat) :
    ⊢
    {{{ ⌜uint.nat tid = ts⌝ }}}
    <<< ∀∀ acs, own_txn_proph p acs >>>
      ResolveAbort #p #tid @ ∅
    <<< ∃ acs', ⌜acs = ActAbort ts :: acs'⌝ ∗ own_txn_proph p acs' >>>
    {{{ RET #(); True }}}.
  Admitted.

  Lemma wp_ResolveCommit
    p (tid : u64) (ts : nat) (wrsP : loc) q (wrs : dbmap) :
    ⊢
    {{{ ⌜uint.nat tid = ts⌝ ∗ own_map wrsP q wrs }}}
    <<< ∀∀ acs, own_txn_proph p acs >>>
      ResolveCommit #p #tid #wrsP @ ∅
    <<< ∃ acs', ⌜acs = ActCommit ts wrs :: acs'⌝ ∗ own_txn_proph p acs' >>>
    {{{ RET #(); own_map wrsP q wrs }}}.
  Admitted.

End proph.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_KeyToGroup (key : string) :
    {{{ True }}}
      KeyToGroup #(LitString key)
    {{{ (gid : u64), RET #gid; ⌜key_to_group key = gid⌝ }}}.
  Proof.
    (*@ func KeyToGroup(key string) uint64 {                                    @*)
    (*@     // TODO                                                             @*)
    (*@     return 0                                                            @*)
    (*@ }                                                                       @*)
  Admitted.

    Theorem wp_Txn__getwrs (txn : loc) (key : string) q wrs :
    {{{ own_txn_wrs txn q wrs }}}
      Txn__getwrs #txn #(LitString key)
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok);
        own_txn_wrs txn q wrs ∗ ⌜wrs !! key = if ok then Some v else None⌝
    }}}.
  Proof.
    iIntros (Φ) "Hwrs HΦ".
    wp_rec.

    (*@ func (txn *Txn) getwrs(key string) (Value, bool) {                      @*)
    (*@     gid := KeyToGroup(key)                                              @*)
    (*@     pwrs := txn.wrs[gid]                                                @*)
    (*@                                                                         @*)
    wp_apply wp_KeyToGroup.
    iIntros (gid Hgid).
    do 2 iNamed "Hwrs".
    wp_loadField.
    wp_apply (wp_MapGet with "HpwrsmP").
    iIntros (pwrsP ok) "[%Hget HpwrsmP]".
    destruct ok; last first.
    { apply map_get_false in Hget as [Hget _].
      rewrite -not_elem_of_dom Hdomwrs -Hgid in Hget.
      by pose proof (elem_of_key_to_group key).
    }
    apply map_get_true in Hget.
    iAssert (⌜is_Some (pwrsm !! gid)⌝)%I as %[pwrs Hpwrs].
    { iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom.
      iPureIntro.
      by rewrite -elem_of_dom -Hdom elem_of_dom.
    }
    iDestruct (big_sepM2_lookup_acc with "Hpwrsm") as "[Hpwrs HpwrsmC]"; [done | done |].

    (*@     v, ok := pwrs[key]                                                  @*)
    (*@     return v, ok                                                        @*)
    (*@ }                                                                       @*)
    wp_apply (wp_MapGet with "Hpwrs").
    iIntros (v ok) "[%Hv Hpwrs]".
    wp_pures.
    iApply "HΦ".
    iDestruct ("HpwrsmC" with "Hpwrs") as "Hpwrsm".
    iFrame "∗ # %".
    iPureIntro.
    specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
    rewrite Hwrsg in Hv.
    destruct ok.
    - apply map_get_true in Hv.
      rewrite lookup_wrs_group_Some in Hv.
      by destruct Hv as [Hv _].
    - apply map_get_false in Hv as [Hv _].
      rewrite lookup_wrs_group_None in Hv.
      by destruct Hv.
  Qed.

  Theorem wp_Txn__setwrs (txn : loc) (key : string) (value : dbval) wrs :
    {{{ own_txn_wrs txn (DfracOwn 1) wrs }}}
      Txn__setwrs #txn #(LitString key) (dbval_to_val value)
    {{{ RET #(); own_txn_wrs txn (DfracOwn 1) (<[key := value]> wrs) }}}.
  Proof.
    iIntros (Φ) "Hwrs HΦ".
    wp_rec.

    (*@ func (txn *Txn) setwrs(key string, value Value) {                       @*)
    (*@     gid := KeyToGroup(key)                                              @*)
    (*@     pwrs := txn.wrs[gid]                                                @*)
    (*@                                                                         @*)
    wp_apply wp_KeyToGroup.
    iIntros (gid Hgid).
    do 2 iNamed "Hwrs".
    wp_loadField.
    wp_apply (wp_MapGet with "HpwrsmP").
    iIntros (pwrsP ok) "[%Hget HpwrsmP]".
    destruct ok; last first.
    { apply map_get_false in Hget as [Hget _].
      rewrite -not_elem_of_dom Hdomwrs -Hgid in Hget.
      by pose proof (elem_of_key_to_group key).
    }
    apply map_get_true in Hget.
    iAssert (⌜is_Some (pwrsm !! gid)⌝)%I as %[pwrs Hpwrs].
    { iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom.
      iPureIntro.
      by rewrite -elem_of_dom -Hdom elem_of_dom.
    }
    iDestruct (big_sepM2_delete with "Hpwrsm") as "[Hpwrs Hpwrsm]"; [done | done |].

    (*@     pwrs[key] = value                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_MapInsert with "Hpwrs"); first done.
    iIntros "Hpwrs".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hwrsp"); first done.
    iIntros "Hwrsp".
    wp_pures.
    iApply "HΦ".
    set pwrs' := <[key := value]> pwrs.
    iAssert ([∗ map] p; m ∈ pwrsmP; <[gid := pwrs']> pwrsm, own_map p (DfracOwn 1) m)%I
      with "[Hpwrsm Hpwrs]" as "Hpwrsm".
    { iDestruct (big_sepM2_insert_2 (λ k p m, own_map p (DfracOwn 1) m) _ _ gid with "Hpwrs Hpwrsm")
        as "Hpwrsm".
      rewrite insert_delete; last apply Hget.
      rewrite insert_delete_insert.
      done.
    }
    iFrame "∗ %".
    iPureIntro.
    intros g m Hgm.
    destruct (decide (gid = g)) as [-> | Hne].
    - rewrite lookup_insert in Hgm. inv Hgm.
      specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
      by rewrite Hwrsg wrs_group_insert.
    - rewrite lookup_insert_ne in Hgm; last done.
      specialize (Hwrsg _ _ Hgm). simpl in Hwrsg.
      subst m.
      by rewrite wrs_group_insert_ne; last rewrite Hgid.
  Qed.

  Theorem wp_Txn__resetwrs (txn : loc) q wrs :
    {{{ own_txn_wrs txn q wrs }}}
      Txn__resetwrs #txn
    {{{ RET #(); own_txn_wrs txn (DfracOwn 1) ∅ }}}.
  Proof.
    iIntros (Φ) "Hwrs HΦ".
    wp_rec.

    (*@ func (txn *Txn) resetwrs() {                                            @*)
    (*@     // Creating a new @wrs is not really necessary, but currently it seems like @*)
    (*@     // there's no easy way to reason modifying a map while iterating over it @*)
    (*@     // (which is a defined behavior in Go).                             @*)
    (*@     wrs := make(map[uint64]map[string]tulip.Value)                      @*)
    (*@     for gid := range(txn.wrs) {                                         @*)
    (*@         wrs[gid] = make(map[string]tulip.Value)                         @*)
    (*@     }                                                                   @*)
    (*@     txn.wrs = wrs                                                       @*)
    (*@     txn.wrsp = make(map[string]tulip.Value)                             @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewMap.
    iIntros (wrsP') "HpwrsmP'".
    do 2 iNamed "Hwrs".
    (* iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom. *)
    wp_loadField.
    set P := (λ (mx : gmap u64 loc),
      let em := gset_to_gmap (∅ : dbmap) (dom mx) in
      ∃ (pwrsmP' : gmap u64 loc),
        "HpwrsmP'" ∷ own_map wrsP' (DfracOwn 1) pwrsmP' ∗
        "Hpwrsm'"  ∷ ([∗ map] p;m ∈ pwrsmP';em, own_map p (DfracOwn 1) m))%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "HpwrsmP [HpwrsmP']").
    { subst P. simpl.
      rewrite dom_empty_L gset_to_gmap_empty.
      iFrame.
      by iApply big_sepM2_empty.
    }
    { clear Φ.
      iIntros (m gid pwrsP Φ) "!> [HP [%Hnone %Hsome]] HΦ".
      iNamed "HP".
      wp_pures.
      wp_apply wp_NewMap.
      iIntros (empP) "HempP".
      wp_apply (wp_MapInsert with "HpwrsmP'"); first by auto.
      iIntros "HpwrsmP'".
      iApply "HΦ".
      subst P. simpl.
      iFrame.
      rewrite dom_insert_L gset_to_gmap_union_singleton.
      iApply (big_sepM2_insert_2 with "[HempP] Hpwrsm'"); first iFrame.
    }
    iIntros "[HpwrsmP HP]".
    subst P. simpl.
    iNamed "HP".
    wp_storeField.
    wp_apply wp_NewMap.
    iIntros (wrspP') "HwrspP'".
    wp_storeField.
    iApply "HΦ".
    iDestruct (big_sepM2_dom with "Hpwrsm'") as %Hdom'.
    iFrame "∗ %".
    iPureIntro.
    split; last first.
    { by rewrite Hdom' dom_gset_to_gmap Hdomwrs. }
    intros g m Hgm.
    rewrite lookup_gset_to_gmap_Some in Hgm.
    destruct Hgm as [_ Hm].
    by rewrite /wrs_group map_filter_empty.
  Qed.

  Theorem wp_Txn__setptgs txn q wrs :
    {{{ own_txn_wrs txn q wrs ∗ own_txn_ptgs txn [] }}}
      Txn__setptgs #txn
    {{{ RET #(); ∃ ptgs, own_txn_wrs txn q wrs ∗ own_txn_ptgs txn ptgs ∗
                         ⌜list_to_set ptgs = ptgroups (dom wrs)⌝
    }}}.
  Proof using heapGS0 tulip_ghostG0 Σ.
    iIntros (Φ) "[Hwrs Hptgs] HΦ".
    wp_rec.

    (*@ func (txn *Txn) setptgs() {                                             @*)
    (*@     var ptgs = txn.ptgs                                                 @*)
    (*@                                                                         @*)
    iNamed "Hptgs".
    clear Hnd.
    wp_loadField.
    wp_apply wp_ref_to; first apply slice_val_ty.
    iIntros (ptgsP) "HptgsP".

    (*@     for gid, pwrs := range(txn.wrs) {                                   @*)
    (*@         if uint64(len(pwrs)) != 0 {                                     @*)
    (*@             ptgs = append(ptgs, gid)                                    @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@     txn.ptgs = ptgs                                                     @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hwrs".
    wp_loadField.
    set P := (λ (mx : gmap u64 loc),
      ∃ (s : Slice.t) (ptgs : list u64),
        "HptgsP" ∷ ptgsP ↦[slice.T uint64T] (to_val s) ∗
        "Hptgs"  ∷ own_slice s uint64T (DfracOwn 1) ptgs ∗
        "Hpwrsm" ∷ ([∗ map] p;m ∈ pwrsmP;pwrsm, own_map p q m) ∗
        "%Hnd"   ∷ ⌜NoDup ptgs⌝ ∗
        "%Hincl" ∷ ⌜Forall (λ g, g ∈ dom mx) ptgs⌝ ∗
        (* non-empty ↔ in ptgs *)
        "%Hspec" ∷ ⌜set_Forall (λ g, keys_group g (dom wrs) ≠ ∅ ↔ g ∈ ptgs) (dom mx)⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "HpwrsmP [$HptgsP $Hptgs $Hpwrsm]").
    { iPureIntro. by split; first apply NoDup_nil. }
    { clear Φ.
      iIntros (m gid pwrsP Φ) "!> [HP [%Hnone %Hsome]] HΦ".
      iNamed "HP".
      iAssert (⌜is_Some (pwrsm !! gid)⌝)%I as %[pwrs Hpwrs].
      { iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom.
        iPureIntro.
        by rewrite -elem_of_dom -Hdom elem_of_dom.
      }
      iDestruct (big_sepM2_lookup_acc with "Hpwrsm") as "[Hpwrs HpwrsmC]"; [done | done |].
      wp_apply (wp_MapLen with "Hpwrs").
      iIntros "[%Hsize Hpwrs]".
      iDestruct ("HpwrsmC" with "Hpwrs") as "Hpwrsm".
      wp_if_destruct.
      { wp_load.
        (* NB: need to provide [own_slice] to properly resolve the right typeclass. *)
        wp_apply (wp_SliceAppend with "Hptgs").
        iIntros (s') "Hptgs".
        wp_store.
        iApply "HΦ".
        iFrame.
        iPureIntro.
        split.
        { apply NoDup_snoc; last apply Hnd.
          intros Hgid.
          rewrite Forall_forall in Hincl.
          specialize (Hincl _ Hgid).
          by apply not_elem_of_dom in Hnone.
        }
        split.
        { rewrite Forall_app Forall_singleton dom_insert_L.
          split; last set_solver.
          apply (Forall_impl _ _ _ Hincl).
          set_solver.
        }
        intros g Hg.
        rewrite dom_insert_L elem_of_union in Hg.
        split.
        { intros Hne.
          destruct Hg as [? | Hg]; first set_solver.
          specialize (Hspec _ Hg). simpl in Hspec.
          set_solver.
        }
        { intros Hsnoc.
          destruct Hg as [Hgid | Hg]; last first.
          { specialize (Hspec _ Hg). simpl in Hspec.
            apply Hspec.
            rewrite -not_elem_of_dom in Hnone.
            set_solver.
          }
          rewrite elem_of_singleton in Hgid.
          subst g.
          (* FIXME: not sure if word is supposed to solve this immediately *)
          assert (Hnz : size pwrs ≠ O).
          { intros Hz. rewrite Hz in Heqb. word. }
          clear Heqb.
          specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
          intros Hempty.
          rewrite -wrs_group_keys_group_dom -Hwrsg in Hempty.
          apply dom_empty_inv_L in Hempty.
          by rewrite map_size_non_empty_iff in Hnz.
        }
      }
      iApply "HΦ".
      iFrame.
      iPureIntro.
      rewrite dom_insert_L.
      split; first apply Hnd.
      split.
      { apply (Forall_impl _ _ _ Hincl). set_solver. }
      apply set_Forall_union; last apply Hspec.
      rewrite set_Forall_singleton.
      assert (Hsizez : size pwrs = O).
      { rewrite Heqb in Hsize. done. }
      split.
      { intros Hne.
        specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
        rewrite -wrs_group_keys_group_dom -Hwrsg in Hne.
        apply map_size_empty_inv in Hsizez.
        by rewrite Hsizez in Hne.
      }
      { intros Hinptgs.
        rewrite Forall_forall in Hincl.
        specialize (Hincl _ Hinptgs).
        by rewrite -not_elem_of_dom in Hnone.
      }
    }
    iIntros "[HpwrsmP HP]". 
    iNamed "HP".
    wp_load. wp_storeField.
    iApply "HΦ".
    iFrame "∗ # %".
    iPureIntro.
    apply set_eq.
    intros gid.
    rewrite elem_of_ptgroups elem_of_list_to_set.
    split.
    { intros Hgid.
      rewrite Forall_forall in Hincl.
      specialize (Hincl _ Hgid).
      specialize (Hspec _ Hincl). simpl in Hspec.
      by apply Hspec.
    }
    { intros Hne.
      destruct (decide (gid ∈ gids_all)) as [Hin | Hnotin]; last first.
      { rewrite /keys_group in Hne.
        apply set_choose_L in Hne as [k Hk].
        pose proof (elem_of_key_to_group k) as Hin.
        set_solver.
      }
      rewrite Hdomwrs in Hspec.
      specialize (Hspec _ Hin). simpl in Hspec.
      by apply Hspec.
    }
  Qed.

  Theorem wp_Txn__resetptgs (txn : loc) ptgs :
    {{{ own_txn_ptgs txn ptgs }}}
      Txn__resetptgs #txn
    {{{ RET #(); own_txn_ptgs txn [] }}}.
  Proof.
    iIntros (Φ) "Hptgs HΦ".
    wp_rec.

    (*@ func (txn *Txn) resetptgs() {                                           @*)
    (*@     txn.ptgs = txn.ptgs[:0]                                             @*)
    (*@ }                                                                       @*)
    iNamed "Hptgs".
    wp_loadField.
    wp_apply wp_SliceTake; first word.
    wp_storeField.
    iApply "HΦ".
    iDestruct (own_slice_take_cap _ _ _ (W64 0) with "Hptgs") as "Hptgs"; first word.
    iFrame.
    iPureIntro.
    by apply NoDup_nil.
  Qed.

  Theorem wp_Txn__reset (txn : loc) wrs q ptgs :
    {{{ own_txn_wrs txn q wrs ∗ own_txn_ptgs txn ptgs }}}
      Txn__reset #txn
    {{{ RET #(); own_txn_wrs txn (DfracOwn 1) ∅ ∗ own_txn_ptgs txn [] }}}.
  Proof.
    iIntros (Φ) "[Hwrs Hptgs] HΦ".
    wp_rec.

    (*@ func (txn *Txn) reset() {                                               @*)
    (*@     txn.resetwrs()                                                      @*)
    (*@     txn.resetptgs()                                                     @*)
    (*@ }                                                                       @*)
    wp_apply (wp_Txn__resetwrs with "Hwrs").
    iIntros "Hwrs".
    wp_apply (wp_Txn__resetptgs with "Hptgs").
    iIntros "Hptgs".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_Txn__commit txn tid rds wrsphys wrsproph γ τ :
    is_lnrz_tid γ tid -∗
    all_prepared γ tid wrsphys -∗
    {{{ own_txn_prepared txn tid rds wrsphys γ τ ∗ own_cmt_tmod γ tid wrsproph }}}
      Txn__commit #txn
    {{{ RET #(); own_txn_uninit txn γ ∗ ⌜wrsphys = wrsproph⌝ }}}.
  Proof.
    iIntros "#Hlnrzed #Hprep" (Φ) "!> [Htxn Htidc] HΦ".
    wp_rec.

    (*@ func (txn *Txn) commit() {                                              @*)
    (*@     ResolveCommit(txn.proph, txn.ts, txn.wrs)                           @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn". iNamed "Hwrs".
    do 3 wp_loadField.
    wp_apply (wp_ResolveCommit with "[$Hwrsp]"); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iMod (txnsys_inv_commit with "Hlnrzed Hprep Htxnsys Hgroups Hrgs Hkeys")
      as "(Htxnsys & Hgroups & Hrgs & Hkeys & #Hcmt)".
    { by rewrite Hfuture. }
    iAssert (⌜wrsphys = wrsproph⌝)%I as %Heq.
    { do 2 iNamed "Htxnsys".
      iDestruct (txn_res_lookup with "Hresm Hcmt") as %Hwrsc.
      iDestruct (elem_of_committed_partitioned_tids with "Hpart") as %[Hnotinwc Hnotinwa].
      { by eauto. }
      iDestruct (cmt_tmod_lookup with "Htidcs Htidc") as %Htidc.
      specialize (Htidcs _ _ Htidc). simpl in Htidcs.
      (* Prove [resm !! tid = Some (ResCommitted wrs)]. *)
      destruct Htidcs as [Htmodcs | Hresm].
      { by rewrite not_elem_of_dom Htmodcs in Hnotinwc. }
      rewrite Hresm in Hwrsc. symmetry in Hwrsc. inv Hwrsc.
      done.
    }
    (* Close the invariant. *)
    rewrite Hfuture /=.
    iDestruct (txnsys_inv_merge_future with "Hproph Htxnsys") as "Htxnsys".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxnsys Hkeys Hgroups Hrgs]") as "_"; first by iFrame.
    iIntros "!> Hwrsp".
    wp_pures.
    do 2 wp_loadField.

    (*@     ts := txn.ts                                                        @*)
    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@                                                                         @*)
    iNamed "Hptgs". iNamed "Hwrs".
    iDestruct "Hpwrsm" as "#Hpwrsm".
    wp_loadField.
    set P := (λ (_ : u64),
                "HpwrsmP" ∷ own_map wrsP (DfracOwn 1) pwrsmP ∗
                "Hgcoords" ∷ own_txn_gcoords txn γ)%I.
    iDestruct (own_slice_small_acc with "Hptgs") as "[Hptgs HptgsC]".
    wp_apply (wp_forSlice P with "[] [$Hptgs $HpwrsmP $Hgcoords]").
    { (* Loop body. *)
      clear Φ.

      (*@         gcoord := txn.gcoords[gid]                                      @*)
      (*@         pwrs := txn.wrs[gid]                                            @*)
      (*@                                                                         @*)
      iIntros (i gid Φ) "!> (HP & %Hinbound & %Hgid) HΦ".
      iNamed "HP". iNamed "Hgcoords".
      wp_loadField.
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrsphys)) as Hdom.
        apply elem_of_list_lookup_2 in Hgid.
        clear -Hdom Hgid Hptgs.
        set_solver.
      }
      wp_apply (wp_MapGet with "Hgcoords").
      iIntros (gcoordP ok) "[%Hgetgcoords Hgcoords]".
      destruct ok; last first.
      { apply map_get_false in Hgetgcoords as [Hnone _].
        by rewrite -not_elem_of_dom Hdomgcoords in Hnone.
      }
      apply map_get_true in Hgetgcoords.
      wp_apply (wp_MapGet with "HpwrsmP").
      iIntros (pwrsP ok) "[%Hgetwrs HpwrsmP]".
      destruct ok; last first.
      { apply map_get_false in Hgetwrs as [Hnotin _].
        by rewrite -not_elem_of_dom Hdomwrs in Hnotin.
      }
      apply map_get_true in Hgetwrs.
      iAssert (⌜is_Some (pwrsm !! gid)⌝)%I as %[pwrs Hpwrs].
      { iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom.
        iPureIntro.
        by rewrite -elem_of_dom -Hdom elem_of_dom.
      }
      iDestruct (big_sepM2_lookup_acc with "Hpwrsm") as "[Hpwrs HpwrsmC]"; [done | done |].

      (*@         go func() {                                                     @*)
      (*@             gcoord.Commit(ts, pwrs)                                     @*)
      (*@         }()                                                             @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_pures.
      iDestruct (big_sepM_lookup with "Hgcoordsabs") as "Hgcoordabs"; first apply Hgetgcoords.
      wp_apply wp_fork.
      { wp_apply (wp_GroupCoordinator__Commit with "[] Hgcoordabs Hpwrs").
        { rewrite Htsword.
          iFrame "Hcmt Htxnwrs".
          iPureIntro.
          assert (Hinptgs : gid ∈ ptgroups (dom wrsphys)).
          { rewrite -Hptgs elem_of_list_to_set elem_of_list_lookup. by eauto. }
          specialize (Hwrsg _ _ Hpwrs).
          done.
        }
        by iIntros "_".
      }
      iApply "HΦ".
      iFrame "∗ # %".
    }
    iIntros "[HP Hptgs]".
    iNamed "HP". clear P.
    iDestruct ("HptgsC" with "Hptgs") as "Hptgs".
    iAssert (own_txn_ptgs txn ptgs)%I with "[$HptgsS $Hptgs]" as "Hptgs"; first done.

    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
    iAssert (own_txn_wrs txn DfracDiscarded wrsphys)%I
      with "[$HwrsP $HwrspP $Hwrsp $HpwrsmP]" as "Hwrs".
    { iFrame "# %". }
    wp_apply (wp_Txn__reset with "[$Hwrs $Hptgs]").
    iIntros "[Hwrs Hptgs]".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Txn__commit_in_abort_future txn tid rds wrs γ τ :
    is_lnrz_tid γ tid -∗
    all_prepared γ tid wrs -∗
    {{{ own_txn_prepared txn tid rds wrs γ τ ∗ own_wabt_tid γ tid }}}
      Txn__commit #txn
    {{{ RET #(); False }}}.
  Proof.
    iIntros "#Hlnrzed #Hprep" (Φ) "!> [Htxn Hwabt] HΦ".
    wp_rec.

    (*@ func (txn *Txn) commit() {                                              @*)
    (*@     trusted_proph.ResolveCommit(txn.proph, txn.ts, txn.wrsp)            @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn". iNamed "Hwrs".
    do 3 wp_loadField.
    wp_apply (wp_ResolveCommit with "[$Hwrsp]"); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iMod (txnsys_inv_commit with "Hlnrzed Hprep Htxnsys Hgroups Hrgs Hkeys")
      as "(Htxnsys & Hgroups & Hrgs & Hkeys & Hcmt)".
    { by rewrite Hfuture. }
    (* Obtain contradiction. *)
    do 2 iNamed "Htxnsys".
    iDestruct (txn_res_lookup with "Hresm Hcmt") as %Hcmt.
    iDestruct (wabt_tid_elem_of with "Htidas Hwabt") as %Hwabt.
    rewrite -Htidas in Hwabt.
    iDestruct (elem_of_tmodas_partitioned_tids with "Hpart") as %[_ Hnotin].
    { apply Hwabt. }
    by specialize (Hnotin _ Hcmt).

    (*@     ts := txn.ts                                                        @*)
    (*@     wrs := txn.wrs                                                      @*)
    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         gcoord := txn.gcoords[gid]                                      @*)
    (*@         pwrs := wrs[gid]                                                @*)
    (*@                                                                         @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.Commit(ts, pwrs)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
  Qed.

  Theorem wp_Txn__abort txn tid rds wrs γ τ :
    is_txn_aborted γ tid -∗
    {{{ own_txn_prepared txn tid rds wrs γ τ ∗ own_wabt_tid γ tid }}}
      Txn__abort #txn
    {{{ RET #(); own_txn_uninit txn γ }}}.
  Proof.
    iIntros "#Habt" (Φ) "!> [Htxn Hwabt] HΦ".
    wp_rec.

    (*@ func (txn *Txn) abort() {                                               @*)
    (*@     trusted_proph.ResolveAbort(txn.proph, txn.ts)                       @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn".
    do 2 wp_loadField.
    wp_apply (wp_ResolveAbort); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iMod (txnsys_inv_abort with "Habt Hwabt Htxnsys") as "Htxnsys".
    { by rewrite Hfuture. }
    rewrite Hfuture /=.
    iDestruct (txnsys_inv_merge_future with "Hproph Htxnsys") as "Htxnsys".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxnsys Hkeys Hgroups Hrgs]") as "_"; first by iFrame.
    iIntros "!> _".
    wp_pures.

    (*@     ts := txn.ts                                                        @*)
    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@                                                                         @*)
    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)


    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         rg := txn.rgs[gid]                                              @*)
    (*@         rg.Abort(txn.ts)                                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hptgs".
    do 2 wp_loadField.
    set P := (λ (_ : u64), own_txn_gcoords txn γ)%I.
    iDestruct (own_slice_small_acc with "Hptgs") as "[Hptgs HptgsC]".
    wp_apply (wp_forSlice P with "[] [$Hptgs $Hgcoords]").
    { (* Loop body. *)
      clear Φ.

      (*@         gcoord := txn.gcoords[gid]                                      @*)
      (*@                                                                         @*)
      iIntros (i gid Φ) "!> (Hgcoords & %Hinbound & %Hgid) HΦ".
      iNamed "Hgcoords".
      wp_loadField.
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrs)) as Hdom.
        apply elem_of_list_lookup_2 in Hgid.
        clear -Hdom Hgid Hptgs.
        set_solver.
      }
      wp_apply (wp_MapGet with "Hgcoords").
      iIntros (gcoordP ok) "[%Hgetgcoords Hgcoords]".
      destruct ok; last first.
      { apply map_get_false in Hgetgcoords as [Hnone _].
        by rewrite -not_elem_of_dom Hdomgcoords in Hnone.
      }
      apply map_get_true in Hgetgcoords.
      (*@         go func() {                                                     @*)
      (*@             gcoord.Abort(ts)                                            @*)
      (*@         }()                                                             @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_pures.
      iDestruct (big_sepM_lookup with "Hgcoordsabs") as "Hgcoordabs"; first apply Hgetgcoords.
      wp_apply wp_fork.
      { wp_apply (wp_GroupCoordinator__Abort with "[] Hgcoordabs").
        { rewrite Htsword. by iFrame "Habt". }
        done.
      }
      iApply "HΦ".
      iFrame "∗ # %".
    }
    iIntros "[Hgcoods Hptgs]". subst P. simpl.
    iDestruct ("HptgsC" with "Hptgs") as "Hptgs".
    iAssert (own_txn_ptgs txn ptgs)%I with "[$HptgsS $Hptgs]" as "Hptgs"; first done.

    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
    wp_apply (wp_Txn__reset with "[$Hwrs $Hptgs]").
    iIntros "[Hwrs Hptgs]".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Txn__abort_in_commit_future txn tid rds wrsphys wrsproph γ τ :
    is_txn_aborted γ tid -∗
    {{{ own_txn_prepared txn tid rds wrsphys γ τ ∗ own_cmt_tmod γ tid wrsproph }}}
      Txn__abort #txn
    {{{ RET #(); False }}}.
  Proof.
    iIntros "#Habt" (Φ) "!> [Htxn Htidc] HΦ".
    wp_rec.

    (*@ func (txn *Txn) abort() {                                               @*)
    (*@     trusted_proph.ResolveAbort(txn.proph, txn.ts)                       @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn".
    do 2 wp_loadField.
    wp_apply (wp_ResolveAbort); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO". do 2 iNamed "Htxnsys".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    (* Prove [tid] must not have committed. *)
    iDestruct (txn_res_lookup with "Hresm Habt") as %Habt.
    iDestruct (cmt_tmod_lookup with "Htidcs Htidc") as %Htidc.
    specialize (Htidcs _ _ Htidc). simpl in Htidcs.
    destruct Htidcs as [Hwc | Hcmt]; last first.
    { by rewrite Hcmt in Habt. }
    specialize (Hcf _ _ Hwc). simpl in Hcf.
    destruct Hcf as (lp & ls & Hfc & _).
    assert (Hhead : head_abort future tid).
    { by rewrite Hfuture. }
    destruct (first_commit_head_abort _ _ _ _ _ Hfc Hhead) as [].

    (*@     ts := txn.ts                                                        @*)
    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         gcoord := txn.gcoords[gid]                                      @*)
    (*@                                                                         @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.Abort(ts)                                            @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
  Qed.

  Theorem wp_Txn__cancel txn tid rds γ τ :
    {{{ own_txn txn tid rds γ τ ∗ own_wabt_tid γ tid ∗ own_txn_reserved_wrs γ tid }}}
      Txn__cancel #txn
    {{{ RET #(); own_txn_uninit txn γ }}}.
  Proof.
    iIntros (Φ) "(Htxn & Habt & Hwrsexcl) HΦ".
    wp_rec.

    (*@ func (txn *Txn) cancel() {                                              @*)
    (*@     trusted_proph.ResolveAbort(txn.proph, txn.ts)                       @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn".
    do 2 wp_loadField.
    wp_apply (wp_ResolveAbort); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iMod (txnsys_inv_cancel with "Habt Hwrsexcl Htxnsys") as "Htxnsys".
    { by rewrite Hfuture. }
    rewrite Hfuture /=.
    iDestruct (txnsys_inv_merge_future with "Hproph Htxnsys") as "Htxnsys".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxnsys Hkeys Hgroups Hrgs]") as "_"; first by iFrame.
    iIntros "!> _".

    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
    wp_apply (wp_Txn__reset with "[$Hwrs $Hptgs]").
    iIntros "[Hwrs Hptgs]".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Txn__cancel_in_commit_future txn tid rds γ τ :
    {{{ own_txn txn tid rds γ τ ∗ (∃ m, own_cmt_tmod γ tid m) ∗ own_txn_reserved_wrs γ tid }}}
      Txn__cancel #txn
    {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "(Htxn & [%m Htidc] & Hwrsexcl) HΦ".
    wp_rec.

    (*@ func (txn *Txn) cancel() {                                              @*)
    (*@     trusted_proph.ResolveAbort(txn.proph, txn.ts)                       @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn".
    do 2 wp_loadField.
    wp_apply (wp_ResolveAbort); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO". do 2 iNamed "Htxnsys".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    (* Obtain [tmods !! tid = Some m]. *)
    iDestruct (cmt_tmod_lookup with "Htidcs Htidc") as %Htidc.
    specialize (Htidcs _ _ Htidc). simpl in Htidcs.
    (* Prove [resm !! tid = Some (ResCommitted m)] impossible, i.e., [tid] not committed yet. *)
    destruct Htidcs as [Htmodcs | Hcmt]; last first.
    { iDestruct (big_sepM_lookup with "Hvr") as "Hvc"; first apply Hcmt.
      iDestruct "Hvc" as "[Hwrsrcpt _]".
      (* Contradicting facts:
       * 1. Txn still owns exclusively the write-set (which is true before prepare).
       * Represented as [Hwrsexcl] from the precondition.
       * 2. Txn has set the write-set and given up the ability to change
       * (which is true after prepare). Represented as [Hwrsrcpt].
       *)
      by iDestruct (txn_oneshot_wrs_agree with "Hwrsexcl Hwrsrcpt") as %Hcontra.
    }
    (* Obtain [first_commit]. *)
    specialize (Hcf _ _ Htmodcs). simpl in Hcf.
    destruct Hcf as (lp & ls & Hfc & _).
    (* Obtain contradiction from [first_commit] and [head_abort]. *)
    assert (Hha : head_abort future tid).
    { by rewrite Hfuture /head_abort /=. }
    destruct (first_commit_head_abort _ _ _ _ _ Hfc Hha).

    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
  Qed.

  Theorem wp_Txn__begin (txn : loc) γ :
    ⊢ {{{ own_txn_uninit txn γ }}}
      <<< ∀∀ (ts : nat), own_largest_ts γ ts >>>
        Txn__begin #txn @ ↑tsNS
      <<< ∃∃ (ts' : nat), own_largest_ts γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
      {{{ RET #(); own_txn_init txn ts' γ }}}.
  Proof.
    (*@ func (txn *Txn) begin() {                                               @*)
    (*@     // TODO                                                             @*)
    (*@     // Ghost action: Linearize.                                         @*)
    (*@     txn.ts = GetTS()                                                    @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__prepare txn tid rds wrs γ τ :
    {{{ own_txn_stable txn tid rds wrs γ τ }}}
      Txn__prepare #txn
    {{{ (status : txnphase), RET #(txnphase_to_u64 status); 
        own_txn_prepared txn tid rds wrs γ τ ∗ safe_txnphase γ tid status
    }}}.
  Proof.
    iIntros (Φ) "Htxn HΦ".
    wp_rec.

    (*@ func (txn *Txn) prepare() uint64 {                                      @*)
    (*@     // Compute the participant groups.                                  @*)
    (*@     txn.setptgs()                                                       @*)
    (*@                                                                         @*)
    iNamed "Htxn".
    wp_apply (wp_Txn__setptgs with "[$Hwrs $Hptgs]").
    iIntros "Hptgs".
    iDestruct "Hptgs" as (ptgs) "(Hwrs & Hptgs & %Hptgs)".

    (*@     // TODO: init the group coordinator                                 @*)
    (*@                                                                         @*)
    (*@     ts := txn.ts                                                        @*)
    (*@     ptgs := txn.ptgs                                                    @*)
    (*@                                                                         @*)
    iNamed "Htxn". iNamed "Hptgs".
    do 2 wp_loadField.

    (*@     // An alternative (and more elegant) design would be using a wait-groups, but @*)
    (*@     // the CV approach has the advantage of early abort: If the transaction @*)
    (*@     // fails to prepare on one of the participant groups (e.g., due to conflict @*)
    (*@     // with another transaction), then the CV approach can "short-circuiting" to @*)
    (*@     // aborting the entire transaction, whereas the WaitGroup approach would @*)
    (*@     // have to wait until all groups reach their own prepare decisions. @*)
    (*@     mu := new(sync.Mutex)                                               @*)
    (*@     cv := sync.NewCond(mu)                                              @*)
    (*@     var np uint64 = 0                                                   @*)
    (*@     var st uint64 = tulip.TXN_PREPARED                                  @*)
    (*@                                                                         @*)
    wp_apply wp_new_free_lock.
    iIntros (muP) "Hfree".
    wp_apply (wp_newCond' with "Hfree").
    iIntros (cvP) "[Hfree #Hcv]".
    wp_apply wp_ref_to; first by auto.
    iIntros (npP) "HnpP".
    wp_apply wp_ref_to; first by auto.
    iIntros (stP) "HstP".
    wp_pures.
    (* Allocate exclusive tokens to prove freshness of response. *)
    iApply fupd_wp.
    iMod (local_gid_tokens_alloc (ptgroups (dom wrs))) as (α) "Htks".
    iModIntro.
    (* Establish the lock invariant. *)
    set I := (∃ (np : u64) (st : txnphase) (gids : gset u64),
                 "HnpP" ∷ npP ↦[uint64T] #np ∗
                 "HstP" ∷ stP ↦[uint64T] #(txnphase_to_u64 st) ∗
                 "Htks" ∷ ([∗ set] gid ∈ gids, local_gid_token α gid) ∗
                 "#Hst" ∷ (match st with
                           | TxnPrepared => [∗ set] gid ∈ gids, is_group_prepared γ gid tid
                           | TxnCommitted => (∃ wrs, is_txn_committed γ tid wrs)
                           | TxnAborted => is_txn_aborted γ tid
                           end) ∗
                 "%Hgidsincl" ∷ ⌜gids ⊆ ptgroups (dom wrs)⌝ ∗
                 "%Hsizegids" ∷ ⌜size gids = uint.nat np⌝)%I.
    iApply fupd_wp.
    iMod (alloc_lock tulipNS _ _ I with "Hfree [HnpP HstP]") as "#Hmu".
    { iModIntro.
      iExists (W64 0), TxnPrepared, ∅.
      iFrame.
      iSplit; first by iApply big_sepS_empty.
      iSplit; first by iApply big_sepS_empty.
      done.
    }
    iModIntro.

    (*@     // Some notes about the concurrency reasoning here:                 @*)
    (*@     //                                                                  @*)
    (*@     // 1. Even though at any point the group coordinators are assigned  @*)
    (*@     // exclusively to @txn.ts, the fact that it is reused (for performance @*)
    (*@     // reason: connection can be established only once for each @Txn object) @*)
    (*@     // means that the associated timestamp is not exposed in the representation @*)
    (*@     // predicate. Hence, we'll need a fractional RA to remember that the group @*)
    (*@     // coordinators are assigned to @txn.ts during the course of @txn.prepare. @*)
    (*@     //                                                                  @*)
    (*@     // 2. To establish sufficient proof that @txn.ts can finalize, we need to @*)
    (*@     // maintain the following the lock invariant:                       @*)
    (*@     // There exists a set G of group IDs:                               @*)
    (*@     // (a) @st associated with the right txn tokens; for @st = TXN_PREPARED, in @*)
    (*@     // particular, all groups in G must have prepared;                  @*)
    (*@     // (b) size(G) = @np;                                               @*)
    (*@     // (c) exclusive tokens over G, allowing a coordinator to prove uniqueness @*)
    (*@     // when adding its result, and thereby re-esbalish property (b).    @*)
    (*@                                                                         @*)
    (*@     // Try to prepare transaction @tcoord.ts on each group.             @*)
    (*@     for _, gid := range(ptgs) {                                         @*)
    (*@                                                                         @*)
    do 2 iNamed "Hwrs".
    iDestruct "Hpwrsm" as "#Hpwrsm".
    wp_loadField.
    set P := (λ (i : u64),
                "HpwrsmP" ∷ own_map wrsP (DfracOwn 1) pwrsmP ∗
                "Hgcoords" ∷ own_txn_gcoords txn γ ∗
                "Htks" ∷ [∗ set] gid ∈ list_to_set (drop (uint.nat i) ptgs), local_gid_token α gid)%I.
    iDestruct (own_slice_small_acc with "Hptgs") as "[Hptgs HptgsC]".
    iDestruct (own_slice_small_sz with "Hptgs") as %Hlenptgs.
    wp_apply (wp_forSlice P with "[] [$Hptgs $HpwrsmP $Hgcoords Htks]"); last first; first 1 last.
    { by rewrite uint_nat_W64_0 drop_0 Hptgs. }
    { clear Φ.

      (*@         gcoord := txn.gcoords[gid]                                      @*)
      (*@         pwrs := txn.wrs[gid]                                            @*)
      (*@                                                                         @*)
      iIntros (i gid Φ) "!> (HP & %Hinbound & %Hgid) HΦ".
      iNamed "HP". iNamed "Hgcoords".
      wp_loadField.
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrs)) as Hdom.
        apply elem_of_list_lookup_2 in Hgid.
        clear -Hdom Hgid Hptgs.
        set_solver.
      }
      wp_apply (wp_MapGet with "Hgcoords").
      iIntros (gcoordP ok) "[%Hgetgcoords Hgcoords]".
      destruct ok; last first.
      { apply map_get_false in Hgetgcoords as [Hnone _].
        by rewrite -not_elem_of_dom Hdomgcoords in Hnone.
      }
      apply map_get_true in Hgetgcoords.
      wp_apply (wp_MapGet with "HpwrsmP").
      iIntros (pwrsP ok) "[%Hgetwrs HpwrsmP]".
      destruct ok; last first.
      { apply map_get_false in Hgetwrs as [Hnotin _].
        by rewrite -not_elem_of_dom Hdomwrs in Hnotin.
      }
      apply map_get_true in Hgetwrs.
      iAssert (⌜is_Some (pwrsm !! gid)⌝)%I as %[pwrs Hpwrs].
      { iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom.
        iPureIntro.
        by rewrite -elem_of_dom -Hdom elem_of_dom.
      }
      iDestruct (big_sepM2_lookup_acc with "Hpwrsm") as "[Hpwrs HpwrsmC]"; [done | done |].
      wp_pures.
      assert (Hvg : gid ∈ ptgroups (dom wrs)).
      { rewrite -Hptgs elem_of_list_to_set. by apply elem_of_list_lookup_2 in Hgid. }

      (*@         go func() {                                                     @*)
      (*@                                                                         @*)
      iDestruct (big_sepM_lookup with "Hgcoordsabs") as "Hgcoordabs"; first apply Hgetgcoords.
      rewrite (drop_S _ _ _ Hgid) list_to_set_cons big_sepS_insert; last first.
      { rewrite not_elem_of_list_to_set. intros Hgidin.
        clear -Hgid Hgidin Hnd.
        rewrite -(take_drop_middle _ _ _ Hgid) in Hnd.
        apply NoDup_app in Hnd as (_ & _ & Hnd).
        by apply NoDup_cons in Hnd as [? _].
      }
      iDestruct "Htks" as "[Htk Htks]".
      wp_apply (wp_fork with "[Htk]").
      { (* Forked thread. *)

        (*@             stg, ok := gcoord.Prepare(ts, ptgs, pwrs)                   @*)
        (*@                                                                         @*)
        iModIntro.
        wp_apply (wp_GroupCoordinator__Prepare with "Hgcoordabs").
        iIntros (stg ok) "#Hsafe".
        wp_pures.

        (*@             if ok {                                                     @*)
        (*@                 mu.Lock()                                               @*)
        (*@                 if stg == tulip.TXN_PREPARED {                          @*)
        (*@                     np += 1                                             @*)
        (*@                 } else {                                                @*)
        (*@                     st = stg                                            @*)
        (*@                 }                                                       @*)
        (*@                 mu.Unlock()                                             @*)
        (*@                 cv.Signal()                                             @*)
        (*@             }                                                           @*)
        (*@                                                                         @*)
        destruct ok; wp_pures.
        { wp_apply (wp_Mutex__Lock with "Hmu").
          iIntros "[Hlocked HI]".
          iNamed "HI".
          assert (Hszgids : (size gids ≤ size gids_all)%nat).
          { apply subseteq_size. etrans; [apply Hgidsincl | apply subseteq_ptgroups]. }
          pose proof size_gids_all as Hszgidsall.
          wp_pures.
          (* Prove [safe_txn_pwrs] used in invariance of PREPARE and UNPREPARE. *)
          iAssert (safe_txn_pwrs γ gid tid pwrs)%I as "#Hsafepwrs".
          { iFrame "Htxnwrs".
            iPureIntro.
            specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
            pose proof (elem_of_ptgroups_non_empty _ _ Hvg) as Hne.
            rewrite -Hwrsg in Hne.
            done.
          }
          case_bool_decide as Hstg; wp_pures.
          { (* Case [TxnPrepared]. *)
            wp_load. wp_store.
            destruct stg; [| done | done].
            rewrite Htsword /=.
            iAssert (|={⊤}=> is_group_prepared γ gid tid)%I as "Hprepared".
            { iInv "Hinv" as "> HinvO" "HinvC".
              iNamed "HinvO".
              iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
              { apply Hin. }
              iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]".
              { apply Hin. }
              iDestruct "Hsafe" as "[Hqp Hqv]".
              iMod (group_inv_prepare with "Hqv Hqp Hsafepwrs Htxnsys Hkeys Hrg Hgroup")
                as "(Htxnsys & Hkeys & Hrg & Hgroup & #Hprepared)".
              iDestruct ("HrgsC" with "Hrg") as "Hrgs".
              iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
              iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
              done.
            }
            iMod "Hprepared" as "#Hprepared".
            wp_apply (wp_Mutex__Unlock with "[-]").
            { iFrame "Hmu Hlocked HnpP HstP".
              iModIntro.
              iExists ({[gid]} ∪ gids).
              iAssert (⌜gid ∉ gids⌝)%I as %Hnotin.
              { iIntros (Hgidin).
                iDestruct (big_sepS_elem_of with "Htks") as "Htk'"; first apply Hgidin.
                by iDestruct (local_gid_token_ne with "Htk Htk'") as %?.
              }
              iSplitL "Htk Htks".
              { iApply (big_sepS_insert_2 with "Htk Htks"). }
              iSplit.
              { destruct st; [| done | done].
                by iApply big_sepS_insert_2.
              }
              iPureIntro.
              { split.
                { clear -Hgidsincl Hvg. set_solver. }
                { rewrite size_union; last set_solver.
                  rewrite size_singleton Hsizegids.
                  clear -Hszgids Hszgidsall Hsizegids. word.
                }
              }
            }
            by wp_apply (wp_Cond__Signal with "Hcv").
          }
          { wp_store.
            destruct stg eqn:Hstgeq; first done.
            { (* Case [TxnCommitted]. *)
              wp_apply (wp_Mutex__Unlock with "[-]").
              { iFrame "Hmu Hlocked ∗ # %". by rewrite Htsword. }
              by wp_apply (wp_Cond__Signal with "Hcv").
            }
            { (* Case [TxnAborted]. *)
              rewrite Htsword.
              iAssert (|={⊤}=> is_txn_aborted γ tid)%I as "Habted".
              { iDestruct "Hsafe" as "[? | Hsafe]"; first done.
                iInv "Hinv" as "> HinvO" "HinvC".
                iNamed "HinvO".
                iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
                { apply Hin. }
                iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]".
                { apply Hin. }
                iMod (txnsys_group_inv_unprepare with "Hsafe Hsafepwrs Hrg Hgroup Htxnsys")
                  as "(Hrg & Hgroup & Htxnsys & #Habted)".
                iDestruct ("HrgsC" with "Hrg") as "Hrgs".
                iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
                iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
                done.
              }
              iMod "Habted" as "#Habted".
              wp_apply (wp_Mutex__Unlock with "[-]").
              { iFrame "Hmu Hlocked ∗ # %". }
              by wp_apply (wp_Cond__Signal with "Hcv").
            }
          }
        }

        (*@             // @ok = false means that the group coordinator has already been @*)
        (*@             // assigned to a different transaction, implying nothing is waiting @*)
        (*@             // on the CV.                                               @*)
        (*@         }()                                                             @*)
        (*@     }                                                                   @*)
        (*@                                                                         @*)
        done.
      }

      iApply "HΦ".
      iFrame "∗ # %".
      rewrite uint_nat_word_add_S; last first.
      { clear -Hinbound. word. }
      done.
    }

    (*@     mu.Lock()                                                           @*)
    (*@     // Wait until either status is no longer TXN_PREPARED or all participant @*)
    (*@     // groups have responded.                                           @*)
    (*@     for st == tulip.TXN_PREPARED && np != uint64(len(ptgs)) {           @*)
    (*@         cv.Wait()                                                       @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iIntros "[HP Hptgs]".
    subst P. iNamed "HP".
    wp_apply (wp_Mutex__Lock with "Hmu").
    iIntros "[Hlocked HI]".
    wp_pures.
    set P := (λ cont : bool,
                ∃ (np : u64) (st : txnphase) (gids : gset u64),
                  "HnpP" ∷ npP ↦[uint64T] #np ∗
                  "HstP" ∷ stP ↦[uint64T] #(txnphase_to_u64 st) ∗
                  "Htks" ∷ ([∗ set] gid ∈ gids, local_gid_token α gid) ∗
                  "Hlocked" ∷ locked #muP ∗
                  "#Hst" ∷ (match st with
                            | TxnPrepared => [∗ set] gid ∈ gids, is_group_prepared γ gid tid
                            | TxnCommitted => (∃ wrs, is_txn_committed γ tid wrs)
                            | TxnAborted => is_txn_aborted γ tid
                            end) ∗
                  "%Hgidsincl" ∷ ⌜gids ⊆ ptgroups (dom wrs)⌝ ∗
                  "%Hsizegids" ∷ ⌜size gids = uint.nat np⌝ ∗
                  "%Hcond"     ∷ ⌜(if cont
                                   then True
                                   else match st with
                                        | TxnPrepared => uint.nat np = length ptgs
                                        | _ => True
                                        end)⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [Hlocked HI]"); last first; first 1 last.
    { iNamed "HI". iFrame "∗ # %". }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      wp_load.
      wp_pures.
      case_bool_decide as Hprepared; wp_pures.
      { wp_load.
        wp_apply wp_slice_len.
        wp_pures.
        case_bool_decide as Hsize; wp_pures.
        { iApply "HΦ".
          iFrame "∗ # %".
          iPureIntro.
          destruct st; try done.
          inv Hsize.
          clear -Hlenptgs. done.
        }
        wp_apply (wp_Cond__Wait with "[-HΦ]").
        { by iFrame "Hcv Hmu Hlocked ∗ # %". }
        iIntros "[Hlocked HI]".
        wp_pures.
        iApply "HΦ".
        iClear "Hst".
        iNamed "HI".
        by iFrame "∗ # %".
      }
      iApply "HΦ".
      iFrame "∗ # %".
      iPureIntro.
      by destruct st.
    }
    iClear "Htks".
    iNamed 1.
        
    (*@     status := st                                                        @*)
    (*@     mu.Unlock()                                                         @*)
    (*@                                                                         @*)
    wp_load. wp_pures.
    wp_apply (wp_Mutex__Unlock with "[Hlocked HnpP HstP Htks]").
    { by iFrame "Hmu Hlocked ∗ # %". }

    (*@     return status                                                       @*)
    (*@ }                                                                       @*)
    wp_pures.
    iApply "HΦ".
    iAssert (safe_txnphase γ tid st)%I as "#Hsafe".
    { destruct st; [| done | done].
      simpl.
      iFrame "Htxnwrs".
      assert (gids = ptgroups (dom wrs)) as ->; last done.
      apply set_subseteq_size_eq; first apply Hgidsincl.
      rewrite -Hptgs size_list_to_set; last apply Hnd.
      clear -Hsizegids Hcond. lia.
    }
    iDestruct ("HptgsC" with "Hptgs") as "Hptgs".
    by iFrame "Hsafe ∗ # %".
  Qed.

  Definition body_spec
    (body : val) (txn : loc) tid r
    (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
    (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ)
    γ τ : iProp Σ :=
    ∀ Φ,
    own_txn txn tid r γ τ ∗ ⌜P r⌝ ∗ txnmap_ptstos τ r -∗
    (∀ ok : bool,
       (own_txn txn tid r γ τ ∗
        if ok
        then ∃ w, ⌜Q r w ∧ dom r = dom w⌝ ∗ (Rc r w ∧ Ra r) ∗ txnmap_ptstos τ w
        else Ra r) -∗ Φ #ok) -∗
    WP body #txn {{ v, Φ v }}.

  Theorem wp_Txn__Run
    txn (body : val)
    (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
    (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ) γ :
    (∀ r w, (Decision (Q r w))) ->
    ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, body_spec body txn tid r P Q Rc Ra γ τ) }}}
      <<< ∀∀ (r : dbmap), ⌜P r ∧ dom r ⊆ keys_all⌝ ∗ own_db_ptstos γ r >>>
        Txn__Run #txn body @ ↑sysNS
      <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q r w⌝ ∗ own_db_ptstos γ w else own_db_ptstos γ r >>>
      {{{ RET #ok; own_txn_uninit txn γ ∗ if ok then Rc r w else Ra r }}}.
  Proof.
    iIntros (Hdec) "!>".
    iIntros (Φ) "[Htxn Hbody] HAU".
    wp_rec. wp_pures.

    (*@ func (txn *Txn) Run(body func(txn *Txn) bool) bool {                    @*)
    (*@     txn.begin()                                                         @*)
    (*@                                                                         @*)
    iAssert (∃ p, know_tulip_inv_with_proph γ p)%I as (p) "#Hinv".
    { do 2 iNamed "Htxn". iFrame "Hinv". }
    wp_apply (wp_Txn__begin with "[-Hbody HAU]").
    { iFrame "∗ # %". }
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (ncfupd_mask_subseteq (⊤ ∖ ↑sysNS)) as "Hclose"; first solve_ndisj.
    iMod "HAU" as (rds) "[[[%HP %Hdomr] Hdbpts] HAUC]".
    iModIntro.
    iNamed "HinvO".
    iDestruct (txnsys_inv_expose_future_extract_ts with "Htxnsys")
      as (future ts) "[Htxnsys Hts]".
    (* Prove [key_inv] are linearizable after [ts]. *)
    iDestruct (keys_inv_before_linearize with "Hkeys Hts") as "[Hkeys Hts]".
    iExists ts.
    (* Pass [ts_auth γ ts] to the underlying layer. *)
    iFrame "Hts".
    iIntros (tid) "[Hts %Htidgt]".
    iDestruct (largest_ts_witness with "Hts") as "#Htidlb".

    pose proof (peek_spec future tid) as Hpeek.
    set form := peek _ _ in Hpeek.
    set Qr := λ m, Q rds (m ∪ rds) ∧ dom m ⊆ dom rds.
    destruct (decide (incorrect_fcc Qr form)) as [Hifcc | HQ].
    { (* Case: Abort branch. *)
      iMod (txnsys_inv_linearize_abort form Q with "Htidlb Hdbpts Htxnsys Hkeys")
        as "(Hdbpts & Htxnsys & Hkeys & Htida & Hwrsexcl & Hclients & #HQ & #Hlnrzs & #Hlnrzed)".
      { apply Hdomr. }
      { apply Htidgt. }
      { apply Hpeek. }
      { done. }
      (* Choose the will-abort branch. Use [∅] as placeholder. *)
      iMod ("HAUC" $! false ∅ with "Hdbpts") as "HΦ".
      iMod "Hclose" as "_".
      iMod ("HinvC" with "[Hts Htxnsys Hkeys Hgroups Hrgs]") as "_".
      { iNamed "Htxnsys". iFrame "∗ # %". }
      (* Allocate transaction local view [txnmap_ptstos τ r]. *)
      iMod (txnmap_alloc rds) as (τ) "[Htxnmap Htxnpts]".
      iIntros "!> Htxn".
      iAssert (own_txn txn tid rds γ τ)%I with "[Htxn Htxnmap]" as "Htxn".
      { iClear "Hinv". do 2 iNamed "Htxn".
        iExists _, ∅.
        rewrite map_empty_union.
        by iFrame "∗ # %".
      }

      (*@     cmt := body(txn)                                                    @*)
      (*@                                                                         @*)
      wp_apply ("Hbody" with "[$Htxn $Htxnpts]"); first done.
      iIntros (cmt) "[Htxn Hpts]".

      (*@     if !cmt {                                                           @*)
      (*@         // This transaction has not really requested to prepare yet, so no @*)
      (*@         // cleanup tasks are required.                                  @*)
      (*@         txn.cancel()                                                    @*)
      (*@         return false                                                    @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { wp_apply (wp_Txn__cancel with "[$Htxn $Htida $Hwrsexcl]").
        iIntros "Htxn".
        wp_pures.
        iApply "HΦ".
        by iFrame.
      }

      (*@     status := txn.prepare()                                             @*)
      (*@                                                                         @*)
      iDestruct "Hpts" as (w) "([%HQ %Hdomw] & [_ HRa] & Hpts)".
      iAssert (|={⊤}=> ∃ wrst, own_txn_stable txn tid rds wrst γ τ)%I
        with "[Htxn Hwrsexcl Hpts]" as "Htxn".
      { iClear "Hinv". iNamed "Htxn".
        iDestruct (txnmap_subseteq with "Htxnmap Hpts") as %Hsubseteq.
        unshelve epose proof (subseteq_dom_eq _ _ Hsubseteq _) as Heq.
        { clear -Hincl Hdomw. set_solver. }
        subst w.
        iInv "Hinv" as "> HinvO" "HinvC".
        iNamed "HinvO".
        iMod (txnsys_inv_preprepare with "HQ Hwrsexcl Htxnsys") as "[Htxnsys Hwrsrcpt]".
        { apply Hvts. }
        { apply Hvwrs. }
        { done. }
        iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
        iFrame "∗ # %".
        do 2 iNamed "Hwrs".
        iFrame "∗ %".
        rewrite -big_sepM2_fupd.
        iApply (big_sepM2_mono with "Hpwrsm").
        iIntros (g r m Hr Hm) "Hm".
        by iMod (own_map_persist with "Hm") as "Hm".
      }
      iMod "Htxn" as (wrst) "Htxn".
      wp_apply (wp_Txn__prepare with "Htxn").
      iIntros (status) "[Htxn Hstatus]".

      (*@     if status == TXN_COMMITTED {                                        @*)
      (*@         // A backup coordinator must have committed this transaction, so simply @*)
      (*@         // reset the write-set here.                                    @*)
      (*@         txn.reset()                                                     @*)
      (*@         return true                                                     @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { destruct status eqn:Hstatus; [done | | done]. clear Heqb.
        subst status.
        iDestruct "Hstatus" as (wrs) "Hcmt".
        (* Obtain a contradiction from [Hcmt] and [Htida]. *)
        iApply fupd_wp.
        iInv "Hinv" as "> HinvO" "HinvC".
        iNamed "HinvO". do 2 iNamed "Htxnsys".
        iDestruct (txn_res_lookup with "Hresm Hcmt") as %Hcmt.
        iDestruct (wabt_tid_elem_of with "Htidas Htida") as %Hwabt.
        rewrite -Htidas in Hwabt.
        iDestruct (elem_of_tmodas_partitioned_tids with "Hpart") as %[_ Hnotin].
        { apply Hwabt. }
        by specialize (Hnotin _ Hcmt).
      }
      rename Heqb into Hstatusnc.

      (*@     if status == TXN_ABORTED {                                          @*)
      (*@         // Ghost action: Abort this transaction.                        @*)
      (*@         txn.abort()                                                     @*)
      (*@         return false                                                    @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { destruct status eqn:Hstatus; [done | done |]. clear Heqb.
        subst status.
        wp_apply (wp_Txn__abort with "Hstatus [$Htxn $Htida]").
        iIntros "Htxn".
        wp_pures.
        iApply "HΦ".
        by iFrame.
      }
      rename Heqb into Hstatusna.

      (*@     // Ghost action: Commit this transaction.                           @*)
      (*@     txn.commit()                                                        @*)
      (*@     return true                                                         @*)
      (*@ }                                                                       @*)
      destruct status; [| done | done]. simpl. clear Hstatusnc Hstatusna.
      iDestruct "Hstatus" as (wrs) "#Hprep".
      iAssert (⌜wrst = wrs⌝)%I as %->.
      { iClear "Hinv". iNamed "Htxn".
        iDestruct "Hprep" as "[#Hwrsrcpt _]".
        by iDestruct (txn_wrs_agree with "Hwrsrcpt Htxnwrs") as %?.
      }
      wp_apply (wp_Txn__commit_in_abort_future with "Hlnrzed Hprep [$Htxn $Htida]").
      iIntros ([]).
    }
    { (* Case: Commit branch. *)
      destruct form as [| | wrs | wrs]; [done | done | done |].
      apply dec_stable in HQ. simpl in Hpeek.
      subst Qr.
      destruct HQ as [HQ Hdomwrs].
      iMod (txnsys_inv_linearize_commit wrs Q with "Htidlb Hdbpts Htxnsys Hkeys")
        as "(Hdbpts & Htxnsys & Hkeys & Htidc & Hwrsexcl & Hclients & #HQ & #Hlnrzs & #Hlnrzed)".
      { apply Hdomwrs. }
      { apply Hdomr. }
      { apply Htidgt. }
      { apply Hpeek. }
      (* Choose the will-commit branch. *)
      iMod ("HAUC" $! true (wrs ∪ rds) with "[$Hdbpts]") as "HΦ"; first done.
      iMod "Hclose" as "_".
      iMod ("HinvC" with "[Hts Htxnsys Hkeys Hgroups Hrgs]") as "_".
      { iNamed "Htxnsys". iFrame "∗ # %". }
      iClear "Hinv".
      (* Allocate transaction local view [txnmap_ptstos τ r]. *)
      iMod (txnmap_alloc rds) as (τ) "[Htxnmap Htxnpts]".
      iIntros "!> Htxn".
      iAssert (own_txn txn tid rds γ τ)%I with "[Htxn Htxnmap]" as "Htxn".
      { do 2 iNamed "Htxn".
        iExists _, ∅.
        rewrite map_empty_union.
        by iFrame "∗ # %".
      }

      (*@     cmt := body(txn)                                                    @*)
      (*@                                                                         @*)
      wp_apply ("Hbody" with "[$Htxn $Htxnpts]"); first done.
      iIntros (cmt) "[Htxn Hpts]".

      (*@     if !cmt {                                                           @*)
      (*@         // This transaction has not really requested to prepare yet, so no @*)
      (*@         // cleanup tasks are required.                                  @*)
      (*@         txn.cancel()                                                    @*)
      (*@         return false                                                    @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { wp_apply (wp_Txn__cancel_in_commit_future with "[$Htxn $Htidc $Hwrsexcl]").
        iIntros ([]).
      }

      (*@     status := txn.prepare()                                             @*)
      (*@                                                                         @*)
      clear HQ.
      iDestruct "Hpts" as (w) "([%HQ %Hdomw] & [HRc _] & Hpts)".
      iAssert (|={⊤}=> ∃ wrst, own_txn_stable txn tid rds wrst γ τ ∗ ⌜w = wrst ∪ rds⌝)%I
        with "[Htxn Hwrsexcl Hpts]" as "Htxn".
      { clear p.
        iDestruct "Htxn" as (p wrst) "Htxn". iNamed "Htxn".
        iDestruct (txnmap_subseteq with "Htxnmap Hpts") as %Hsubseteq.
        unshelve epose proof (subseteq_dom_eq _ _ Hsubseteq _) as Heq.
        { clear -Hincl Hdomw. set_solver. }
        subst w.
        iInv "Hinv" as "> HinvO" "HinvC".
        iNamed "HinvO".
        iMod (txnsys_inv_preprepare with "HQ Hwrsexcl Htxnsys") as "[Htxnsys Hwrsrcpt]".
        { apply Hvts. }
        { apply Hvwrs. }
        { done. }
        iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
        iFrame "∗ # %".
        do 2 iNamed "Hwrs".
        iFrame "∗ %".
        iApply fupd_sep.
        iSplitL; last done.
        rewrite -big_sepM2_fupd.
        iApply (big_sepM2_mono with "Hpwrsm").
        iIntros (g r m Hr Hm) "Hm".
        by iMod (own_map_persist with "Hm") as "Hm".
      }
      iMod "Htxn" as (wrst) "[Htxn %Heq]". subst w.
      wp_apply (wp_Txn__prepare with "Htxn").
      iIntros (status) "[Htxn Hstatus]".

      (*@     if status == TXN_COMMITTED {                                        @*)
      (*@         // A backup coordinator must have committed this transaction, so simply @*)
      (*@         // reset the write-set here.                                    @*)
      (*@         txn.reset()                                                     @*)
      (*@         return true                                                     @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { destruct status eqn:Hstatus; [done | | done]. clear Heqb.
        subst status.
        iDestruct "Hstatus" as (wrsc) "#Hwrsc".
        iNamed "Htxn".
        (* Obtain [wrsc = wrs ∧ wrst = wrs]. *)
        iAssert (|={⊤}=> own_cmt_tmod γ tid wrs ∗ ⌜wrsc = wrs ∧ wrst = wrs⌝)%I
          with "[Htidc]" as "Htidc".
        { iInv "Hinv" as "> HinvO" "HinvC".
          iNamed "HinvO". do 2 iNamed "Htxnsys".
          iDestruct (txn_res_lookup with "Hresm Hwrsc") as %Hwrsc.
          iDestruct (elem_of_committed_partitioned_tids with "Hpart") as %[Hnotinwc Hnotinwa].
          { by eauto. }
          iDestruct (cmt_tmod_lookup with "Htidcs Htidc") as %Htidc.
          apply Htidcs in Htidc.
          (* Prove [resm !! tid = Some (ResCommitted wrs)]. *)
          destruct Htidc as [Htmodcs | Hresm].
          { by rewrite not_elem_of_dom Htmodcs in Hnotinwc. }
          rewrite Hresm in Hwrsc. symmetry in Hwrsc. inv Hwrsc.
          iDestruct (big_sepM_lookup with "Hvr") as "Hr"; first apply Hresm.
          iDestruct "Hr" as "[Hrcp _]".
          iDestruct (txn_wrs_agree with "Hrcp Htxnwrs") as %->.
          iMod ("HinvC" with "[-Htidc]") as "_".
          { by iFrame "∗ # %". }
          by iFrame "∗ %".
        }
        iMod "Htidc" as "[Htidc %Heq]".
        destruct Heq as [-> ->].
        iNamed "Htxn".
        wp_apply (wp_Txn__reset with "[$Hwrs $Hptgs]").
        iIntros "[Hwrs Hptgs]".
        wp_pures.
        iApply "HΦ".
        by iFrame "∗ # %".
      }
      rename Heqb into Hstatusnc.

      (*@     if status == TXN_ABORTED {                                          @*)
      (*@         // Ghost action: Abort this transaction.                        @*)
      (*@         txn.abort()                                                     @*)
      (*@         return false                                                    @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { destruct status eqn:Hstatus; [done | done |]. clear Heqb.
        subst status. simpl.
        wp_apply (wp_Txn__abort_in_commit_future with "Hstatus [$Htxn $Htidc]").
        iIntros ([]).
      }
      rename Heqb into Hstatusna.

      (*@     // Ghost action: Commit this transaction.                           @*)
      (*@     txn.commit()                                                        @*)
      (*@     return true                                                         @*)
      (*@ }                                                                       @*)
      destruct status as [| |] eqn:Hstatus; [| done | done].
      simpl. clear Hstatus Hstatusnc Hstatusna.
      iDestruct "Hstatus" as (wrsc) "#Hprep".
      iAssert (⌜wrsc = wrst⌝)%I as %->.
      { iNamed "Htxn".
        iDestruct "Hprep" as "[Hwrsrcpt _]".
        by iDestruct (txn_wrs_agree with "Htxnwrs Hwrsrcpt") as %?.
      }
      wp_apply (wp_Txn__commit with "Hlnrzed Hprep [Htxn Htidc]").
      { iFrame "∗ #". }
      iIntros "[Htxn %Heq]". subst wrst.
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
  Qed.

  Theorem wp_Txn__Write txn tid key value rds γ τ :
    {{{ own_txn txn tid rds γ τ ∗ (∃ vprev, txnmap_ptsto τ key vprev) }}}
      Txn__Write #txn #(LitString key) #(LitString value)
    {{{ RET #(); own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key (Some value) }}}.
  Proof.
    iIntros (Φ) "[Htxn [%v Hpt]] HΦ".
    wp_rec.

    (*@ func (txn *Txn) Write(key string, value string) {                       @*)
    (*@     v := tulip.Value{                                                   @*)
    (*@         Present : true,                                                 @*)
    (*@         Content : value,                                                @*)
    (*@     }                                                                   @*)
    (*@     txn.setwrs(key, v)                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Htxn".
    wp_pures.
    wp_apply (wp_Txn__setwrs _ _ (Some value) with "Hwrs").
    iIntros "Hwrs".
    wp_pures.
    iApply "HΦ".
    iDestruct (txnmap_lookup with "Htxnmap Hpt") as %Hlookup.
    apply elem_of_dom_2 in Hlookup.
    iMod (txnmap_update (Some value) with "Htxnmap Hpt") as "[Htxnmap Hpt]".
    rewrite insert_union_l.
    iFrame "∗ # %".
    iPureIntro.
    rewrite /valid_wrs dom_insert_L.
    set_solver.
  Qed.

  Theorem wp_Txn__Delete txn tid key rds γ τ :
    {{{ own_txn txn tid rds γ τ ∗ (∃ vprev, txnmap_ptsto τ key vprev) }}}
      Txn__Delete #txn #(LitString key)
    {{{ RET #(); own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key None }}}.
  Proof.
    iIntros (Φ) "[Htxn [%v Hpt]] HΦ".
    wp_rec.

    (*@ func (txn *Txn) Delete(key string) {                                    @*)
    (*@     v := tulip.Value{                                                   @*)
    (*@         Present : false,                                                @*)
    (*@     }                                                                   @*)
    (*@     txn.setwrs(key, v)                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Htxn".
    wp_pures.
    wp_apply (wp_Txn__setwrs _ _ None with "Hwrs").
    iIntros "Hwrs".
    wp_pures.
    iApply "HΦ".
    iDestruct (txnmap_lookup with "Htxnmap Hpt") as %Hlookup.
    apply elem_of_dom_2 in Hlookup.
    iMod (txnmap_update None with "Htxnmap Hpt") as "[Htxnmap Hpt]".
    rewrite insert_union_l.
    iFrame "∗ # %".
    iPureIntro.
    rewrite /valid_wrs dom_insert_L.
    set_solver.
  Qed.

  Theorem wp_Txn__Read txn tid key value rds γ τ  :
    {{{ own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key value }}}
      Txn__Read #txn #(LitString key)
    {{{ (ok : bool), RET (dbval_to_val (if ok then value else None), #ok);
        own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key value
    }}}.
  Proof.
    iIntros (Φ) "[Htxn Hpt] HΦ".
    wp_rec.

    (*@ func (txn *Txn) Read(key string) (tulip.Value, bool) {                  @*)
    (*@     vlocal, hit := txn.getwrs(key)                                      @*)
    (*@     if hit {                                                            @*)
    (*@         return vlocal, true                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Htxn".
    wp_apply (wp_Txn__getwrs with "Hwrs").
    iIntros (vlocal ok) "[Hwrs %Hv]".
    iDestruct (txnmap_lookup with "Htxnmap Hpt") as %Hvalue.
    wp_if_destruct.
    { (* Prove [vlocal = value]. *)
      apply (lookup_union_Some_l _ rds) in Hv.
      rewrite Hv in Hvalue.
      inv Hvalue.
      wp_pures.
      iApply ("HΦ" $! true).
      by iFrame "∗ # %".
    }
    clear Heqb ok.

    (*@     gid := KeyToGroup(key)                                              @*)
    (*@     gcoord := txn.gcoords[gid]                                          @*)
    (*@     v, ok := gcoord.Read(txn.ts, key)                                   @*)
    (*@                                                                         @*)
    wp_apply wp_KeyToGroup.
    iIntros (gid Hgid).
    iNamed "Hgcoords".
    wp_loadField.
    wp_apply (wp_MapGet with "Hgcoords").
    iIntros (gcoord ok) "[%Hget Hgcoords]".
    destruct ok; last first.
    { apply map_get_false in Hget as [Hget _].
      rewrite -not_elem_of_dom Hdomgcoords -Hgid in Hget.
      by pose proof (elem_of_key_to_group key).
    }
    apply map_get_true in Hget.
    iDestruct (big_sepM_lookup with "Hgcoordsabs") as "Hgcoordabs"; first apply Hget.
    iNamed "Htxn".
    wp_loadField.
    wp_apply (wp_GroupCoordinator__Read with "Hgcoordabs").
    iIntros (v ok) "#Hread".
    wp_pures.

    (*@     if !ok {                                                            @*)
    (*@         return tulip.Value{}, false                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct ok; wp_pures; last first.
    { iApply ("HΦ" $! false).
      iAssert (own_txn_gcoords txn γ)%I with "[$HgcoordsP $Hgcoords]" as "Hgcoords".
      { by iFrame "# %". }
      by iFrame "∗ # %".
    }
    rewrite Htsword.

    (*@     trusted_proph.ResolveRead(txn.proph, txn.ts, key)                   @*)
    (*@                                                                         @*)
    rewrite lookup_union_r in Hvalue; last apply Hv.
    iDestruct (big_sepM_lookup with "Hlnrz") as "Hhistl"; first apply Hvalue.
    do 2 wp_loadField.
    wp_apply wp_ResolveRead; first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    pose proof (elem_of_key_to_group key) as Hin.
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
    { apply Hin. }
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]".
    { apply Hin. }
    iDestruct (big_sepS_elem_of_acc _ _ key with "Hkeys") as "[Hkey HkeysC]".
    { apply elem_of_dom_2 in Hvalue. set_solver. }
    iMod (txnsys_inv_read with "Hread Hhistl Htxnsys Hgroup Hrg Hkey")
      as "(Htxnsys & Hgroup & Hrg & Hkey & %Heq)".
    { rewrite /valid_ts in Hvts. lia. }
    { by rewrite Hfuture. }
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iDestruct ("HkeysC" with "Hkey") as "Hkeys".
    rewrite Hfuture /=.
    iDestruct (txnsys_inv_merge_future with "Hproph Htxnsys") as "Htxnsys".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iIntros "!> _".
    wp_pures.
    subst value.

    (*@     return v, true                                                      @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! true).
    iAssert (own_txn_gcoords txn γ)%I with "[$HgcoordsP $Hgcoords]" as "Hgcoords".
    { by iFrame "# %". }
    by iFrame "∗ # %".
  Qed.

End program.
