From Perennial.program_proof.rsm.distx Require Import prelude.
From Perennial.program_proof.rsm.distx.program Require Import replica_group txnlog.
From Perennial.program_proof.rsm.distx.invariance Require Import
  linearize commit abort cancel preprepare read.
From Goose.github_com.mit_pdos.rsm Require Import distx.

Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

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

  (*@ type Txn struct {                                                       @*)
  (*@     // Transaction timestamp.                                           @*)
  (*@     ts   uint64                                                         @*)
  (*@     // Replica groups.                                                  @*)
  (*@     rgs  map[uint64]*ReplicaGroup                                       @*)
  (*@     // Buffered write-set.                                              @*)
  (*@     wrs  map[uint64]map[string]Value                                    @*)
  (*@     // Participant group of this transaction. Initialized in prepare time. @*)
  (*@     ptgs []uint64                                                       @*)
  (*@     // Global prophecy variable (for verification purpose).             @*)
  (*@     proph primitive.ProphId                                             @*)
  (*@ }                                                                       @*)
  Definition own_wrs (wrsP : loc) (wrs : dbmap) : iProp Σ :=
    ∃ (pwrsmP : gmap u64 loc) (pwrsm : gmap u64 dbmap),
      "HpwrsmP" ∷ own_map wrsP (DfracOwn 1) pwrsmP ∗
      "Hpwrsm"  ∷ ([∗ map] p; m ∈ pwrsmP; pwrsm, own_map p (DfracOwn 1) m) ∗
      "%Hwrsg"  ∷ ⌜map_Forall (λ g m, m = wrs_group g wrs) pwrsm⌝ ∗
      "%Hdomwrs" ∷ ⌜dom pwrsmP = gids_all⌝.

  Definition own_txn_wrs txn (wrs : dbmap) : iProp Σ :=
    ∃ (wrsP : loc),
      "HwrsP" ∷ txn ↦[Txn :: "wrs"] #wrsP ∗
      "Hwrs"  ∷ own_wrs wrsP wrs.

  Definition own_txn_rgs txn γ : iProp Σ :=
    ∃ (rgsP : loc) (rgs : gmap u64 loc),
      "HrgsP"    ∷ txn ↦[Txn :: "rgs"] #rgsP ∗
      "Hrgs"     ∷ own_map rgsP (DfracOwn 1) rgs ∗
      "#Hrgsabs" ∷ ([∗ map] g ↦ rg ∈ rgs, is_rg rg g γ) ∗
      "%Hdomrgs" ∷ ⌜dom rgs = gids_all⌝.

  Definition own_txn_ptgs txn (ptgs : list groupid) : iProp Σ :=
    ∃ (ptgsS : Slice.t),
      "HptgsS" ∷ txn ↦[Txn :: "ptgs"] (to_val ptgsS) ∗
      "Hptgs"  ∷ own_slice ptgsS uint64T (DfracOwn 1) ptgs ∗
      "%Hnd"   ∷ ⌜NoDup ptgs⌝.

  Definition own_txn_impl txn (tid : nat) (proph : proph_id) : iProp Σ :=
    ∃ (tsW : u64),
      "HtsW"     ∷ txn ↦[Txn :: "ts"] #tsW ∗
      "HprophP"  ∷ txn ↦[Txn :: "proph"] #proph ∗
      "%Htsword" ∷ ⌜uint.nat tsW = tid⌝.

  Definition own_txn_init txn tid γ : iProp Σ :=
    ∃ proph,
      "Htxn"  ∷ own_txn_impl txn tid proph ∗
      "Hwrs"  ∷ own_txn_wrs txn ∅ ∗
      "Hrgs"  ∷ own_txn_rgs txn γ ∗
      "Hptgs" ∷ own_txn_ptgs txn [] ∗
      "#Hinv" ∷ know_distx_inv γ proph ∗
      "%Hvts" ∷ ⌜valid_ts tid⌝.

  Definition own_txn_uninit txn γ : iProp Σ :=
    ∃ tid, own_txn_init txn tid γ.

  Definition own_txn txn tid rds γ τ : iProp Σ :=
    ∃ proph wrs,
      "Htxn"    ∷ own_txn_impl txn tid proph ∗
      "Hwrs"    ∷ own_txn_wrs txn wrs ∗
      "Hrgs"    ∷ own_txn_rgs txn γ ∗
      "Hptgs"   ∷ own_txn_ptgs txn [] ∗
      (* diff from [own_txn_init] *)
      "Htxnmap" ∷ txnmap_auth τ (wrs ∪ rds) ∗
      "#Hinv"   ∷ know_distx_inv γ proph ∗
      (* diff from [own_txn_init] *)
      "#Hlnrz"  ∷ ([∗ map] key ↦ value ∈ rds, hist_lnrz_at γ key (pred tid) value) ∗
      "%Hdomr"  ∷ ⌜dom rds ⊆ keys_all⌝ ∗
      (* diff from [own_txn_init] *)
      "%Hincl"  ∷ ⌜dom wrs ⊆ dom rds⌝ ∗
      "%Hvts"   ∷ ⌜valid_ts tid⌝ ∗
      (* diff from [own_txn_init] *)
      "%Hvwrs"  ∷ ⌜valid_wrs wrs⌝.

  Definition own_txn_stable txn tid rds wrs γ τ : iProp Σ :=
    ∃ proph,
      "Htxn"     ∷ own_txn_impl txn tid proph ∗
      "Hwrs"     ∷ own_txn_wrs txn wrs ∗
      "Hrgs"     ∷ own_txn_rgs txn γ ∗
      "Hptgs"    ∷ own_txn_ptgs txn [] ∗
      "Htxnmap"  ∷ txnmap_auth τ (wrs ∪ rds) ∗
      "#Hinv"    ∷ know_distx_inv γ proph ∗
      "#Hlnrz"   ∷ ([∗ map] key ↦ value ∈ rds, hist_lnrz_at γ key (pred tid) value) ∗
      "%Hdomr"  ∷ ⌜dom rds ⊆ keys_all⌝ ∗
      (* diff from [own_txn] and [wrs] is exposed *)
      "#Htxnwrs" ∷ txnwrs_receipt γ tid wrs ∗
      "%Hincl"   ∷ ⌜dom wrs ⊆ dom rds⌝ ∗
      "%Hvts"    ∷ ⌜valid_ts tid⌝ ∗
      "%Hvwrs"   ∷ ⌜valid_wrs wrs⌝.

  Definition own_txn_prepared txn tid rds wrs γ τ : iProp Σ :=
    ∃ proph ptgs,
      "Htxn"     ∷ own_txn_impl txn tid proph ∗
      "Hwrs"     ∷ own_txn_wrs txn wrs ∗
      "Hrgs"     ∷ own_txn_rgs txn γ ∗
      (* diff from [own_txn_stable] *)
      "Hptgs"    ∷ own_txn_ptgs txn ptgs ∗
      "Htxnmap"  ∷ txnmap_auth τ (wrs ∪ rds) ∗
      "#Hinv"    ∷ know_distx_inv γ proph ∗
      "#Hlnrz"   ∷ ([∗ map] key ↦ value ∈ rds, hist_lnrz_at γ key (pred tid) value) ∗
      "#Htxnwrs" ∷ txnwrs_receipt γ tid wrs ∗
      "%Hdomr"  ∷ ⌜dom rds ⊆ keys_all⌝ ∗
      "%Hincl"   ∷ ⌜dom wrs ⊆ dom rds⌝ ∗
      "%Hvts"    ∷ ⌜valid_ts tid⌝ ∗
      "%Hvwrs"   ∷ ⌜valid_wrs wrs⌝ ∗
      (* diff from [own_txn_stable] *)
      "%Hptgs"   ∷ ⌜list_to_set ptgs = ptgroups (dom wrs)⌝.

  Lemma wp_ResolveRead γ p (tid : u64) (key : byte_string) (ts : nat) :
    ⊢ {{{ ⌜uint.nat tid = ts⌝ }}}
    <<< ∀∀ acs, txn_proph γ p acs >>>
      ResolveRead #p #tid #(LitString key) @ ∅
    <<< ∃ acs', ⌜acs = ActRead ts key :: acs'⌝ ∗ txn_proph γ p acs' >>>
    {{{ RET #(); True }}}.
  Admitted.

  Lemma wp_ResolveAbort γ p (tid : u64) (ts : nat) :
    ⊢ {{{ ⌜uint.nat tid = ts⌝ }}}
    <<< ∀∀ acs, txn_proph γ p acs >>>
      ResolveAbort #p #tid @ ∅
    <<< ∃ acs', ⌜acs = ActAbort ts :: acs'⌝ ∗ txn_proph γ p acs' >>>
    {{{ RET #(); True }}}.
  Admitted.

  Lemma wp_ResolveCommit
    γ p (tid : u64) (ts : nat) (wrsP : loc) (wrs : dbmap) :
    ⊢ {{{ ⌜uint.nat tid = ts⌝ ∗ own_wrs wrsP wrs }}}
    <<< ∀∀ acs, txn_proph γ p acs >>>
      ResolveCommit #p #tid #wrsP @ ∅
    <<< ∃ acs', ⌜acs = ActCommit ts wrs :: acs'⌝ ∗ txn_proph γ p acs' >>>
    {{{ RET #(); own_wrs wrsP wrs }}}.
  Admitted.

  Theorem wp_KeyToGroup (key : byte_string) :
    {{{ True }}}
      KeyToGroup #(LitString key)
    {{{ (gid : u64), RET #gid; ⌜key_to_group key = gid⌝ }}}.
  Proof.
    (*@ func KeyToGroup(key string) uint64 {                                    @*)
    (*@     // TODO                                                             @*)
    (*@     return 0                                                            @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__getwrs (txn : loc) (key : byte_string) wrs :
    {{{ own_txn_wrs txn wrs }}}
      Txn__getwrs #txn #(LitString key)
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok);
        own_txn_wrs txn wrs ∗ ⌜wrs !! key = if ok then Some v else None⌝
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

  Theorem wp_Txn__setwrs (txn : loc) (key : byte_string) (value : dbval) wrs :
    {{{ own_txn_wrs txn wrs }}}
      Txn__setwrs #txn #(LitString key) (dbval_to_val value)
    {{{ RET #(); own_txn_wrs txn (<[key := value]> wrs) }}}.
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
    wp_pures.
    iApply "HΦ".
    set pwrs' := <[key := value]> pwrs.
    iAssert ([∗ map] p; m ∈ pwrsmP; <[gid := pwrs']> pwrsm, own_map p (DfracOwn 1) m)%I
      with "[Hpwrsm Hpwrs]" as "Hpwrsm".
    { iDestruct (big_sepM2_insert_2 (λ k p m, own_map p (DfracOwn 1) m) _ _ gid with "Hpwrs Hpwrsm")
        as "Hpwrsm".
      rewrite insert_delete_id; last apply Hget.
      rewrite insert_delete_eq.
      done.
    }
    iFrame "∗ %".
    iPureIntro.
    intros g m Hgm.
    destruct (decide (gid = g)) as [-> | Hne].
    - rewrite lookup_insert_eq in Hgm. inv Hgm.
      specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
      by rewrite Hwrsg wrs_group_insert.
    - rewrite lookup_insert_ne in Hgm; last done.
      specialize (Hwrsg _ _ Hgm). simpl in Hwrsg.
      subst m.
      by rewrite wrs_group_insert_ne; last rewrite Hgid.
  Qed.

  Theorem wp_Txn__Read txn tid key value rds γ τ :
    {{{ own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key value }}}
      Txn__Read #txn #(LitString key)
    {{{ RET (dbval_to_val value); own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key value }}}.
  Proof.
    iIntros (Φ) "[Htxn Hpt] HΦ".
    wp_rec.

    (*@ func (txn *Txn) Read(key string) Value {                                @*)
    (*@     vlocal, ok := txn.getwrs(key)                                       @*)
    (*@     if ok {                                                             @*)
    (*@         return vlocal                                                   @*)
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
      iApply "HΦ".
      by iFrame "∗ # %".
    }
    clear Heqb ok.

    (*@     gid := KeyToGroup(key)                                              @*)
    (*@     rg := txn.rgs[gid]                                                  @*)
    (*@                                                                         @*)
    wp_apply wp_KeyToGroup.
    iIntros (gid Hgid).
    iNamed "Hrgs".
    wp_loadField.
    wp_apply (wp_MapGet with "Hrgs").
    iIntros (rg ok) "[%Hget Hrgs]".
    destruct ok; last first.
    { apply map_get_false in Hget as [Hget _].
      rewrite -not_elem_of_dom Hdomrgs -Hgid in Hget.
      by pose proof (elem_of_key_to_group key).
    }
    apply map_get_true in Hget.
    iDestruct (big_sepM_lookup with "Hrgsabs") as "Hrgabs"; first apply Hget.

    (*@     v := rg.Read(txn.ts, key)                                           @*)
    (*@                                                                         @*)
    iNamed "Htxn".
    rewrite lookup_union_r in Hvalue; last apply Hv.
    wp_loadField.
    wp_apply (wp_ReplicaGroup__Read with "Hrgabs").
    { rewrite /safe_read Htsword /valid_key.
      apply elem_of_dom_2 in Hvalue.
      by assert (Hin : key ∈ keys_all) by set_solver.
    }
    iIntros (v) "#Hhistr".
    rewrite Htsword.

    (*@     ResolveRead(txn.proph, txn.ts, key)                                 @*)
    (*@     return v                                                            @*)
    (*@ }                                                                       @*)
    iDestruct (big_sepM_lookup with "Hlnrz") as "Hhistl"; first apply Hvalue.
    (* Prove [vlocal = value]. *)
    do 2 wp_loadField.
    wp_apply wp_ResolveRead; first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iDestruct (big_sepS_elem_of_acc _ _ key with "Hkeys") as "[Hkey HkeysC]".
    { apply elem_of_dom_2 in Hvalue. set_solver. }
    iMod (txnsys_inv_read with "Hhistl Hhistr Htxnsys Hkey") as "(Htxnsys & Hkey & %Heq)".
    { rewrite /valid_ts in Hvts. lia. }
    { by rewrite Hfuture. }
    iDestruct ("HkeysC" with "Hkey") as "Hkeys".
    rewrite Hfuture /=.
    iDestruct (txnsys_inv_merge_future with "Hproph Htxnsys") as "Htxnsys".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups]") as "_".
    iIntros "!> _".
    wp_pures.
    subst value.
    iApply "HΦ".
    (* This additional step ensures iFrame below to pick the right resource to frame. *)
    iAssert (own_txn_rgs txn γ)%I with "[Hrgs HrgsP]" as "Hrgs".
    { iFrame "∗ # %". }
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Txn__Write txn tid key value rds γ τ :
    {{{ own_txn txn tid rds γ τ ∗ (∃ vprev, txnmap_ptsto τ key vprev) }}}
      Txn__Write #txn #(LitString key) #(LitString value)
    {{{ RET #(); own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key (Some value) }}}.
  Proof.
    iIntros (Φ) "[Htxn [%v Hpt]] HΦ".
    wp_rec.

    (*@ func (txn *Txn) Write(key string, value string) {                       @*)
    (*@     v := Value{                                                         @*)
    (*@         b : true,                                                       @*)
    (*@         s : value,                                                      @*)
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
    (*@     v := Value{                                                         @*)
    (*@         b : false,                                                      @*)
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

  Theorem wp_Txn__begin (txn : loc) γ :
    ⊢ {{{ own_txn_uninit txn γ }}}
      <<< ∀∀ (ts : nat), ts_auth γ ts >>>
        Txn__begin #txn @ ↑tsNS
      <<< ∃∃ (ts' : nat), ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
      {{{ RET #(); own_txn_init txn ts' γ }}}.
  Proof.
    (*@ func (txn *Txn) begin() {                                               @*)
    (*@     // TODO                                                             @*)
    (*@     // Ghost action: Linearize.                                         @*)
    (*@     txn.ts = GetTS()                                                    @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__setptgs txn wrs :
    {{{ own_txn_wrs txn wrs ∗ own_txn_ptgs txn [] }}}
      Txn__setptgs #txn
    {{{ RET #(); ∃ ptgs, own_txn_wrs txn wrs ∗ own_txn_ptgs txn ptgs ∗
                         ⌜list_to_set ptgs = ptgroups (dom wrs)⌝
    }}}.
  Proof using distx_ghostG0 heapGS0 Σ.
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
      ∃ (s : Slice.t) (ptgs : list groupid),
        "HptgsP" ∷ ptgsP ↦[slice.T uint64T] (to_val s) ∗
        "Hptgs"  ∷ own_slice s uint64T (DfracOwn 1) ptgs ∗
        "Hpwrsm" ∷ ([∗ map] p;m ∈ pwrsmP;pwrsm, own_map p (DfracOwn 1) m) ∗
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
      (* FIXME: not sure if word is supposed to solve this immediately *)
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

  Definition groups_txnst γ (ts : nat) (st : txnst) : iProp Σ :=
    match st with
    | StPrepared _ => (∃ m, all_prepared γ ts m)
    | StCommitted => (∃ m, txnres_cmt γ ts m)
    | StAborted => txnres_abt γ ts
    end.

  Theorem wp_slicem (mP : loc) dq (m : dbmap) :
    {{{ own_map mP dq m }}}
      slicem #mP
    {{{ (s : Slice.t), RET (to_val s); ∃ l, own_map mP dq m ∗ own_dbmap_in_slice s l m }}}.
  Proof.
    (*@ func slicem(m map[string]Value) []WriteEntry {                          @*)
    (*@     // TODO                                                             @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__prepare txn tid rds wrs γ τ :
    {{{ own_txn_stable txn tid rds wrs γ τ }}}
      Txn__prepare #txn
    {{{ (status : txnst), RET #(txnst_to_u64 status);
        own_txn_prepared txn tid rds wrs γ τ ∗ groups_txnst γ tid status
    }}}.
  Proof.
    iIntros (Φ) "Htxn HΦ".
    wp_rec.

    (*@ func (txn *Txn) prepare() uint64 {                                      @*)
    (*@     var status = TXN_PREPARED                                           @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first by auto.
    iIntros (statusP) "HstatusP".
    wp_pures.

    (*@     txn.setptgs()                                                       @*)
    (*@                                                                         @*)
    iNamed "Htxn".
    wp_apply (wp_Txn__setptgs with "[$Hwrs $Hptgs]").
    iIntros "(%ptgs & Hwrs & Hptgs & %Hptgs)".

    (*@     var i uint64 = 0                                                    @*)
    (*@     for i < uint64(len(txn.ptgs)) {                                     @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first by auto.
    iIntros (iP) "HiP".
    set prepared := λ st, match st with
                          | StPrepared _ => True
                          | _ => False
                          end.
    set P := (λ (cont : bool), ∃ (i : u64) (status : txnst),
      let ptgs' := take (uint.nat i) ptgs in
      "HiP"      ∷ iP ↦[uint64T] #i ∗
      "HstatusP" ∷ statusP ↦[uint64T] #(txnst_to_u64 status) ∗
      "Htxn"     ∷ own_txn_impl txn tid proph ∗
      "Hrgs"     ∷ own_txn_rgs txn γ ∗
      "Hwrs"     ∷ own_txn_wrs txn wrs ∗
      "Hptgs"    ∷ own_txn_ptgs txn ptgs ∗
      "#Hpreps"  ∷ ([∗ list] g ∈ ptgs', txnprep_prep γ g tid) ∗
      "Htoken"   ∷ if cont then ⌜prepared status⌝ else groups_txnst γ tid status)%I.
    wp_apply (wp_forBreak_cond P with "[] [-HΦ Htxnmap]"); last first; first 1 last.
    { (* Loop entry. *)
      subst P. simpl.
      (* [∅] here is just a placeholder. *)
      iExists _, (StPrepared ∅).
      iFrame "∗ # %".
      by rewrite uint_nat_W64_0 take_0 big_sepL_nil.
    }
    { (* Loop body. *)
      clear Φ. iIntros (Φ) "!> HP HΦ". iNamed "HP".
      wp_load.
      iNamed "Hptgs".
      wp_loadField.
      wp_apply (wp_slice_len).
      iDestruct (own_slice_sz with "Hptgs") as %Hlen.
      wp_if_destruct; last first.
      { (* Exit from the loop condition. *)
        iApply "HΦ".
        iFrame "∗ # %".
        destruct status; [simpl | done | done].
        rewrite take_ge; last lia.
        rewrite -big_sepS_list_to_set; last apply Hnd.
        rewrite Hptgs.
        by iFrame "#".
      }
      wp_pures.

      (*@         gid := txn.ptgs[i]                                              @*)
      (*@         rg := txn.rgs[gid]                                              @*)
      (*@         pwrs := txn.wrs[gid]                                            @*)
      (*@                                                                         @*)
      wp_load. wp_loadField.
      iDestruct (own_slice_small_acc with "Hptgs") as "[Hptgs HptgsC]".
      destruct (lookup_lt_is_Some_2 ptgs (uint.nat i)) as [gid Hgid]; first word.
      wp_apply (wp_SliceGet with "[$Hptgs]"); first done.
      iIntros "Hptgs".
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrs)) as Hdom.
        apply list_elem_of_lookup_2 in Hgid.
        set_solver.
      }
      iNamed "Hrgs".
      wp_loadField.
      wp_apply (wp_MapGet with "Hrgs").
      iIntros (rgP ok) "[%Hgetrgs Hrgs]".
      destruct ok; last first.
      { apply map_get_false in Hgetrgs as [Hnotin _].
        by rewrite -not_elem_of_dom Hdomrgs in Hnotin.
      }
      apply map_get_true in Hgetrgs.
      iDestruct (big_sepM_lookup with "Hrgsabs") as "#Hrgabs"; first apply Hgetrgs.
      wp_pures.
      iNamed "Hwrs". iNamed "Hwrs".
      wp_loadField.
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

      (*@         status = rg.Prepare(txn.ts, slicem(pwrs))                       @*)
      (*@                                                                         @*)
      wp_apply (wp_slicem with "Hpwrs").
      iIntros (pwrsS) "(%pwrsL & Hpwrs & HpwrsS)".
      iNamed "Htxn".
      wp_loadField.
      wp_apply (wp_ReplicaGroup__Prepare with "[] Hrgabs HpwrsS").
      { rewrite Htsword.
        iFrame "Htxnwrs".
        iPureIntro.
        assert (Hwg : pwrs = wrs_group gid wrs).
        { by apply Hwrsg. }
        assert (Hinptgs : gid ∈ ptgroups (dom wrs)).
        { rewrite -Hptgs elem_of_list_to_set list_elem_of_lookup. by eauto. }
        assert (Hne : pwrs ≠ ∅).
        { rewrite elem_of_ptgroups -wrs_group_keys_group_dom dom_empty_iff_L in Hinptgs.
          by rewrite Hwg.
        }
        done.
      }
      iIntros (st) "Hst".
      wp_store.
      rename Heqb into Hinbound.
      iDestruct ("HptgsC" with "Hptgs") as "Hptgs".
      iDestruct ("HpwrsmC" with "Hpwrs") as "Hpwrsm".
      (* This additional step ensures iFrame below to pick the right resource to frame. *)
      iAssert (own_txn_rgs txn γ)%I with "[Hrgs HrgsP]" as "Hrgs".
      { iFrame "∗ # %". }

      (*@         if status != TXN_PREPARED {                                     @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_load.
      wp_if_destruct.
      { iApply "HΦ".
        subst P. simpl.
        iFrame "∗ # %".
        by destruct st; [| iFrame | iFrame].
      }

      (*@         i++                                                             @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_load. wp_store.
      destruct st as [m | |] eqn:Hst; [| done | done].
      simpl.
      iApply "HΦ".
      subst P. simpl.
      iFrame "HiP".
      iExists (StPrepared m).
      iFrame "∗ # %". simpl.
      rewrite uint_nat_word_add_S; last first.
      { clear -Hlen Hinbound. word. }
      rewrite (take_S_r _ _ _ Hgid) big_sepL_snoc.
      by iFrame "∗ #".
    }
    iIntros "HP".

    (*@     return status                                                       @*)
    (*@ }                                                                       @*)
    iNamed "HP". clear P.
    wp_load.
    iApply "HΦ".
    by iFrame "∗ # %".
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

  Theorem wp_Txn__resetwrs (txn : loc) wrs :
    {{{ own_txn_wrs txn wrs }}}
      Txn__resetwrs #txn
    {{{ RET #(); own_txn_wrs txn ∅ }}}.
  Proof.
    iIntros (Φ) "Hwrs HΦ".
    wp_rec.

    (*@ func (txn *Txn) resetwrs() {                                            @*)
    (*@     wrs := make(map[uint64]map[string]Value)                            @*)
    (*@     for gid := range(txn.wrs) {                                         @*)
    (*@         wrs[gid] = make(map[string]Value)                               @*)
    (*@     }                                                                   @*)
    (*@     txn.wrs = wrs                                                       @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewMap.
    iIntros (wrsP') "HpwrsmP'".
    do 2 iNamed "Hwrs".
    iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom.
    wp_loadField.
    set P := (λ (mx : gmap u64 loc),
      let em := gset_to_gmap (∅ : dbmap) (dom mx) in
      ∃ (pwrsmP' : gmap u64 loc),
        "HpwrsmP'" ∷ own_map wrsP' (DfracOwn 1) pwrsmP' ∗
        "Hpwrsm'" ∷ ([∗ map] p;m ∈ pwrsmP';em, own_map p (DfracOwn 1) m))%I.
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

  Theorem wp_Txn__reset (txn : loc) wrs ptgs :
    {{{ own_txn_wrs txn wrs ∗ own_txn_ptgs txn ptgs }}}
      Txn__reset #txn
    {{{ RET #(); own_txn_wrs txn ∅ ∗ own_txn_ptgs txn [] }}}.
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
    txns_lnrz_receipt γ tid -∗
    all_prepared γ tid wrsphys -∗
    {{{ own_txn_prepared txn tid rds wrsphys γ τ ∗ txns_cmt_elem γ tid wrsproph }}}
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
    wp_apply (wp_ResolveCommit with "[$Hwrs]"); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iMod (txnsys_inv_commit with "Hlnrzed Hprep Htxnsys Hgroups Hkeys")
      as "(Htxnsys & Hgroups & Hkeys & #Hcmt)".
    { by rewrite Hfuture. }
    iAssert (⌜wrsphys = wrsproph⌝)%I as %Heq.
    { iNamed "Htxnsys".
      iDestruct (txnres_lookup with "Hresm Hcmt") as %Hwrsc.
      iDestruct (elem_of_committed_partitioned_tids with "Hpart") as %[Hnotinwc Hnotinwa].
      { by eauto. }
      iDestruct (txns_cmt_lookup with "Htidcs Htidc") as %Htidc.
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
    iMod ("HinvC" with "[Htxnsys Hkeys Hgroups]") as "_"; first by iFrame.
    iIntros "!> Hwrs".
    iAssert (own_txn_wrs txn wrsphys)%I with "[$HwrsP $Hwrs]" as "Hwrs".
    wp_pures.

    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         rg := txn.rgs[gid]                                              @*)
    (*@         rg.Commit(txn.ts)                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hptgs".
    wp_loadField.
    set P := (λ (_ : u64),
      "HtsW" ∷ txn ↦[Txn::"ts"] #tsW ∗
      "Hrgs" ∷ own_txn_rgs txn γ)%I.
    iDestruct (own_slice_small_acc with "Hptgs") as "[Hptgs HptgsC]".
    wp_apply (wp_forSlice P with "[] [$Hptgs $HtsW $Hrgs]").
    { (* Loop body. *)
      clear Φ.
      iIntros (i gid Φ) "!> (HP & %Hinbound & %Hgid) HΦ".
      iNamed "HP".
      iNamed "Hrgs".
      wp_loadField.
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrsphys)) as Hdom.
        apply list_elem_of_lookup_2 in Hgid.
        clear -Hdom Hgid Hptgs.
        set_solver.
      }
      wp_apply (wp_MapGet with "Hrgs").
      iIntros (rgP ok) "[%Hgetrgs Hrgs]".
      destruct ok; last first.
      { apply map_get_false in Hgetrgs as [Hnone _].
        by rewrite -not_elem_of_dom Hdomrgs in Hnone.
      }
      apply map_get_true in Hgetrgs.
      wp_loadField.
      iDestruct (big_sepM_lookup with "Hrgsabs") as "Hrgabs"; first apply Hgetrgs.
      wp_apply (wp_ReplicaGroup__Commit with "[] Hrgabs").
      { rewrite Htsword.
        iFrame "Hcmt".
        iPureIntro.
        assert (Hinptgs : gid ∈ ptgroups (dom wrsphys)).
        { rewrite -Hptgs elem_of_list_to_set list_elem_of_lookup. by eauto. }
        done.
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
    wp_apply (wp_Txn__reset with "[$Hwrs $Hptgs]").
    iIntros "[Hwrs Hptgs]".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Txn__commit_in_abort_future txn tid rds wrs γ τ :
    txns_lnrz_receipt γ tid -∗
    all_prepared γ tid wrs -∗
    {{{ own_txn_prepared txn tid rds wrs γ τ ∗ txns_abt_elem γ tid }}}
      Txn__commit #txn
    {{{ RET #(); False }}}.
  Proof.
    iIntros "#Hlnrzed #Hprep" (Φ) "!> [Htxn Hwabt] HΦ".
    wp_rec.

    (*@ func (txn *Txn) commit() {                                              @*)
    (*@     ResolveCommit(txn.proph, txn.ts, txn.wrs)                           @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn". iNamed "Hwrs".
    do 3 wp_loadField.
    wp_apply (wp_ResolveCommit with "[$Hwrs]"); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iMod (txnsys_inv_commit with "Hlnrzed Hprep Htxnsys Hgroups Hkeys")
      as "(Htxnsys & Hgroups & Hkeys & Hcmt)".
    { by rewrite Hfuture. }
    (* Obtain contradiction. *)
    iNamed "Htxnsys".
    iDestruct (txnres_lookup with "Hresm Hcmt") as %Hcmt.
    iDestruct (txns_abt_elem_of with "Htidas Hwabt") as %Hwabt.
    rewrite -Htidas in Hwabt.
    iDestruct (elem_of_tmodas_partitioned_tids with "Hpart") as %[_ Hnotin].
    { apply Hwabt. }
    by specialize (Hnotin _ Hcmt).

    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         rg := txn.rgs[gid]                                              @*)
    (*@         rg.Commit(txn.ts)                                               @*)
    (*@     }                                                                   @*)
    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
  Qed.

  Theorem wp_Txn__abort txn tid rds wrs γ τ :
    txnres_abt γ tid -∗
    {{{ own_txn_prepared txn tid rds wrs γ τ ∗ txns_abt_elem γ tid }}}
      Txn__abort #txn
    {{{ RET #(); own_txn_uninit txn γ }}}.
  Proof.
    iIntros "#Habt" (Φ) "!> [Htxn Hwabt] HΦ".
    wp_rec.

    (*@ func (txn *Txn) abort() {                                               @*)
    (*@     ResolveAbort(txn.proph, txn.ts)                                     @*)
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
    iMod ("HinvC" with "[Htxnsys Hkeys Hgroups]") as "_"; first by iFrame.
    iIntros "!> _".
    wp_pures.

    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         rg := txn.rgs[gid]                                              @*)
    (*@         rg.Abort(txn.ts)                                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hptgs".
    wp_loadField.
    set P := (λ (_ : u64),
      "HtsW" ∷ txn ↦[Txn::"ts"] #tsW ∗
      "Hrgs" ∷ own_txn_rgs txn γ)%I.
    iDestruct (own_slice_small_acc with "Hptgs") as "[Hptgs HptgsC]".
    wp_apply (wp_forSlice P with "[] [$Hptgs $HtsW $Hrgs]").
    { (* Loop body. *)
      clear Φ.
      iIntros (i gid Φ) "!> (HP & %Hinbound & %Hgid) HΦ".
      iNamed "HP".
      iNamed "Hrgs".
      wp_loadField.
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrs)) as Hdom.
        apply list_elem_of_lookup_2 in Hgid.
        clear -Hdom Hgid Hptgs.
        set_solver.
      }
      wp_apply (wp_MapGet with "Hrgs").
      iIntros (rgP ok) "[%Hgetrgs Hrgs]".
      destruct ok; last first.
      { apply map_get_false in Hgetrgs as [Hnone _].
        by rewrite -not_elem_of_dom Hdomrgs in Hnone.
      }
      apply map_get_true in Hgetrgs.
      wp_loadField.
      iDestruct (big_sepM_lookup with "Hrgsabs") as "Hrgabs"; first apply Hgetrgs.
      wp_apply (wp_ReplicaGroup__Abort with "[] Hrgabs").
      { rewrite Htsword. by iFrame "Habt". }
      iApply "HΦ".
      iFrame "∗ # %".
    }
    iIntros "[HP Hptgs]".
    iNamed "HP". clear P.
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
    txnres_abt γ tid -∗
    {{{ own_txn_prepared txn tid rds wrsphys γ τ ∗ txns_cmt_elem γ tid wrsproph }}}
      Txn__abort #txn
    {{{ RET #(); False }}}.
  Proof.
    iIntros "#Habt" (Φ) "!> [Htxn Htidc] HΦ".
    wp_rec.

    (*@ func (txn *Txn) abort() {                                               @*)
    (*@     ResolveAbort(txn.proph, txn.ts)                                     @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn".
    do 2 wp_loadField.
    wp_apply (wp_ResolveAbort); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO". iNamed "Htxnsys".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    (* Prove [tid] must not have committed. *)
    iDestruct (txnres_lookup with "Hresm Habt") as %Habt.
    iDestruct (txns_cmt_lookup with "Htidcs Htidc") as %Htidc.
    specialize (Htidcs _ _ Htidc). simpl in Htidcs.
    destruct Htidcs as [Hwc | Hcmt]; last first.
    { by rewrite Hcmt in Habt. }
    specialize (Hcf _ _ Hwc). simpl in Hcf.
    destruct Hcf as (lp & ls & Hfc & _).
    assert (Hhead : head_abort future tid).
    { by rewrite Hfuture. }
    destruct (first_commit_head_abort _ _ _ _ _ Hfc Hhead) as [].

    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         rg := txn.rgs[gid]                                              @*)
    (*@         rg.Abort(txn.ts)                                                @*)
    (*@     }                                                                   @*)
    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
  Qed.

  Theorem wp_Txn__cancel txn tid rds γ τ :
    {{{ own_txn txn tid rds γ τ ∗ txns_abt_elem γ tid ∗ txnwrs_excl γ tid }}}
      Txn__cancel #txn
    {{{ RET #(); own_txn_uninit txn γ }}}.
  Proof.
    iIntros (Φ) "(Htxn & Habt & Hwrsexcl) HΦ".
    wp_rec.

    (*@ func (txn *Txn) cancel() {                                              @*)
    (*@     ResolveAbort(txn.proph, txn.ts)                                     @*)
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
    iMod ("HinvC" with "[Htxnsys Hkeys Hgroups]") as "_"; first by iFrame.
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
    {{{ own_txn txn tid rds γ τ ∗ (∃ m, txns_cmt_elem γ tid m) ∗ txnwrs_excl γ tid }}}
      Txn__cancel #txn
    {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "(Htxn & [%m Htidc] & Hwrsexcl) HΦ".
    wp_rec.

    (*@ func (txn *Txn) cancel() {                                              @*)
    (*@     ResolveAbort(txn.proph, txn.ts)                                     @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn".
    do 2 wp_loadField.
    wp_apply (wp_ResolveAbort); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iNamed "Htxnsys".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    (* Obtain [tmods !! tid = Some m]. *)
    iDestruct (txns_cmt_lookup with "Htidcs Htidc") as %Htidc.
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
      by iDestruct (txnwrs_frag_agree with "Hwrsexcl Hwrsrcpt") as %Hcontra.
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

  Theorem wp_Txn__Run
    txn (body : val)
    (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
    (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ) γ :
    (∀ r w, (Decision (Q r w))) ->
    ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, body_spec body txn tid r P Q Rc Ra γ τ) }}}
      <<< ∀∀ (r : dbmap), ⌜P r ∧ dom r ⊆ keys_all⌝ ∗ db_ptstos γ r >>>
        Txn__Run #txn body @ ↑sysNS
      <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q r w⌝ ∗ db_ptstos γ w else db_ptstos γ r >>>
      {{{ RET #ok; own_txn_uninit txn γ ∗ if ok then Rc r w else Ra r }}}.
  Proof.
    iIntros (Hdec) "!>".
    iIntros (Φ) "[Htxn Hbody] HAU".
    wp_rec. wp_pures.

    (*@ func (txn *Txn) Run(body func(txn *Txn) bool) bool {                    @*)
    (*@     txn.begin()                                                         @*)
    (*@                                                                         @*)
    iNamed "Htxn".
    wp_apply (wp_Txn__begin with "[-Hbody HAU]").
    { iFrame "∗ # %". }
    clear Hvts tid.
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
    iDestruct (ts_witness with "Hts") as "#Htidlb".

    pose proof (peek_spec future tid) as Hpeek.
    set form := peek _ _ in Hpeek.
    set Qr := λ m, Q rds (m ∪ rds) ∧ dom m ⊆ dom rds.
    destruct (decide (incorrect_fcc Qr form)) as [Hifcc | HQ].
    { (* Case: Abort branch. *)
      iMod (txnsys_inv_linearize_abort form Q with "Htidlb Hdbpts Htxnsys Hkeys")
        as "(Hdbpts & Htxnsys & Hkeys & Htida & Hwrsexcl & #HQ & #Hlnrzs & #Hlnrzed)".
      { apply Hdomr. }
      { apply Htidgt. }
      { apply Hpeek. }
      { done. }
      (* Choose the will-abort branch. Use [∅] as placeholder. *)
      iMod ("HAUC" $! false ∅ with "Hdbpts") as "HΦ".
      iMod "Hclose" as "_".
      iMod ("HinvC" with "[Hts Htxnsys Hkeys Hgroups]") as "_".
      { iNamed "Htxnsys". iFrame "∗ # %". }
      (* Allocate transaction local view [txnmap_ptstos τ r]. *)
      iMod (txnmap_alloc rds) as (τ) "[Htxnmap Htxnpts]".
      iIntros "!> Htxn".
      iAssert (own_txn txn tid rds γ τ)%I with "[Htxn Htxnmap]" as "Htxn".
      { iClear "Hinv". iNamed "Htxn".
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
        iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups]") as "_".
        by iFrame "∗ # %".
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
        iNamed "HinvO". iNamed "Htxnsys".
        iDestruct (txnres_lookup with "Hresm Hcmt") as %Hcmt.
        iDestruct (txns_abt_elem_of with "Htidas Htida") as %Hwabt.
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
      destruct status as [m | |]; [| done | done]. simpl. clear Hstatusnc Hstatusna m.
      iDestruct "Hstatus" as (wrs) "#Hprep".
      iAssert (⌜wrst = wrs⌝)%I as %->.
      { iClear "Hinv". iNamed "Htxn".
        iDestruct "Hprep" as "[#Hwrsrcpt _]".
        by iDestruct (txnwrs_receipt_agree with "Hwrsrcpt Htxnwrs") as %?.
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
        as "(Hdbpts & Htxnsys & Hkeys & Htidc & Hwrsexcl & #HQ & #Hlnrzs & #Hlnrzed)".
      { apply Hdomwrs. }
      { apply Hdomr. }
      { apply Htidgt. }
      { apply Hpeek. }
      (* Choose the will-commit branch. *)
      iMod ("HAUC" $! true (wrs ∪ rds) with "[$Hdbpts]") as "HΦ"; first done.
      iMod "Hclose" as "_".
      iMod ("HinvC" with "[Hts Htxnsys Hkeys Hgroups]") as "_".
      { iNamed "Htxnsys". iFrame "∗ # %". }
      iClear "Hinv". clear proph.
      (* Allocate transaction local view [txnmap_ptstos τ r]. *)
      iMod (txnmap_alloc rds) as (τ) "[Htxnmap Htxnpts]".
      iIntros "!> Htxn".
      iAssert (own_txn txn tid rds γ τ)%I with "[Htxn Htxnmap]" as "Htxn".
      { iNamed "Htxn".
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
      { iDestruct "Htxn" as (p wrst) "Htxn". iNamed "Htxn".
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
        iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups]") as "_".
        by iFrame "∗ # %".
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
        iAssert (|={⊤}=> txns_cmt_elem γ tid wrs ∗ ⌜wrsc = wrs ∧ wrst = wrs⌝)%I
          with "[Htidc]" as "Htidc".
        { iInv "Hinv" as "> HinvO" "HinvC".
          iNamed "HinvO". iNamed "Htxnsys".
          iDestruct (txnres_lookup with "Hresm Hwrsc") as %Hwrsc.
          iDestruct (elem_of_committed_partitioned_tids with "Hpart") as %[Hnotinwc Hnotinwa].
          { by eauto. }
          iDestruct (txns_cmt_lookup with "Htidcs Htidc") as %Htidc.
          apply Htidcs in Htidc.
          (* Prove [resm !! tid = Some (ResCommitted wrs)]. *)
          destruct Htidc as [Htmodcs | Hresm].
          { by rewrite not_elem_of_dom Htmodcs in Hnotinwc. }
          rewrite Hresm in Hwrsc. symmetry in Hwrsc. inv Hwrsc.
          iDestruct (big_sepM_lookup with "Hvr") as "Hr"; first apply Hresm.
          iDestruct "Hr" as "[Hrcp _]".
          iDestruct (txnwrs_receipt_agree with "Hrcp Htxnwrs") as %->.
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
      destruct status as [m | |] eqn:Hstatus; [| done | done].
      simpl. clear Hstatus Hstatusnc Hstatusna m.
      iDestruct "Hstatus" as (wrsc) "#Hprep".
      iAssert (⌜wrsc = wrst⌝)%I as %->.
      { iNamed "Htxn".
        iDestruct "Hprep" as "[Hwrsrcpt _]".
        by iDestruct (txnwrs_receipt_agree with "Htxnwrs Hwrsrcpt") as %?.
      }
      wp_apply (wp_Txn__commit with "Hlnrzed Hprep [Htxn Htidc]").
      { iFrame "∗ #". }
      iIntros "[Htxn %Heq]". subst wrst.
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
  Qed.

End program.
