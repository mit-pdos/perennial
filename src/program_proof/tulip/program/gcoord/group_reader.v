From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import quorum.
From Perennial.program_proof.tulip.invariance Require Import read.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type GroupReader struct {                                               @*)
  (*@     // Number of replicas. Read-only.                                   @*)
  (*@     nrps   uint64                                                       @*)
  (*@     // Cached read set. Exists for performance reason; could have an interface @*)
  (*@     // to create a transaction that does not cache reads.               @*)
  (*@     valuem map[string]tulip.Value                                       @*)
  (*@     // Versions responded by each replica for each key. Instead of using a @*)
  (*@     // single map[uint64]Version for the current key being read, this design allows @*)
  (*@     // supporting more sophisticated "async-read" in future.            @*)
  (*@     qreadm map[string]map[uint64]tulip.Version                          @*)
  (*@ }                                                                       @*)
  Definition own_greader_valuem
    (grd : loc) (valuem : gmap dbkey dbval) (ts : nat) γ : iProp Σ :=
    ∃ (valuemP : loc),
      "HvaluemP" ∷ grd ↦[GroupReader :: "valuem"] #valuemP ∗
      "Hvaluem"  ∷ own_map valuemP (DfracOwn 1) valuem ∗
      "#Hfinal"  ∷ ([∗ map] k ↦ v ∈ valuem, fast_or_quorum_read γ k ts v).

  Definition own_greader_qreadm
    (grd : loc) (qreadm : gmap dbkey (gmap u64 (u64 * dbval))) (ts : nat) γ : iProp Σ :=
    ∃ (qreadmP : loc) (qreadmM : gmap dbkey loc) ,
      "HqreadmP" ∷ grd ↦[GroupReader :: "qreadm"] #qreadmP ∗
      "HqreadmM" ∷ own_map qreadmP (DfracOwn 1) qreadmM ∗
      "Hqreadm"  ∷ ([∗ map] k ↦ p; m ∈ qreadmM; qreadm, own_map p (DfracOwn 1) m) ∗
      "#Hqread"  ∷ ([∗ map] k ↦ m ∈ qreadm,
                      [∗ map] rid ↦ ver ∈ m, slow_read γ rid k (uint.nat ver.1) ts ver.2) ∗
      "%Hvrids"  ∷ ⌜map_Forall (λ _ m, dom m ⊆ rids_all) qreadm⌝.

  Definition own_greader_nrps (grd : loc) : iProp Σ :=
    ∃ (nrps : u64),
      "Hnrps"   ∷ grd ↦[GroupReader :: "nrps"] #nrps ∗
      "%Hnrps"  ∷ ⌜uint.nat nrps = size rids_all⌝.

  Definition own_greader (grd : loc) (ts : nat) γ : iProp Σ :=
    ∃ (valuem : gmap dbkey dbval) (qreadm : gmap dbkey (gmap u64 (u64 * dbval))),
      "Hvaluem" ∷ own_greader_valuem grd valuem ts γ ∗
      "Hqreadm" ∷ own_greader_qreadm grd qreadm ts γ ∗
      "Hnrps"   ∷ own_greader_nrps grd.

End repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupReader__cquorum (grd : loc) (n : u64) :
    {{{ own_greader_nrps grd }}}
      GroupReader__cquorum #grd #n
    {{{ RET #(bool_decide (size rids_all / 2 < uint.Z n)); own_greader_nrps grd }}}.
  Proof.
    iIntros (Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) cquorum(n uint64) bool {                        @*)
    (*@     return quorum.ClassicQuorum(grd.nrps) <= n                          @*)
    (*@ }                                                                       @*)
    iNamed "Hgrd".
    wp_loadField.
    wp_apply wp_ClassicQuorum.
    iIntros (x Hx).
    wp_pures.
    case_bool_decide as Hc1.
    { case_bool_decide as Hc2; last word.
      iApply "HΦ". by iFrame "∗ %".
    }
    { case_bool_decide as Hc2; first word.
      iApply "HΦ". by iFrame "∗ %".
    }
  Qed.

  Theorem wp_GroupReader__pickLatestValue (grd : loc) (key : string) qreadm verm ts γ :
    qreadm !! key = Some verm ->
    cquorum_size rids_all (dom verm) ->
    {{{ own_greader_qreadm grd qreadm ts γ }}}
      GroupReader__pickLatestValue #grd #(LitString key)
    {{{ (value : dbval), RET (dbval_to_val value); 
        own_greader_qreadm grd qreadm ts γ ∗ quorum_read γ key ts value
    }}}.
  Proof.
    iIntros (Hqread Hqsize Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) pickLatestValue(key string) tulip.Value {       @*)
    (*@     var lts uint64                                                      @*)
    (*@     var value tulip.Value                                               @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first done.
    iIntros (ltsP) "HltsP".
    wp_apply wp_ref_of_zero; first done.
    iIntros (valueP) "HvalueP".

    (*@     verm := grd.qreadm[key]                                             @*)
    (*@                                                                         @*)
    iNamed "Hgrd".
    wp_loadField.
    wp_apply (wp_MapGet with "HqreadmM").
    iIntros (vermP ok) "[%Hok HqreadmM]".
    wp_pures.
    destruct ok; last first.
    { iDestruct (big_sepM2_dom with "Hqreadm") as %Hdomqreadm.
      apply map_get_false in Hok as [Hnone _].
      rewrite -not_elem_of_dom Hdomqreadm in Hnone.
      by apply elem_of_dom_2 in Hqread.
    }
    apply map_get_true in Hok.
    iDestruct (big_sepM2_lookup_acc with "Hqreadm") as "[Hverm HqreadmC]".
    { apply Hok. }
    { apply Hqread. }

    (*@     for _, ver := range(verm) {                                         @*)
    (*@         if lts <= ver.Timestamp {                                       @*)
    (*@             value = ver.Value                                           @*)
    (*@             lts = ver.Timestamp                                         @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    set P := (λ (mx : gmap u64 (u64 * dbval)),
                ∃ (lts : u64) (value : dbval),
                  "HltsP"     ∷ ltsP ↦[uint64T] #lts ∗
                  "HvalueP"   ∷ valueP ↦[boolT * (stringT * unitT)%ht] (dbval_to_val value) ∗
                  "%Hlargest" ∷ ⌜map_Forall (λ _ x, uint.Z x.1 ≤ uint.Z lts) mx⌝ ∗
                  "%Hin"      ∷ ⌜if decide (mx = ∅)
                                 then lts = U64 0
                                 else map_Exists (λ _ x, x = (lts, value)) mx⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Hverm [HltsP HvalueP]").
    { iExists _, None. by iFrame. }
    { clear Φ.
      iIntros (mx rid [t v] Φ) "!> [HP %Hmx] HΦ".
      iNamed "HP".
      wp_load.
      wp_pures.
      case_bool_decide as Horder; wp_pures.
      { wp_apply (wp_StoreAt with "HvalueP").
        { destruct v; by auto. }
        iIntros "HvalueP".
        wp_store.
        iApply "HΦ".
        subst P.
        iFrame.
        iPureIntro.
        split.
        { intros rid' [t' v'] Hv'. simpl.
          destruct (decide (rid' = rid)) as [-> | Hne].
          { rewrite lookup_insert in Hv'. by inv Hv'. }
          rewrite lookup_insert_ne in Hv'; last done.
          specialize (Hlargest _ _ Hv'). simpl in Hlargest.
          clear -Hlargest Horder. lia.
        }
        { destruct (decide (<[rid:=(t, v)]> mx = ∅)) as [He | Hne].
          { by apply insert_non_empty in He. }
          by apply map_Exists_insert_2_1.
        }
      }
      iApply "HΦ".
      subst P.
      iFrame.
      iPureIntro.
      split.
      { apply map_Forall_insert_2; last done.
        simpl. lia.
      }
      { case_decide as Hmxe.
        { clear -Horder Hin. word. }
        case_decide as Hinsert.
        { by apply insert_non_empty in Hinsert. }
        destruct Hmx as [Hmx _].
        by apply map_Exists_insert_2_2.
      }
    }
    iIntros "[Hverm HP]".
    subst P. iNamed "HP".
    wp_pures.
    wp_load.

    (*@     return value                                                        @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iDestruct ("HqreadmC" with "Hverm") as "HqreadmC".
    iFrame "∗ # %".
    iDestruct (big_sepM_lookup with "Hqread") as "Hqreadkey"; first apply Hqread.
    case_decide as Hverm.
    { exfalso.
      rewrite -dom_empty_iff_L -size_empty_iff_L in Hverm.
      clear -Hqsize Hverm. rewrite /cquorum_size in Hqsize. lia.
    }
    destruct Hin as (rid & [t v] & Hvermrid & Htv).
    inv Htv.
    iDestruct (big_sepM_lookup with "Hqreadkey") as "Hlver"; first apply Hvermrid.
    iNamed "Hlver".
    iFrame "Hv %".
    iModIntro.
    iExists (dom verm).
    iSplit.
    { rewrite big_sepS_big_sepM.
      iApply (big_sepM_mono with "Hqreadkey").
      iIntros (r [t v] Htv).
      iNamed 1. simpl.
      iApply (read_promise_weaken_lb with "Hioa").
      specialize (Hlargest _ _ Htv). simpl in Hlargest.
      clear -Hlargest. lia.
    }
    iPureIntro.
    by specialize (Hvrids _ _ Hqread).
  Qed.

  Theorem wp_GroupReader__read (grd : loc) (key : string) valuem ts γ :
    {{{ own_greader_valuem grd valuem ts γ }}}
      GroupReader__read #grd #(LitString key)
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok); 
        own_greader_valuem grd valuem ts γ ∗
        if ok then fast_or_quorum_read γ key ts v else True
    }}}.
  Proof.
    iIntros (Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) read(key string) (tulip.Value, bool) {          @*)
    (*@     v, ok := grd.valuem[key]                                            @*)
    (*@     return v, ok                                                        @*)
    (*@ }                                                                       @*)
    iNamed "Hgrd".
    wp_loadField.
    wp_apply (wp_MapGet with "Hvaluem").
    iIntros (v ok) "[%Hok Hvaluem]".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ #".
    destruct ok; last done.
    apply map_get_true in Hok.
    by iApply (big_sepM_lookup with "Hfinal").
  Qed.

  Theorem wp_GroupReader__responded (grd : loc) (rid : u64) (key : string) ts γ :
    {{{ own_greader grd ts γ }}}
      GroupReader__responded #grd #rid #(LitString key)
    {{{ (responded : bool), RET #responded; own_greader grd ts γ }}}.
  Proof.
    iIntros (Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) responded(rid uint64, key string) bool {        @*)
    (*@     _, final := grd.valuem[key]                                         @*)
    (*@     if final {                                                          @*)
    (*@         // The final value is already determined.                       @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hgrd". iNamed "Hvaluem".
    wp_loadField.
    wp_apply (wp_MapGet with "Hvaluem").
    iIntros (v final) "[%Hfinal Hvaluem]".
    wp_pures.
    destruct final; wp_pures.
    { iApply "HΦ". by iFrame "∗ # %". }

    (*@     qread, ok := grd.qreadm[key]                                        @*)
    (*@     if !ok {                                                            @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hqreadm".
    wp_loadField.
    wp_apply (wp_MapGet with "HqreadmM").
    iIntros (qreadP ok) "[%Hok HqreadmM]".
    wp_pures.
    destruct ok; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ # %". }

    (*@     _, responded := qread[rid]                                          @*)
    (*@     if responded {                                                      @*)
    (*@         // The replica has already responded with its latest version.   @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    apply map_get_true in Hok.
    iDestruct (big_sepM2_dom with "Hqreadm") as %Hdomqreadm.
    assert (is_Some (qreadm !! key)) as [qread Hqread].
    { by rewrite -elem_of_dom -Hdomqreadm elem_of_dom. }
    iDestruct (big_sepM2_lookup_acc with "Hqreadm") as "[Hqr HqreadmC]".
    { apply Hok. }
    { apply Hqread. }
    wp_apply (wp_MapGet with "Hqr").
    clear Hfinal v.
    iIntros (v responded) "[%Hresponded Hqr]".
    wp_pures.
    iDestruct ("HqreadmC" with "Hqr") as "Hqreadm".
    by destruct responded; wp_pures; iApply "HΦ"; iFrame "∗ # %".
  Qed.

  Theorem wp_GroupReader__clearVersions (grd : loc) (key : string) qreadm ts γ :
    {{{ own_greader_qreadm grd qreadm ts γ }}}
      GroupReader__clearVersions #grd #(LitString key)
    {{{ RET #(); own_greader_qreadm grd (delete key qreadm) ts γ }}}.
  Proof.
    iIntros (Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) clearVersions(key string) {                     @*)
    (*@     delete(grd.qreadm, key)                                             @*)
    (*@ }                                                                       @*)
    iNamed "Hgrd".
    wp_loadField.
    wp_apply (wp_MapDelete with "HqreadmM").
    iIntros "HqreadmM".
    wp_pures.
    iDestruct (big_sepM2_dom with "Hqreadm") as %Hdomqreadm.
    iApply "HΦ".
    destruct (decide (key ∈ dom qreadm)) as [Hin | Hnotin]; last first.
    { apply not_elem_of_dom in Hnotin.
      rewrite delete_notin; last apply Hnotin.
      assert (Hnone : qreadmM !! key = None).
      { by rewrite -not_elem_of_dom Hdomqreadm not_elem_of_dom. }
      rewrite /map_del delete_notin; last apply Hnone.
      by iFrame "∗ # %".
    }
    assert (is_Some (qreadmM !! key)) as [p Hp].
    { by rewrite -elem_of_dom Hdomqreadm. }
    apply elem_of_dom in Hin as [m Hm].
    iDestruct (big_sepM2_delete with "Hqreadm") as "[_ Hqreadm]".
    { apply Hp. }
    { apply Hm. }
    iDestruct (big_sepM_delete with "Hqread") as "[_ Hqread']".
    { apply Hm. }
    iFrame "∗ # %".
    iPureIntro.
    by apply map_Forall_delete.
  Qed.

  Theorem wp_GroupReader__processReadResult
    grd (rid : u64) (key : string) (ver : u64 * dbval) ts γ :
    rid ∈ rids_all ->
    fast_or_slow_read γ rid key (uint.nat ver.1) ts ver.2 -∗
    {{{ own_greader grd ts γ }}}
      GroupReader__processReadResult #grd #rid #(LitString key) (u64_dbval_to_val ver)
    {{{ RET #(); own_greader grd ts γ }}}.
  Proof.
    iIntros (Hrid) "#Hfsread".
    iIntros (Φ) "!> Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) processReadResult(rid uint64, key string, ver tulip.Version) { @*)
    (*@     _, final := grd.valuem[key]                                         @*)
    (*@     if final {                                                          @*)
    (*@         // The final value is already determined.                       @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hgrd". iNamed "Hvaluem". iNamed "Hqreadm".
    wp_loadField.
    wp_apply (wp_MapGet with "Hvaluem").
    iIntros (v final) "[%Hfinal Hvaluem]".
    wp_pures.
    destruct final; wp_pures.
    { iApply "HΦ". by iFrame "∗ # %". }

    (*@     if ver.Timestamp == 0 {                                             @*)
    (*@         // Fast-path read: set the final value and clean up the read versions. @*)
    (*@         grd.valuem[key] = ver.Value                                     @*)
    (*@         delete(grd.qreadm, key)                                         @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct (big_sepM2_dom with "Hqreadm") as %Hdomqreadm.
    destruct ver as [rts value].
    case_bool_decide as Hrts; simpl in Hrts; wp_pures.
    { wp_loadField.
      wp_apply (wp_MapInsert with "Hvaluem"); first done.
      iIntros "Hvaluem".
      wp_loadField.
      wp_apply (wp_MapDelete with "HqreadmM").
      iIntros "HqreadmM".
      wp_pures.
      iApply "HΦ".
      iAssert ([∗ map] p;m ∈ delete key qreadmM; delete key qreadm, own_map p (DfracOwn 1) m)%I
        with "[Hqreadm]" as "Hqreadm".
      { destruct (decide (key ∈ dom qreadm)) as [Hin | Hnotin].
        { apply elem_of_dom in Hin as [qread Hqread].
          by iDestruct (big_sepM2_delete_r with "Hqreadm") as (p) "(_ & _ & Hqreadm)".
        }
        assert (Hnone : qreadmM !! key = None).
        { by rewrite -not_elem_of_dom Hdomqreadm. }
        apply not_elem_of_dom in Hnotin.
        do 2 (rewrite delete_notin; last done).
        done.
      }
      iFrame "∗ # %".
      iModIntro.
      iSplit.
      { rewrite /fast_or_slow_read.
        inv Hrts.
        case_decide as Hcase; last first.
        { simpl in Hcase. clear -Hcase. word. }
        simpl.
        iApply (big_sepM_insert_2 with "[] Hfinal").
        iFrame "Hfsread".
      }
      { iSplit.
        { destruct (decide (key ∈ dom qreadm)) as [Hin | Hnotin]; last first.
          { apply not_elem_of_dom in Hnotin.
            by rewrite delete_notin.
          }
          apply elem_of_dom in Hin as [qread Hqread].
          by iDestruct (big_sepM_delete with "Hqread") as "[_ ?]".
        }
        { iPureIntro.
          by apply map_Forall_delete.
        }
      }
    }

    (*@     qread, ok := grd.qreadm[key]                                        @*)
    (*@     if !ok {                                                            @*)
    (*@         // The very first version arrives. Initialize a new map with the version @*)
    (*@         // received.                                                    @*)
    (*@         verm := make(map[uint64]tulip.Version)                          @*)
    (*@         verm[rid] = ver                                                 @*)
    (*@         grd.qreadm[key] = verm                                          @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapGet with "HqreadmM").
    iIntros (qreadP ok) "[%Hok HqreadmM]".
    wp_pures.
    destruct ok; wp_pures; last first.
    { wp_apply (wp_NewMap u64 (u64 * dbval)).
      iIntros (vermP) "Hverm".
      wp_apply (wp_MapInsert with "Hverm"); first by auto.
      iIntros "Hverm".
      wp_loadField.
      wp_apply (wp_MapInsert with "HqreadmM"); first by auto.
      iIntros "HqreadmM".
      wp_pures.
      iApply "HΦ".
      apply map_get_false in Hok as [HqreadmM _].
      assert (Hqreadm : qreadm !! key = None).
      { by rewrite -not_elem_of_dom -Hdomqreadm not_elem_of_dom. }
      iDestruct (big_sepM2_insert_2 _ _ _ key with "[Hverm] Hqreadm") as "Hqreadm".
      { iFrame "Hverm". }
      iFrame "∗ # %".
      iModIntro.
      iSplit.
      { iApply (big_sepM_insert_2 with "[] Hqread").
        rewrite /map_insert insert_empty big_sepM_singleton.
        rewrite /fast_or_slow_read.
        case_decide as Hslow; simpl in Hslow.
        { exfalso. clear -Hrts Hslow. apply u64_val_ne in Hrts. word. }
        done.
      }
      { iPureIntro.
        apply map_Forall_insert_2; last done.
        rewrite /map_insert insert_empty dom_singleton_L.
        clear -Hrid. set_solver.
      }
    }

    (*@     _, responded := qread[rid]                                          @*)
    (*@     if responded {                                                      @*)
    (*@         // The replica has already responded with its latest version.   @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    apply map_get_true in Hok.
    assert (is_Some (qreadm !! key)) as [qread Hqread].
    { by rewrite -elem_of_dom -Hdomqreadm elem_of_dom. }
    iDestruct (big_sepM2_delete _ _ _ key with "Hqreadm") as "[Hqr Hqreadm]".
    { apply Hok. }
    { apply Hqread. }
    wp_apply (wp_MapGet with "Hqr").
    clear Hfinal v.
    iIntros (v responded) "[%Hresponded Hqr]".
    wp_pures.
    destruct responded; wp_pures.
    { iDestruct (big_sepM2_insert_2 _ _ _ key with "[Hqr] Hqreadm") as "Hqreadm".
      { iFrame "Hqr". }
      do 2 (rewrite insert_delete; last done).
      iApply "HΦ".
      by iFrame "∗ # %".
    }

    (*@     // Record the version responded by the replica.                     @*)
    (*@     qread[rid] = ver                                                    @*)
    (*@     grd.qreadm[key] = qread                                             @*)
    (*@                                                                         @*)
    wp_apply (wp_MapInsert with "Hqr"); first done.
    iIntros "Hqr".
    wp_loadField.
    wp_apply (wp_MapInsert with "HqreadmM"); first done.
    iIntros "HqreadmM".
    rewrite /map_insert.
    set qread' := insert _ _ qread.
    iDestruct (big_sepM_lookup with "Hqread") as "Hqreadprev"; first apply Hqread.
    iDestruct (big_sepM_insert_2 _ _ key qread' with "[] Hqread")
      as "Hqread'".
    { simpl.
      iApply (big_sepM_insert_2 with "[] Hqreadprev").
      rewrite /fast_or_slow_read.
      case_decide as Hslow; simpl in Hslow.
      { exfalso. clear -Hrts Hslow. apply u64_val_ne in Hrts. word. }
      done.
    }
    set qreadm' := insert _ _ qreadm.
    assert (Hvrids' : map_Forall (λ _ m, dom m ⊆ rids_all) qreadm').
    { apply map_Forall_insert_2; last done.
      rewrite dom_insert_L.
      specialize (Hvrids _ _ Hqread). simpl in Hvrids.
      clear -Hrid Hvrids. set_solver.
    }

    (*@     // Count the responses from replicas.                               @*)
    (*@     n := uint64(len(qread))                                             @*)
    (*@     if !grd.cquorum(n) {                                                @*)
    (*@         // Cannot determine the final value without a classic quorum of @*)
    (*@         // versions.                                                    @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_MapLen with "Hqr").
    iIntros "[%Hsz Hqr]".
    apply map_get_false in Hresponded as [Hresponded _].
    rewrite map_size_insert_None in Hsz *; last apply Hresponded.
    wp_pures.
    wp_apply (wp_GroupReader__cquorum with "Hnrps").
    iIntros "Hnrps".
    (* this additional step avoids some unwanted computation *)
    set sc := size rids_all.
    wp_pures.
    case_bool_decide as Hsize; wp_pures; last first.
    { iDestruct (big_sepM2_insert_2 _ _ _ key with "[Hqr] Hqreadm") as "Hqreadm".
      { iFrame "Hqr". }
      rewrite 2!insert_delete_insert.
      iApply "HΦ".
      by iFrame "∗ # %".
    }

    (*@     // With enough versions, choose the latest one to be the final value. @*)
    (*@     latest := grd.pickLatestValue(key)                                  @*)
    (*@     grd.valuem[key] = latest                                            @*)
    (*@                                                                         @*)
    iDestruct (big_sepM2_insert_2 _ _ _ key with "[Hqr] Hqreadm") as "Hqreadm".
    { simpl. iFrame "Hqr". }
    rewrite 2!insert_delete_insert.
    iAssert (own_greader_qreadm grd qreadm' ts γ)%I
      with "[HqreadmP HqreadmM Hqreadm]" as "Hqreadm".
    { by iFrame "∗ # %". }
    wp_apply (wp_GroupReader__pickLatestValue with "Hqreadm").
    { apply lookup_insert. }
    { rewrite /cquorum_size.
      rewrite dom_insert_L size_union; last first.
      { apply not_elem_of_dom in Hresponded. clear -Hresponded. set_solver. }
      rewrite size_singleton size_dom.
      clear -Hsz Hsize. lia.
    }
    iIntros (latest) "[Hqreadm #Hqr]".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hvaluem"); first done.
    iIntros "Hvaluem".

    (*@     // The thread that determines the final value for @key also clears the @*)
    (*@     // versions collected for @key.                                     @*)
    (*@     grd.clearVersions(key)                                              @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupReader__clearVersions with "Hqreadm").
    iIntros "Hqreadm".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ # %".
    iModIntro.
    iApply (big_sepM_insert_2 with "[] Hfinal").
    by iRight.
  Qed.

End program.
