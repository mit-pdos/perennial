From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import quorum.
From Perennial.program_proof.tulip.program.gcoord Require Import
  greader_repr greader_cquorum greader_pick_latest_value greader_clear_versions.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupReader__processReadResult
    grd (rid : u64) (key : byte_string) (ver : dbpver) (slow : bool) ts γ :
    rid ∈ rids_all ->
    fast_or_slow_read γ rid key (uint.nat ver.1) ts ver.2 slow -∗
    {{{ own_greader grd ts γ }}}
      GroupReader__processReadResult #grd #rid #(LitString key) (dbpver_to_val ver) #slow
    {{{ RET #(); own_greader grd ts γ }}}.
  Proof.
    iIntros (Hrid) "#Hfsread".
    iIntros (Φ) "!> Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) processReadResult(rid uint64, key string, ver tulip.Version, slow bool) { @*)
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

    (*@     if !slow {                                                          @*)
    (*@         // Fast-path read: set the final value and clean up the read versions. @*)
    (*@         grd.valuem[key] = ver.Value                                     @*)
    (*@         delete(grd.qreadm, key)                                         @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct (big_sepM2_dom with "Hqreadm") as %Hdomqreadm.
    destruct ver as [rts value].
    destruct slow; wp_pures; last first.
    (* case_bool_decide as Hrts; simpl in Hrts; wp_pures. *)
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
        do 2 (rewrite delete_id; last done).
        done.
      }
      iFrame "∗ # %".
      iModIntro.
      iSplit.
      { iApply (big_sepM_insert_2 with "[] Hfinal").
        iFrame "Hfsread".
      }
      { iSplit.
        { destruct (decide (key ∈ dom qreadm)) as [Hin | Hnotin]; last first.
          { apply not_elem_of_dom in Hnotin.
            by rewrite delete_id.
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
        by rewrite /map_insert insert_empty big_sepM_singleton.
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
      do 2 (rewrite insert_delete_id; last done).
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
    { by iApply (big_sepM_insert_2 with "[] Hqreadprev"). }
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
      rewrite 2!insert_delete_eq.
      iApply "HΦ".
      by iFrame "∗ # %".
    }

    (*@     // With enough versions, choose the latest one to be the final value. @*)
    (*@     latest := grd.pickLatestValue(key)                                  @*)
    (*@     grd.valuem[key] = latest                                            @*)
    (*@                                                                         @*)
    iDestruct (big_sepM2_insert_2 _ _ _ key with "[Hqr] Hqreadm") as "Hqreadm".
    { simpl. iFrame "Hqr". }
    rewrite 2!insert_delete_eq.
    iAssert (own_greader_qreadm grd qreadm' ts γ)%I
      with "[HqreadmP HqreadmM Hqreadm]" as "Hqreadm".
    { by iFrame "∗ # %". }
    wp_apply (wp_GroupReader__pickLatestValue with "Hqreadm").
    { apply lookup_insert_eq. }
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
