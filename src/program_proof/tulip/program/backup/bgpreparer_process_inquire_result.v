From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import propose.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_try_resign.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_try_resign bgpreparer_in
  bgpreparer_collect_proposal bgpreparer_try_validate
  bgpreparer_count_proposals bgpreparer_latest_proposal
  bgpreparer_cquorum bgpreparer_hcquorum
  bgpreparer_become_unpreparing bgpreparer_become_preparing
  bgpreparer_get_pwrs bgpreparer_count_fast_proposals
  bgpreparer_quorum_validated.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__processInquireResult
    (gpp : loc) (rid : u64) (pp : ppsl) (vd : bool) (pwrsP : loc) (res : rpres)
    pwrs rk ts cid gid γ :
    let rkl := uint.nat pp.1 in
    (1 < rk)%nat ->
    rid ∈ rids_all ->
    gid ∈ gids_all ->
    (if vd then own_map pwrsP DfracDiscarded pwrs else True) -∗
    inquire_outcome γ gid rid cid ts rk rkl pp.2 vd pwrs res -∗
    know_tulip_inv γ -∗
    {{{ own_backup_gpreparer gpp rk ts cid gid γ }}}
      BackupGroupPreparer__processInquireResult #gpp #rid (ppsl_to_val pp) #vd #pwrsP #(rpres_to_u64 res)
    {{{ RET #(); own_backup_gpreparer gpp rk ts cid gid γ }}}.
  Proof.
    iIntros (rkl Hrk Hrid Hgid) "#Hm #Hinq #Hinv".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) processInquireResult(rid uint64, pp tulip.PrepareProposal, vd bool, pwrs tulip.KVMap, res uint64) { @*)
    (*@     // Result is ready or another backup coordinator has become live.   @*)
    (*@     if gpp.tryResign(res) {                                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hgpp".
    wp_pures.
    wp_apply (wp_BackupGroupPreparer__tryResign with "[] Hgpp").
    { by destruct res. }
    iIntros (resigned phase') "(Hgpp & %Hres & %Hresigned)".
    clear phase. rename phase' into phase.
    destruct resigned; wp_pures.
    { iApply "HΦ". by iFrame. }

    (*@     // Skip since the coordinator is already in the second phase.       @*)
    (*@     if gpp.in(BGPP_PREPARING) || gpp.in(BGPP_UNPREPARING) {             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__in _ BGPPPreparing with "Hgpp").
    iIntros "Hgpp".
    destruct (bool_decide (phase = BGPPPreparing)) eqn:Hpreparing; wp_pures.
    { iApply "HΦ". by iFrame. }
    wp_apply (wp_BackupGroupPreparer__in _ BGPPUnpreparing with "Hgpp").
    iIntros "Hgpp".
    destruct (bool_decide (phase = BGPPUnpreparing)) eqn:Hunpreparing; wp_pures.
    { iApply "HΦ". by iFrame. }
    rewrite bool_decide_eq_false in Hpreparing.
    rewrite bool_decide_eq_false in Hunpreparing.

    (*@     // Record prepare prososal and validation result.                   @*)
    (*@     gpp.collectProposal(rid, pp)                                        @*)
    (*@     gpp.tryValidate(rid, vd, pwrs)                                      @*)
    (*@                                                                         @*)
    (* Prove the only possible res here is [ReplicaOK]. *)
    destruct res; try done. simpl.
    iNamed "Hinq". iNamed "Hgpp".
    wp_apply (wp_BackupGroupPreparer__collectProposal_weak with "Hvote Hlb Hpps").
    { apply Hrid. }
    clear pps.
    iIntros (pps) "Hpps".
    wp_pures.
    wp_apply (wp_BackupGroupPreparer__tryValidate with "Hm Hsafepwrs Hvd [$Hpwrs $Hvdm]").
    { apply Hrid. }
    iIntros "[Hpwrs Hvdm]".
    wp_pures.

    (*@     // No decision should be made without a classic quorum of prepare proposals. @*)
    (*@     n := gpp.countProposals()                                           @*)
    (*@     if !gpp.cquorum(n) {                                                @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__countProposals with "Hpps").
    iIntros (n) "[Hpps %Hn]".
    wp_apply (wp_BackupGroupPreparer__cquorum with "Hnrps").
    iIntros "Hnrps".
    set c := (bool_decide _).
    destruct c eqn:Hquorumpsl; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ # %". }
    subst c.

    (* Prepare for making [exclusive_proposal]; we didn't create it explicitly
    here since we won't always make a proposal here (when going to the
    VALIDATING state). *)
    iAssert (quorum_voted γ gid ts rk cid)%I as (ridsvt) "[#Hbkvotes %Hcq]".
    { iNamed "Hpps".
      iExists (dom pps).
      iFrame "Hvotes".
      iPureIntro.
      split; first apply Hdompps.
      clear -Hn Hquorumpsl.
      rewrite bool_decide_eq_true in Hquorumpsl.
      rewrite -size_dom in Hn.
      rewrite /cquorum_size -Hn. lia.
    }
    iAssert (own_replica_backup_token γ cid.1 cid.2 ts rk gid)%I
      with "[Htoken]" as "Htoken".
    { by destruct phase. }

    (*@     // Compute the latest prepare proposal.                             @*)
    (*@     latest := gpp.latestProposal()                                      @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__latestProposal with "Hpps").
    { rewrite -map_size_non_empty_iff.
      rewrite bool_decide_eq_true in Hquorumpsl.
      clear -Hn Hquorumpsl. word.
    }
    iIntros (p) "(Hpps & %Hinpps & %Hgeall)".
    wp_pures.

    (*@     if latest.Rank != 0 {                                               @*)
    (*@                                                                         @*)
    set c := (bool_decide _).
    destruct c eqn:Hnz; wp_pures; last first.
    { (* First we prove safety of this proposal. *)
      iAssert (safe_proposal γ gid ts rk p.2)%I as "#Hsafepsl".
      { iNamed "Hpps".
        iExists blts.
        apply elem_of_map_img_1 in Hinpps as [i Hp].
        rewrite map_Forall2_forall in Hblts.
        destruct Hblts as [Hblts Hdom].
        rewrite bool_decide_eq_true in Hquorumpsl.
        assert (Hlatest : latest_before_quorum rk blts = uint.nat p.1).
        { (* FIXME: ugly proof and should be a general lemma about [latest_before_quorum]. *)
          unshelve epose proof (latest_before_quorum_in blts rk _) as Hin.
          { intros Hempty.
            rewrite Hempty in Hdom.
            clear -Hn Hquorumpsl Hdom.
            apply dom_empty_inv_L in Hdom.
            rewrite Hdom map_size_empty in Hn.
            word.
          }
          destruct Hin as (j & blt & Hblt & Heq).
          rewrite -Heq.
          assert (is_Some (pps !! j)) as [pj Hpj].
          { by rewrite -elem_of_dom Hdom elem_of_dom. }
          specialize (Hgeall _ _ Hpj). simpl in Hgeall.
          specialize (Hblts _ _ _ Hpj Hblt) as Hpjlatest.
          destruct Hpjlatest as [Hpjlatest _].
          assert (is_Some (blts !! i)) as [l Hl].
          { by rewrite -elem_of_dom -Hdom elem_of_dom. }
          specialize (Hblts _ _ _ Hp Hl) as [Hplatest _].
          pose proof (latest_before_quorum_ge blts rk) as Hge.
          specialize (Hge _ _ Hl). simpl in Hge.
          rewrite -Heq in Hge.
          specialize (Hlen _ _ Hl) as Hlenl. simpl in Hlenl.
          specialize (Hlen _ _ Hblt) as Hlenblt. simpl in Hlenblt.
          rewrite /latest_term -Hlenblt in Hpjlatest.
          rewrite Hpjlatest.
          rewrite Hpjlatest in Hge.
          rewrite /latest_term -Hlenl in Hplatest.
          rewrite Hplatest in Hge.
          clear -Hgeall Hge.
          word.
        }
        rewrite Hlatest.
        iDestruct (big_sepM_lookup with "Hpsl") as "Hpp".
        { apply Hp. }
        (* rewrite Hunprep. *)
        iFrame "#".
        iPureIntro.
        split.
        { rewrite -Hdom.
          split; first apply Hdompps.
          clear -Hn Hquorumpsl.
          rewrite -size_dom in Hn.
          rewrite /cquorum_size -Hn. lia.
        }
        split.
        { apply (map_Forall_impl _ _ _ Hlen). clear. lia. }
        { destruct (decide (uint.nat p.1 = 0)%nat) as [Hz | _]; last done.
          rewrite bool_decide_eq_false in Hnz.
          clear -Hz Hnz. exfalso.
          assert (Hp : p.1 = W64 0) by word.
          by rewrite Hp in Hnz.
        }
      }

      (*@         // Unprepare this transaction if its latest slow proposal is @false. @*)
      (*@         if !latest.Prepared {                                           @*)
      (*@             gpp.phase = BGPP_UNPREPARING                                @*)
      (*@             return                                                      @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      destruct p.2 eqn:Hunprep; wp_pures; last first.
      { wp_apply (wp_BackupGroupPreparer__becomeUnpreparing with "[$Hsrespm $Hphase]").
        iIntros "[Hsrespm Hphase]".
        wp_pures.
        iApply "HΦ".
        iAssert (exclusive_proposal γ gid ts rk)%I with "[Htoken]" as "Hexcl".
        { rewrite /exclusive_proposal.
          destruct (decide (rk = 1)%nat); first lia.
          by iFrame "∗ # %".
        }
        iAssert (|={⊤}=> is_group_prepare_proposal γ gid ts rk false)%I with "[Hexcl]" as "> #Hpsl".
        { iDestruct "Hinv" as (proph) "Hinv".
          iInv "Hinv" as "> HinvO" "HinvC".
          iNamed "HinvO".
          iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
          { apply Hgid. }
          iMod (group_inv_propose with "Hsafepsl Hexcl Hgroup") as "[Hgroup #Hppsl]".
          { clear -Hrk. lia. }
          iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
          by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
        }
        by iFrame "∗ #".
      }

      (*@         // If the latest slow proposal is @true, we further check the   @*)
      (*@         // availability of partial writes. We might be able to prove it @*)
      (*@         // without this check by using the fact that a cquorum must have been @*)
      (*@         // validated in order to prepare in the slow rank, and the fact that @*)
      (*@         // we've received a cquorum of responses at this point, but the @*)
      (*@         // reasoning seems pretty tricky. In any case, the check should be valid @*)
      (*@         // and would eventually passes with some alive cquorum.         @*)
      (*@         _, ok := gpp.getPwrs()                                          @*)
      (*@         if !ok {                                                        @*)
      (*@             return                                                      @*)
      (*@         }                                                               @*)
      (*@         gpp.phase = BGPP_PREPARING                                      @*)
      (*@         return                                                          @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_apply (wp_BackupGroupPreparer__getPwrs with "Hpwrs").
      iClear "Hm". clear pwrsP.
      iIntros (pwrsP pwrsok) "[Hpwrs Hm]".
      wp_pures.
      destruct pwrsok; wp_pures; last first.
      { iApply "HΦ". iFrame "∗ #". by destruct phase. }
      wp_apply (wp_BackupGroupPreparer__becomePreparing with "[$Hsrespm $Hphase]").
      iIntros "[Hsrespm Hphase]".
      wp_pures.
      iApply "HΦ".
      iAssert (exclusive_proposal γ gid ts rk)%I with "[Htoken]" as "Hexcl".
      { rewrite /exclusive_proposal.
        destruct (decide (rk = 1)%nat); first lia.
        by iFrame "∗ # %".
      }
      iAssert (|={⊤}=> is_group_prepare_proposal γ gid ts rk true)%I with "[Hexcl]" as "> #Hpsl".
      { iDestruct "Hinv" as (proph) "Hinv".
        iInv "Hinv" as "> HinvO" "HinvC".
        iNamed "HinvO".
        iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
        { apply Hgid. }
        iMod (group_inv_propose with "Hsafepsl Hexcl Hgroup") as "[Hgroup #Hppsl]".
        { clear -Hrk. lia. }
        iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
        by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      }
      by iFrame "∗ #".
    }
    subst c.
    rewrite bool_decide_eq_true in Hnz.
    inv Hnz as [Hz].

    (*@     // All the proposals collected so far are fast. Now we need to decide the @*)
    (*@     // next step based on how many of them are prepared and unprepared. @*)
    (*@     nfu := gpp.countFastProposals(false)                                @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__countFastProposals with "Hpps").
    iIntros (nfu) "[Hpps %Hnfu]".

    (*@     // Note that using majority (i.e., floor(n / 2) + 1) rather than half (i.e., @*)
    (*@     // ceiling(n / 2)) as the threshold would lead to liveness issues.  @*)
    (*@     //                                                                  @*)
    (*@     // For instance, in a 3-replica setup, using majority means that the @*)
    (*@     // coordinator can propose UNPREPARED only if it knows there are at least @*)
    (*@     // two fast unprepares. Consider the following scenario:            @*)
    (*@     // 1. Replica X fails.                                              @*)
    (*@     // 2. Txn A validates on replica Y and fails.                       @*)
    (*@     // 3. Txn B validates on replica Z and fails.                       @*)
    (*@     // 4. Backup group coordinators of A and B will obtain each one fast @*)
    (*@     // unprepare (on Z and Y, respetively), so they cannot abort, but also not @*)
    (*@     // commit since they will not be able to validate on the other replica. @*)
    (*@     if gpp.hcquorum(nfu) {                                              @*)
    (*@         // The number of fast unprepares has reached at least half of some @*)
    (*@         // classic quorum, which means the number of fast prepares must not @*)
    (*@         // reach a majority in this quorum. This further implies the transaction @*)
    (*@         // could not have fast prepared, and hence it is safe to unprepare. @*)
    (*@         //                                                              @*)
    (*@         // Logical action: Propose.                                     @*)
    (*@         gpp.phase = BGPP_UNPREPARING                                    @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__hcquorum with "Hnrps").
    iIntros "Hnrps".
    set c := bool_decide _.
    destruct c eqn:Huorp; wp_pures.
    { wp_apply (wp_BackupGroupPreparer__becomeUnpreparing with "[$Hsrespm $Hphase]").
      iIntros "[Hsrespm Hphase]".
      wp_pures.
      iApply "HΦ".
      iAssert (safe_proposal γ gid ts rk false)%I as "#Hsafepsl".
      { iNamed "Hpps".
        iExists blts.
        apply elem_of_map_img_1 in Hinpps as [i Hp].
        rewrite map_Forall2_forall in Hblts.
        destruct Hblts as [Hblts Hdom].
        rewrite bool_decide_eq_true in Hquorumpsl.
        assert (Hlatest : latest_before_quorum rk blts = uint.nat p.1).
        { (* FIXME: ugly proof and should be a general lemma about [latest_before_quorum]. *)
          unshelve epose proof (latest_before_quorum_in blts rk _) as Hin.
          { intros Hempty.
            rewrite Hempty in Hdom.
            clear -Hn Hquorumpsl Hdom.
            apply dom_empty_inv_L in Hdom.
            rewrite Hdom map_size_empty in Hn.
            word.
          }
          destruct Hin as (j & blt & Hblt & Heq).
          rewrite -Heq.
          assert (is_Some (pps !! j)) as [pj Hpj].
          { by rewrite -elem_of_dom Hdom elem_of_dom. }
          specialize (Hgeall _ _ Hpj). simpl in Hgeall.
          specialize (Hblts _ _ _ Hpj Hblt) as Hpjlatest.
          destruct Hpjlatest as [Hpjlatest _].
          assert (is_Some (blts !! i)) as [l Hl].
          { by rewrite -elem_of_dom -Hdom elem_of_dom. }
          specialize (Hblts _ _ _ Hp Hl) as [Hplatest _].
          pose proof (latest_before_quorum_ge blts rk) as Hge.
          specialize (Hge _ _ Hl). simpl in Hge.
          rewrite -Heq in Hge.
          specialize (Hlen _ _ Hl) as Hlenl. simpl in Hlenl.
          specialize (Hlen _ _ Hblt) as Hlenblt. simpl in Hlenblt.
          rewrite /latest_term -Hlenblt in Hpjlatest.
          rewrite Hpjlatest.
          rewrite Hpjlatest in Hge.
          rewrite /latest_term -Hlenl in Hplatest.
          rewrite Hplatest in Hge.
          clear -Hgeall Hge.
          word.
        }
        rewrite Hlatest Hz uint_nat_W64_0.
        iFrame "#".
        iSplit; first done.
        iPureIntro.
        split.
        { rewrite -Hdom.
          split; first apply Hdompps.
          clear -Hn Hquorumpsl.
          rewrite -size_dom in Hn.
          rewrite /cquorum_size -Hn. lia.
        }
        split.
        { apply (map_Forall_impl _ _ _ Hlen). clear. lia. }
        { destruct (decide (O = O)); last done.
          rewrite bool_decide_eq_true in Huorp.
          rewrite /nfast.
          replace (size (filter _ _)) with (uint.nat nfu).
          { clear -Huorp. lia. }
          rewrite Hnfu /accepted_in.
          apply map_Forall2_size_filter.
          simpl.
          rewrite map_Forall2_forall.
          split; last apply Hdom.
          intros ridx px lx Hpx Hlx.
          specialize (Hblts _ _ _ Hpx Hlx).
          destruct Hblts as [Hpx1 Hpx2].
          pose proof (latest_before_quorum_ge blts rk) as Hallz.
          rewrite Hlatest Hz uint_nat_W64_0 in Hallz.
          specialize (Hallz _ _ Hlx). simpl in Hallz.
          specialize (Hlen _ _ Hlx). simpl in Hlen.
          rewrite /latest_term -Hlen in Hpx1.
          assert (Hpx1z : px.1 = W64 0).
          { clear -Hallz Hpx1. word. }
          rewrite Hpx1z uint_nat_W64_0 in Hpx2.
          rewrite Hpx2.
          split.
          { intros Heq. by rewrite Heq. }
          { intros Heq. by inv Heq. }
        }
      }
      iAssert (exclusive_proposal γ gid ts rk)%I with "[Htoken]" as "Hexcl".
      { rewrite /exclusive_proposal.
        destruct (decide (rk = 1)%nat); first lia.
        by iFrame "∗ # %".
      }
      iAssert (|={⊤}=> is_group_prepare_proposal γ gid ts rk false)%I
        with "[Hexcl]" as "> #Hpsl".
      { iDestruct "Hinv" as (proph) "Hinv".
        iInv "Hinv" as "> HinvO" "HinvC".
        iNamed "HinvO".
        iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
        { apply Hgid. }
        iMod (group_inv_propose with "Hsafepsl Hexcl Hgroup") as "[Hgroup #Hppsl]".
        { clear -Hrk. lia. }
        iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
        by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      }
      by iFrame "∗ #".
    }

    (*@     // The check below is a proof artifact. We should be able to deduce safety @*)
    (*@     // of proposing PREPARE from the fact that the number of fast unprepares @*)
    (*@     // does not reach half, and the fact that decisions are binary. TODO: remove @*)
    (*@     // this once that is proven.                                        @*)
    (*@     nfp := gpp.countFastProposals(true)                                 @*)
    (*@     if !gpp.hcquorum(nfp) {                                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__countFastProposals with "Hpps").
    iIntros (nfp) "[Hpps %Hnfp]".
    wp_apply (wp_BackupGroupPreparer__hcquorum with "Hnrps").
    iIntros "Hnrps".
    set d := bool_decide _.
    destruct d eqn:Hfp; wp_pures; last first.
    { iApply "HΦ". iFrame "∗ #". by destruct phase. }
    iAssert (safe_proposal γ gid ts rk true)%I as "#Hsafepsl".
    { iNamed "Hpps".
      iExists blts.
      apply elem_of_map_img_1 in Hinpps as [i Hp].
      rewrite map_Forall2_forall in Hblts.
      destruct Hblts as [Hblts Hdom].
      rewrite bool_decide_eq_true in Hquorumpsl.
      assert (Hlatest : latest_before_quorum rk blts = uint.nat p.1).
      { (* FIXME: ugly proof and should be a general lemma about [latest_before_quorum]. *)
        unshelve epose proof (latest_before_quorum_in blts rk _) as Hin.
        { intros Hempty.
          rewrite Hempty in Hdom.
          clear -Hn Hquorumpsl Hdom.
          apply dom_empty_inv_L in Hdom.
          rewrite Hdom map_size_empty in Hn.
          word.
        }
        destruct Hin as (j & blt & Hblt & Heq).
        rewrite -Heq.
        assert (is_Some (pps !! j)) as [pj Hpj].
        { by rewrite -elem_of_dom Hdom elem_of_dom. }
        specialize (Hgeall _ _ Hpj). simpl in Hgeall.
        specialize (Hblts _ _ _ Hpj Hblt) as Hpjlatest.
        destruct Hpjlatest as [Hpjlatest _].
        assert (is_Some (blts !! i)) as [l Hl].
        { by rewrite -elem_of_dom -Hdom elem_of_dom. }
        specialize (Hblts _ _ _ Hp Hl) as [Hplatest _].
        pose proof (latest_before_quorum_ge blts rk) as Hge.
        specialize (Hge _ _ Hl). simpl in Hge.
        rewrite -Heq in Hge.
        specialize (Hlen _ _ Hl) as Hlenl. simpl in Hlenl.
        specialize (Hlen _ _ Hblt) as Hlenblt. simpl in Hlenblt.
        rewrite /latest_term -Hlenblt in Hpjlatest.
        rewrite Hpjlatest.
        rewrite Hpjlatest in Hge.
        rewrite /latest_term -Hlenl in Hplatest.
        rewrite Hplatest in Hge.
        clear -Hgeall Hge.
        word.
      }
      rewrite Hlatest Hz uint_nat_W64_0.
      iFrame "#".
      iSplit; first done.
      iPureIntro.
      split.
      { rewrite -Hdom.
        split; first apply Hdompps.
        clear -Hn Hquorumpsl.
        rewrite -size_dom in Hn.
        rewrite /cquorum_size -Hn. lia.
      }
      split.
      { apply (map_Forall_impl _ _ _ Hlen). clear. lia. }
      { destruct (decide (O = O)); last done.
        rewrite bool_decide_eq_true in Hfp.
        rewrite /nfast.
        replace (size (filter _ _)) with (uint.nat nfp).
        { clear -Hfp. lia. }
        rewrite Hnfp /accepted_in.
        apply map_Forall2_size_filter.
        simpl.
        rewrite map_Forall2_forall.
        split; last apply Hdom.
        intros ridx px lx Hpx Hlx.
        specialize (Hblts _ _ _ Hpx Hlx).
        destruct Hblts as [Hpx1 Hpx2].
        pose proof (latest_before_quorum_ge blts rk) as Hallz.
        rewrite Hlatest Hz uint_nat_W64_0 in Hallz.
        specialize (Hallz _ _ Hlx). simpl in Hallz.
        specialize (Hlen _ _ Hlx). simpl in Hlen.
        rewrite /latest_term -Hlen in Hpx1.
        assert (Hpx1z : px.1 = W64 0).
        { clear -Hallz Hpx1. word. }
        rewrite Hpx1z uint_nat_W64_0 in Hpx2.
        rewrite Hpx2.
        split.
        { intros Heq. by rewrite Heq. }
        { intros Heq. by inv Heq. }
      }
    }

    (*@     // At this point, we know there exists a classic quorum in which the number @*)
    (*@     // of fast unprepares does not reach half (and hence not a majority), @*)
    (*@     // meaning the transaction could not have fast unprepared. However, we still @*)
    (*@     // need to ensure validation on a majority to achieve mutual exclusion. @*)
    (*@                                                                         @*)
    (*@     // Move to PREPARING phase if it reaches a majority.                @*)
    (*@     if gpp.quorumValidated() {                                          @*)
    (*@         // Logical action: Propose.                                     @*)
    (*@         gpp.phase = BGPP_PREPARING                                      @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__quorumValidated with "[$Hvdm $Hnrps]").
    iIntros (qv) "(Hvdm & Hnrps & #Hqv)".
    destruct qv; wp_pures.
    { wp_apply (wp_BackupGroupPreparer__becomePreparing with "[$Hsrespm $Hphase]").
      iIntros "[Hsrespm Hphase]".
      wp_pures.
      iApply "HΦ".
      iAssert (exclusive_proposal γ gid ts rk)%I with "[Htoken]" as "Hexcl".
      { rewrite /exclusive_proposal.
        destruct (decide (rk = 1)%nat); first lia.
        by iFrame "∗ # %".
      }
      iAssert (|={⊤}=> is_group_prepare_proposal γ gid ts rk true)%I
        with "[Hexcl]" as "> #Hpsl".
      { iDestruct "Hinv" as (proph) "Hinv".
        iInv "Hinv" as "> HinvO" "HinvC".
        iNamed "HinvO".
        iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
        { apply Hgid. }
        iMod (group_inv_propose with "Hsafepsl Hexcl Hgroup") as "[Hgroup #Hppsl]".
        { clear -Hrk. lia. }
        iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
        by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      }
      by iFrame "∗ #".
    }

    (*@     // Cannot proceed to the second phase (i.e., proposing prepares or  @*)
    (*@     // unprepares). Try to validate on more replicas.                   @*)
    (*@     gpp.phase = BGPP_VALIDATING                                         @*)
    (*@ }                                                                       @*)
    iNamed "Hphase".
    wp_storeField.
    iApply "HΦ".
    iDestruct (own_backup_gpreparer_srespm_non_accepting_phase _ _ BGPPValidating
                with "Hsrespm") as "Hsrespm".
    { intros []. }
    by iFrame "∗ #".
  Qed.

End program.
