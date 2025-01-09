From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section collect.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__collect
    (px : loc) (nid : u64) (term : u64)
    (nidme : u64) (entsP : Slice.t) (ents : list byte_string)
    (termc lsnc : u64) (logpeer : list byte_string) nids γ :
    nid ∈ nids ->
    drop (uint.nat lsnc) logpeer = ents ->
    past_nodedecs_latest_before γ nid (uint.nat termc) (uint.nat term) logpeer -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_nominated_with_termc_lsnc px nidme termc lsnc nids γ ∗
        own_slice entsP stringT (DfracOwn 1) ents
    }}}
      Paxos__collect #px #nid #term (to_val entsP)
    {{{ RET #(); own_paxos_nominated px nidme nids γ }}}.
  Proof.
    iIntros (Hinnids Hlogpeer) "#Hpromise #Hinv".
    iIntros (Φ) "!> [Hpx Hents] HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) collect(nid uint64, term uint64, ents []string) {      @*)
    (*@     _, recved := px.respp[nid]                                          @*)
    (*@     if recved {                                                         @*)
    (*@         // Vote from [nid] has already been received.                   @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hpx". iNamed "Hcand". iNamed "Honlyc".
    wp_loadField.
    wp_apply (wp_MapGet with "Hrespp").
    iIntros (v recved) "[%Hrecved Hrespp]".
    wp_if_destruct.
    { iApply "HΦ".
      iFrame "Hpx HentspP HiscandP".
      by iFrame "∗ # %".
    }
    apply map_get_false in Hrecved as [Hrecved _].
    clear Heqb v recved.

    (*@     if term < px.termp {                                                @*)
    (*@         // Simply record the response if the peer has a smaller term.   @*)
    (*@         px.respp[nid] = true                                            @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_MapInsert with "Hrespp"); first done.
      iIntros "Hrespp".
      wp_pures.
      iApply "HΦ".
      set logc := take _ log.
      set respp' := map_insert _ _ _.
      iAssert (votes_in γ (dom respp') (uint.nat termc) (uint.nat termp) (logc ++ entsp))%I
        as "Hvotes'".
      { iNamed "Hpromise".
        iNamed "Hvotes".
        iDestruct (big_sepM_insert_2 with "Hpastd Hdss") as "Hdss'".
        iFrame "Hdss'".
        iPureIntro.
        split.
        { by apply map_Forall_insert_2. }
        split.
        { rewrite /latest_term_before_quorum_nodedec.
          rewrite (latest_term_before_quorum_with_insert_le _ _ _ _ _ (uint.nat term)).
          { done. }
          { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
          { rewrite -Hlends. apply Hlatest. }
          rewrite -latest_term_before_quorum_nodedec_unfold Hlatestq.
          clear -Heqb.
          word.
        }
        split.
        { rewrite length_of_longest_ledger_in_term_insert_None; first apply Hlongestq.
          { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
          rewrite (latest_term_before_with_None (mbind nodedec_to_ledger) (length ds)).
          { done. }
          rewrite /latest_term_nodedec /latest_term_before_nodedec in Hlatest.
          word.
        }
        split.
        { apply map_Exists_insert_2_2; last done.
          by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom.
        }
        { by rewrite 2!dom_insert_L Hdomdss. }
      }
      iFrame "Hpx HentspP HiscandP".
      iFrame "∗ # %".
      iPureIntro.
      rewrite dom_insert_L.
      set_solver.
    }
    rewrite Z.nlt_ge in Heqb.
    rename Heqb into Htermple.

    (*@     if term == px.termp && uint64(len(ents)) <= uint64(len(px.entsp)) { @*)
    (*@         // Simply record the response if the peer has the same term, but not @*)
    (*@         // more entries (i.e., longer prefix).                          @*)
    (*@         px.respp[nid] = true                                            @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_and with "[HentspP Hentsp]").
    { iNamedAccu. }
    { by wp_pures. }
    { iIntros (Heq).
      iNamed 1.
      wp_apply wp_slice_len.
      wp_loadField.
      wp_apply wp_slice_len.
      wp_pures.
      by iFrame.
    }
    iNamed 1.
    wp_if_destruct.
    { destruct Heqb as [Heq Hszle].
      inv Heq.
      iDestruct (own_slice_sz with "Hents") as %Hszents.
      iDestruct (own_slice_sz with "Hentsp") as %Hszentsp.
      wp_loadField.
      wp_apply (wp_MapInsert with "Hrespp"); first done.
      iIntros "Hrespp".
      wp_pures.
      iApply "HΦ".
      set logc := take _ log.
      set respp' := map_insert _ _ _.
      iAssert (⌜uint.Z lsnc ≤ length log⌝)%I as %Hlsncub.
      { by iNamed "Hpx". }
      iAssert (votes_in γ (dom respp') (uint.nat termc) (uint.nat termp) (logc ++ entsp))%I
        as "Hvotes'".
      { iNamed "Hpromise".
        iNamed "Hvotes".
        iDestruct (big_sepM_insert_2 with "Hpastd Hdss") as "Hdss'".
        iFrame "Hdss'".
        iPureIntro.
        split.
        { by apply map_Forall_insert_2. }
        split.
        { rewrite /latest_term_before_quorum_nodedec.
          rewrite (latest_term_before_quorum_with_insert_le _ _ _ _ _ (uint.nat termp)).
          { done. }
          { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
          { rewrite -Hlends. apply Hlatest. }
          rewrite -latest_term_before_quorum_nodedec_unfold Hlatestq.
          done.
        }
        split.
        { rewrite (length_of_longest_ledger_in_term_insert_Some_length_le _ _ _ _ logpeer).
          { apply Hlongestq. }
          { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
          { by rewrite Hacpt. }
          rewrite length_drop in Hszents.
          rewrite Hlongestq length_app length_take.
          clear -Hszents Hszentsp Hszle Hlsncub.
          word.
        }
        split.
        { apply map_Exists_insert_2_2; last done.
          by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom.
        }
        { by rewrite 2!dom_insert_L Hdomdss. }
      }
      iFrame "Hpx HiscandP".
      iFrame "∗ # %".
      iPureIntro.
      rewrite dom_insert_L.
      set_solver.
    }
    apply Classical_Prop.not_and_or in Heqb.
    rename Heqb into Hcase.
    rewrite Z.nle_gt in Hcase.
    iDestruct (own_slice_sz with "Hents") as %Hszents.
    iDestruct (own_slice_sz with "Hentsp") as %Hszentsp.

    (*@     // Update the largest term and longest log seen so far in this preparing @*)
    (*@     // phase, and record the response.                                  @*)
    (*@     px.termp = term                                                     @*)
    (*@     px.entsp = ents                                                     @*)
    (*@     px.respp[nid] = true                                                @*)
    (*@                                                                         @*)
    do 2 wp_storeField.
    wp_loadField.
    wp_apply (wp_MapInsert with "Hrespp"); first done.
    iIntros "Hrespp".
    wp_pures.
    iApply "HΦ".
    set logc := take _ log.
    set respp' := map_insert _ _ _.
    iAssert (⌜uint.Z term < uint.Z termc⌝)%I as %Htermlt.
    { iNamed "Hpromise".
      iPureIntro.
      rewrite /latest_term_nodedec /latest_term_before_nodedec Hlends in Hlatest.
      set f := mbind _ in Hlatest.
      unshelve epose proof (latest_term_before_with_lt f (uint.nat termc) ds _) as Hlt.
      { word. }
      clear -Hlt Hlatest.
      word.
    }
    (* Prove that the committed part [logc] matches on the leader and peer sides. *)
    iInv "Hinv" as "> HinvO" "HinvC".
    iAssert (⌜logpeer = logc ++ ents⌝)%I as %->.
    { (* Obtain [safe_ledger_above]. *)
      iNamed "Hpx".
      iDestruct "Hcmted" as (p) "[Hcmted %Hple]".
      iNamed "Hpromise".
      destruct (decide (p < uint.nat term)%nat) as [Hlt | Hge].
      { (* Case: The safe term [p] is less than the term [term] of [logpeer] / [ents].  *)
        iDestruct (safe_ledger_past_nodedecs_impl_prefix with "Hcmted Hpastd HinvO") as %Hlogc.
        { apply Hinnids. }
        { apply Hlt. }
        { apply Hacpt. }
        iPureIntro.
        subst logc.
        rewrite -(take_drop (uint.nat lsnc) logpeer) -Hlogpeer.
        f_equal.
        destruct Hlogc as [logtail ->].
        rewrite take_app_le; last first.
        { rewrite length_take. clear -Hlsncub. lia. }
        by rewrite take_idemp.
      }
      (* Case: The safe term equal to the entries term. *)
      assert (term = termp) as ->.
      { clear -Hple Hge Htermple Hllep. word. }
      destruct Hcase as [? | Hlenlt]; first done.
      assert (p = uint.nat termp) as ->.
      { clear -Hple Hge Htermple Hllep. lia. }
      iDestruct "Hcmted" as (nidx nidsq) "Hcmted".
      iNamed "Hcmted".
      iDestruct (paxos_inv_impl_nodes_inv with "HinvO") as (termlm) "[Hnodes %Hdomtermlm]".
      iDestruct (nodes_inv_extract_ds_psa with "Hnodes") as (dss bs) "[Hndp Hnodes]".
      iDestruct (big_sepM2_dom with "Hnodes") as %Hdomdp.
      iDestruct (big_sepM2_dom with "Hndp") as %Hdom.
      rewrite dom_map_zip_with_L Hdomdp intersection_idemp_L Hdomtermlm in Hdom.
      symmetry in Hdom.
      iClear "Hndp".
      iDestruct (accepted_proposal_past_nodedecs_impl_prefix with "Hvacpt Hpastd Hnodes")
        as %Horprefix.
      { rewrite Hdom. apply Hmember. }
      { rewrite Hdom. apply Hinnids. }
      { apply Hacpt. }
      iPureIntro.
      assert (Hlogc : prefix logc logpeer).
      { destruct Horprefix as [Hprefix | Hprefix]; first apply Hprefix.
        rewrite (prefix_length_eq _ _ Hprefix); first done.
        rewrite length_take.
        unshelve epose proof (drop_lt_inv logpeer (uint.nat lsnc) _) as Hgt.
        { rewrite Hlogpeer. intros ->. simpl in Hszents. clear -Hszents Hlenlt. word. }
        lia.
      }
      subst logc.
      rewrite -(take_drop (uint.nat lsnc) logpeer) -Hlogpeer.
      f_equal.
      destruct Hlogc as [logtail ->].
      rewrite take_app_le; last first.
      { rewrite length_take. clear -Hlsncub. lia. }
      by rewrite take_idemp.
    }
    iMod ("HinvC" with "HinvO") as "_".
    iAssert (votes_in γ (dom respp') (uint.nat termc) (uint.nat term) (logc ++ ents))%I
      as "Hvotes'".
    { iNamed "Hpromise".
      iNamed "Hvotes".
      iDestruct (big_sepM_insert_2 with "Hpastd Hdss") as "Hdss'".
      iFrame "Hdss'".
      iPureIntro.
      split.
      { by apply map_Forall_insert_2. }
      split.
      { apply latest_term_before_quorum_with_insert_ge.
        { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
        { by rewrite /latest_term_nodedec /latest_term_before_nodedec Hlends in Hlatest. }
        rewrite -latest_term_before_quorum_nodedec_unfold Hlatestq.
        word.
      }
      split.
      { apply length_of_longest_ledger_in_term_insert_Some_length_ge.
        { by rewrite -not_elem_of_dom -Hdomdss not_elem_of_dom. }
        { by rewrite Hacpt. }
        { destruct (decide (termp = term)) as [-> | Hne].
          { (* Case: [termp = term]. *)
            destruct Hcase as [? | Hlonger]; first done.
            rewrite Hlongestq 2!length_app.
            lia.
          }
          { (* Case: [termp < term]. *)
            assert (Hltterm : uint.Z termp < uint.Z term) by word.
            replace (length_of_longest_ledger_in_term _ _) with O; first lia.
            rewrite /length_of_longest_ledger_in_term /length_of_longest_ledger.
            replace (omap _ _) with (∅ : gmap u64 ledger).
            { by rewrite fmap_empty map_fold_empty. }
            apply map_eq.
            intros nidx.
            rewrite lookup_empty lookup_omap.
            set f := mbind nodedec_to_ledger.
            set t := uint.nat termc.
            set p := uint.nat term.
            unshelve epose proof (latest_term_before_quorum_with_None f dss t p _) as Hnone.
            { rewrite -latest_term_before_quorum_nodedec_unfold Hlatestq.
              clear -Hltterm Htermlt.
              word.
            }
            destruct (dss !! nidx) as [dsx |] eqn:Hdsx; last done.
            simpl.
            specialize (Hnone _ _ Hdsx).
            by rewrite /ledger_in_term_with Hnone.
          }
        }
      }
      split.
      { apply map_Exists_insert_2_1. by rewrite Hacpt. }
      { by rewrite 2!dom_insert_L Hdomdss. }
    }
    iFrame "Hpx HiscandP HentspP".
    iFrame "∗ # %".
    iPureIntro.
    split; last lia.
    rewrite dom_insert_L. set_solver.
  Qed.

End collect.
