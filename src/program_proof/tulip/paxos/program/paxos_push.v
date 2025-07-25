From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr paxos_cquorum.
From Perennial.program_proof.tulip.program.util Require Import sort.
From Goose.github_com.mit_pdos.tulip Require Import paxos util.

Section push.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__push (px : loc) (nidme termc : u64) nids γ :
    nidme ∈ nids ->
    know_paxos_inv γ nids -∗
    {{{ own_paxos_leading_with_termc px nidme termc nids γ }}}
      Paxos__push #px
    {{{ (lsnc : u64) (pushed : bool), RET (#lsnc, #pushed);
        own_paxos_leading_with_termc px nidme termc nids γ ∗
        if pushed
        then ∃ logc, safe_ledger_above γ nids (uint.nat termc) logc ∗
                     ⌜length logc = uint.nat lsnc⌝
        else True
    }}}.
  Proof.
    iIntros (Hnidme) "#Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) push() (uint64, bool) {                                @*)
    (*@     if !px.cquorum(uint64(len(px.lsnpeers)) + 1) {                      @*)
    (*@         // Nothing should be done without responses from some quorum of nodes. @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl".
    wp_loadField.
    wp_apply (wp_MapLen with "Hlsnpeers").
    iIntros "[%Hszlsnpeers Hlsnpeers]".
    wp_apply (wp_Paxos__cquorum with "Hsc").
    iIntros "Hsc".
    (* Not using [wp_if_destruct] to prevent it eating equality about [nids]. *)
    case_bool_decide as Hqsize; wp_pures; last first.
    { wp_pures.
      iApply "HΦ".
      iFrame "Hcand".
      by iFrame "∗ # %".
    }
    
    (*@     var lsns = make([]uint64, 0, px.sc)                                 @*)
    (*@                                                                         @*)
    iNamed "Hsc".
    wp_loadField.
    wp_apply wp_NewSliceWithCap.
    { word. }
    iIntros (lsnsinitP) "Hlsns".
    wp_apply wp_ref_to; first done.
    iIntros (lsnsPP) "HlsnsPP".

    (*@     for _, lsn := range(px.lsnpeers) {                                  @*)
    (*@         lsns = append(lsns, lsn)                                        @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    rewrite uint_nat_W64_0 /=.
    set P := (λ (m : gmap u64 u64), ∃ (lsnsP' : Slice.t) (lsns' : list u64),
          "HlsnsP"  ∷ lsnsPP ↦[slice.T uint64T] (to_val lsnsP') ∗
          "Hlsns"   ∷ own_slice lsnsP' uint64T (DfracOwn 1) lsns' ∗
          "%Hlsns'" ∷ ⌜(map_to_list m).*2 ≡ₚ lsns'⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Hlsnpeers [$HlsnsPP $Hlsns]").
    { set_solver. }
    { (* Loop body. *)
      clear Φ.
      iIntros (m nid lsn Φ) "!> (HP & %Hnone & %Hlsn) HΦ".
      iNamed "HP".
      wp_load.
      wp_apply (wp_SliceAppend with "Hlsns").
      iIntros (lsnsP'') "Hlsns".
      wp_store.
      iApply "HΦ".
      iFrame.
      iPureIntro.
      rewrite map_to_list_insert; last apply Hnone.
      rewrite fmap_cons Hlsns' /=.
      apply Permutation_cons_append.
    }
    iIntros "[Hlsnpeers HP]".
    iNamed "HP". clear P.

    (*@     util.Sort(lsns)                                                     @*)
    (*@                                                                         @*)
    wp_load.
    wp_apply (wp_Sort with "Hlsns").
    iIntros (lsnsorts) "(Hlsns & %Hsorted & %Hperm)".
    wp_load.
    wp_apply wp_slice_len.
    wp_loadField.
    wp_load.
    iDestruct (own_slice_sz with "Hlsns") as %Hszsorted.
    rewrite Hperm -Hlsns' length_fmap length_map_to_list in Hszsorted.
    rewrite word.unsigned_add Hsc in Hqsize.
    set i := word.sub _ _.
    assert (is_Some (lsnsorts !! uint.nat i)) as [lsn Hlsn].
    { apply lookup_lt_is_Some_2.
      subst i.
      rewrite Hperm -Hlsns' length_fmap length_map_to_list.
      rewrite word.unsigned_sub_nowrap; last word.
      word.
    }
    iDestruct (own_slice_to_small with "Hlsns") as "Hlsns".
    wp_apply (wp_SliceGet with "[$Hlsns]").
    { iPureIntro. apply Hlsn. }
    iIntros "Hlsns".
    wp_pures.

    (*@     if lsn < px.lsnc {                                                  @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_if_destruct.
    { wp_pures.
      iApply "HΦ".
      iFrame "Hcand".
      by iFrame "∗ # %".
    }

    (*@     return lsn, true                                                    @*)
    (*@ }                                                                       @*)
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iSplit.
    { iFrame "Hcand".
      by iFrame "∗ # %".
    }
    iDestruct (own_slice_sz with "Hlog") as %Hszlog.
    set lsnpeersq := filter (λ x, (uint.nat lsn ≤ uint.nat x.2)%nat) lsnpeers.
    set nidpeersq := dom lsnpeersq.
    iDestruct "Haocm" as (aocm) "Haocm".
    set aocmq := filter (λ x, x.1 ∈ nidpeersq) aocm.
    destruct (decide (map_Exists (λ _ b, b = false) aocmq)) as [Hsomecmted | Hallacpted].
    { (* Case: Some peer in the quorum has already committed up to the reported LSN. *)
      destruct Hsomecmted as (nidx & b & Hfalse & ->).
      unshelve epose proof (lookup_weaken _ aocm _ _ Hfalse _) as Hnidx.
      { apply map_filter_subseteq. }
      iDestruct (big_sepM2_dom with "Haocm") as %Hdom.
      subst aocmq.
      apply map_lookup_filter_Some_1_2 in Hfalse.
      subst nidpeersq.
      rewrite elem_of_dom /= in Hfalse.
      destruct Hfalse as [lsncmted Hlsncmted].
      subst lsnpeersq.
      rewrite map_lookup_filter_Some /= in Hlsncmted.
      destruct Hlsncmted as [Hlsncmted Hlenge].
      iDestruct (big_sepM2_lookup with "Haocm") as "Hcmtedpeer".
      { apply Hlsncmted. }
      { apply Hnidx. }
      iDestruct "Hcmtedpeer" as (logx) "[Hlogx %Hlenlogx]".
      iDestruct (safe_ledger_above_weaken (take (uint.nat lsn) logx) with "Hlogx") as "Hcmted'".
      { apply prefix_take. }
      iFrame "Hcmted'".
      iPureIntro.
      rewrite length_take.
      lia.
    }
    (* Case: All peers in the quorum have accepted up to their reported LSNs. *)
    rewrite map_not_Exists in Hallacpted.
    set logc := take (uint.nat lsn) log.
    iExists logc.
    iSplit; last first.
    { iPureIntro.
      rewrite length_take.
      apply list_elem_of_lookup_2 in Hlsn.
      rewrite Hperm -Hlsns' in Hlsn.
      apply list_elem_of_lookup_1 in Hlsn as [j Hlsn].
      rewrite list_lookup_fmap in Hlsn.
      destruct (map_to_list lsnpeers !! j) as [[nidy lsny] |] eqn:Hy; last done.
      inv Hlsn.
      apply list_elem_of_lookup_2, elem_of_map_to_list in Hy.
      specialize (Hlelog _ _ Hy). simpl in Hlelog.
      clear -Hlelog. word.
    }
    iExists (uint.nat termc).
    iSplit; last done.
    set nidsq := ({[nidme]} ∪ nidpeersq).
    iExists nidme, nidsq.
    iDestruct (accepted_proposal_lb_weaken logc with "Hacpted") as "Hacpted'".
    { apply prefix_take. }
    subst terml.
    iFrame "Hacpted'".
    iSplit.
    { rewrite big_sepM2_alt.
      iDestruct "Haocm" as "[%Hdom Haocm]".
      iDestruct (big_sepM_dom_subseteq_difference _ _ nidpeersq with "Haocm") as
        (m) "([%Hdomm %Hm] & Haocm' & _)".
      { rewrite dom_map_zip_with -Hdom intersection_idemp_L.
        apply subseteq_dom, map_filter_subseteq.
      }
      iApply (big_sepS_insert_2 with "[] []").
      { by iFrame "Hacpted'". }
      rewrite big_sepS_big_sepM.
      iApply (big_sepM_impl_dom_eq with "Haocm'"); first done.
      iIntros (nid [x a] lsnp Hxa Hlsnp) "!> Hacpt".
      assert (Ha : aocmq !! nid = Some a).
      { rewrite map_lookup_filter_Some.
        split.
        { pose proof (lookup_weaken _ _ _ _ Hxa Hm) as Hlookup.
          rewrite map_lookup_zip_Some in Hlookup.
          by destruct Hlookup as [_ ?].
        }
        by rewrite elem_of_dom.
      }
      specialize (Hallacpted _ _ Ha).
      rewrite not_false_iff_true in Hallacpted.
      subst a. simpl.
      rewrite map_lookup_filter_Some /= in Hlsnp.
      destruct Hlsnp as [Hlsnp Hgelsn].
      rewrite map_subseteq_spec in Hm.
      specialize (Hm _ _ Hxa).
      rewrite map_lookup_zip_Some /= in Hm.
      destruct Hm as [Hx _].
      rewrite Hlsnp in Hx.
      inv Hx.
      iApply (accepted_proposal_length_lb_weaken with "Hacpt").
      rewrite length_take.
      clear -Hgelsn. lia.
    }
    iPureIntro.
    split; last apply Hnidme.
    split.
    { apply union_least; first set_solver.
      trans (dom lsnpeers); [apply dom_filter_subseteq | set_solver].
    }
    rewrite /cquorum_size.
    rewrite size_union; last first.
    { rewrite disjoint_singleton_l.
      assert (Hsubseteq : nidpeersq ⊆ nids ∖ {[nidme]}).
      { subst nidpeersq lsnpeersq.
        trans (dom lsnpeers); [apply dom_filter_subseteq | apply Hinclnids].
      }
      clear -Hsubseteq.
      set_solver.
    }
    rewrite size_singleton.
    set lsndrops := drop (uint.nat i) lsnsorts.
    assert (Hlensorts : size nids / 2 ≤ length lsndrops).
    { rewrite length_drop.
      rewrite Hperm -Hlsns' length_fmap length_map_to_list.
      rewrite word.unsigned_sub_nowrap; last word.
      word.
    }
    rewrite -Hlsns' in Hperm.
    (* Key to this proof: Obtain from [lsnsorts] an inversion [nlsorts] with
    node IDs, allowing proof of the following [submseteq] relation. We might be
    able to simplify the proof by eliminating the detour using [filter] to
    define the node IDs quorum, but define it directly using the [nlsorts]. *)
    apply Permutation_map_inv in Hperm as (nlsorts & Hnlsorts & Hperm).
    set nldrops := drop (uint.nat i) nlsorts.
    assert (Hincl : nldrops ⊆+ map_to_list lsnpeersq).
    { apply NoDup_submseteq.
      { subst nldrops.
        apply (NoDup_suffix _ nlsorts); first apply suffix_drop.
        rewrite -Hperm.
        apply NoDup_map_to_list.
      }
      intros nlx Hnlx.
      assert (Hinsorts : nlx ∈ nlsorts).
      { apply (subseteq_drop (uint.nat i) nlsorts _ Hnlx). }
      rewrite -Hperm in Hinsorts.
      destruct nlx as [nidx lsnx].
      rewrite elem_of_map_to_list in Hinsorts.
      rewrite elem_of_map_to_list.
      rewrite map_lookup_filter_Some /=.
      split; first apply Hinsorts.
      apply list_elem_of_lookup in Hnlx as [j Hnlx].
      subst nldrops.
      rewrite lookup_drop /= in Hnlx.
      assert (lsnsorts !! (uint.nat i + j)%nat = Some lsnx) as Hlsnx.
      { by rewrite Hnlsorts list_lookup_fmap Hnlx /=. }
      unshelve epose proof (Hsorted _ _ _ _ _ Hlsn Hlsnx) as Hle; first lia.
      word.
    }
    assert (Hsizele : length lsndrops ≤ length (map_to_list lsnpeersq).*2).
    { apply submseteq_length in Hincl.
      revert Hincl.
      rewrite 2!length_drop Hnlsorts 2!length_fmap.
      word.
    }
    subst nidpeersq.
    rewrite length_fmap length_map_to_list in Hsizele.
    rewrite size_dom.
    clear -Hsizele Hlensorts.
    word.
  Qed.

End push.
