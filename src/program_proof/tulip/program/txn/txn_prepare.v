From Perennial.program_proof.tulip.invariance Require Import prepare unprepare.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import res txn_repr txn_setptgs.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_prepare.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

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
    iIntros "[Hwrs Hptgs]".

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
                "Htks" ∷ [∗ set] gid ∈ list_to_set (drop (uint.nat i) ptgsL), local_gid_token α gid)%I.
    iDestruct (own_slice_small_sz with "HptgsL") as %Hlenptgs.
    wp_apply (wp_forSlice P with "[] [$HptgsL $HpwrsmP $Hgcoords Htks]"); last first; first 1 last.
    { by rewrite uint_nat_W64_0 drop_0 HptgsL. }
    { clear Φ.

      (*@         gcoord := txn.gcoords[gid]                                      @*)
      (*@         pwrs := txn.wrs[gid]                                            @*)
      (*@                                                                         @*)
      iIntros (i gid Φ) "!> (HP & %Hinbound & %Hgid) HΦ".
      iNamed "HP". iNamed "Hgcoords".
      wp_loadField.
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrs)) as Hdom.
        apply list_elem_of_lookup_2 in Hgid.
        clear -Hdom Hgid HptgsL.
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
      { rewrite -HptgsL elem_of_list_to_set. by apply list_elem_of_lookup_2 in Hgid. }

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
        iAssert (safe_txn_pwrs γ gid tid pwrs)%I as "#Hsafepwrs".
        { iFrame "Htxnwrs".
          iPureIntro.
          specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
          pose proof (elem_of_ptgroups_non_empty _ _ Hvg) as Hne.
          rewrite -Hwrsg in Hne.
          done.
        }
        iAssert (safe_txn_ptgs γ tid (ptgroups (dom wrs)))%I as "#Hsafeptgs".
        { by iFrame "Htxnwrs". }
        wp_apply (wp_GroupCoordinator__Prepare with "[] [] [] Hpwrs [] Hgcoordabs").
        { by rewrite Htsword. }
        { by rewrite Htsword. }
        { by rewrite Htsword. }
        { by iFrame "# %". }
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
    iIntros "[HP _]".
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
                                        | TxnPrepared => uint.nat np = length ptgsL
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
      rewrite -HptgsL size_list_to_set; last apply Hnd.
      clear -Hsizegids Hcond. lia.
    }
    by iFrame "Hsafe ∗ # %".
  Qed.

End program.
