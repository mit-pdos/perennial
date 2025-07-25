From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import prepare unprepare.
(* import for [local_gid_token] *)
From Perennial.program_proof.tulip.program.txn Require Import res.
From Perennial.program_proof.tulip.program.backup Require Import
  btcoord_repr bgcoord_prepare.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupTxnCoordinator__stabilize tcoord ts γ :
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__stabilize #tcoord
    {{{ (status : txnphase) (valid : bool), RET (#(txnphase_to_u64 status), #valid); 
        own_backup_tcoord tcoord ts γ ∗
        if valid then safe_txnphase γ ts status else True
    }}}.
  Proof.
    iIntros (Φ) "Htcoord HΦ".
    wp_rec.

    (*@ func (tcoord *BackupTxnCoordinator) stabilize() (uint64, bool) {        @*)
    (*@     ts := tcoord.ts                                                     @*)
    (*@     rank := tcoord.rank                                                 @*)
    (*@     ptgs := tcoord.ptgs                                                 @*)
    (*@                                                                         @*)
    iNamed "Htcoord". iNamed "Hts". iNamed "Hrank". iNamed "Hptgs".
    do 3 wp_loadField.

    (*@     mu := new(sync.Mutex)                                               @*)
    (*@     cv := sync.NewCond(mu)                                              @*)
    (*@     // Number of groups that have responded (i.e., groups whose prepare status @*)
    (*@     // is determined).                                                  @*)
    (*@     var nr uint64 = 0                                                   @*)
    (*@     // Number of groups that have prepared.                             @*)
    (*@     var np uint64 = 0                                                   @*)
    (*@     var st uint64 = tulip.TXN_PREPARED                                  @*)
    (*@     var vd bool = true                                                  @*)
    (*@                                                                         @*)
    wp_apply wp_new_free_lock.
    iIntros (muP) "Hfree".
    wp_apply (wp_newCond' with "Hfree").
    iIntros (cvP) "[Hfree #Hcv]".
    wp_apply wp_ref_to; first by auto.
    iIntros (nrP) "HnrP".
    wp_apply wp_ref_to; first by auto.
    iIntros (npP) "HnpP".
    wp_apply wp_ref_to; first by auto.
    iIntros (stP) "HstP".
    wp_apply wp_ref_to; first by auto.
    iIntros (vdP) "HvdP".
    wp_pures.
    (* Allocate exclusive tokens to prove freshness of response. *)
    iApply fupd_wp.
    iMod (local_gid_tokens_alloc ptgs) as (α) "Htks".
    iModIntro.
    (* Establish the lock invariant. *)
    set I := (∃ (np nr : u64) (st : txnphase) (vd : bool) (gids : gset u64),
                 let allprep := vd && bool_decide (st = TxnPrepared) in
                 "HnpP" ∷ npP ↦[uint64T] #np ∗
                 "HnrP" ∷ nrP ↦[uint64T] #nr ∗
                 "HstP" ∷ stP ↦[uint64T] #(txnphase_to_u64 st) ∗
                 "HvdP" ∷ vdP ↦[boolT] #vd ∗
                 "Htks" ∷ ([∗ set] gid ∈ gids, local_gid_token α gid) ∗
                 "#Hst" ∷ (match st with
                           | TxnPrepared => [∗ set] gid ∈ gids, is_group_prepared γ gid ts
                           | TxnCommitted => (∃ wrs, is_txn_committed γ ts wrs)
                           | TxnAborted => is_txn_aborted γ ts
                           end) ∗
                 "%Hgidsincl" ∷ ⌜gids ⊆ ptgs⌝ ∗
                 "%Hsizegids" ∷ ⌜size gids = uint.nat np⌝ ∗
                 "%Hnpnr"     ∷ ⌜if allprep then np = nr else True⌝)%I.
    iApply fupd_wp.
    iMod (alloc_lock tulipNS _ _ I with "Hfree [HnpP HnrP HstP HvdP]") as "#Hmu".
    { iModIntro.
      iExists (W64 0), (W64 0), TxnPrepared, true, ∅.
      iFrame.
      iSplit; first by iApply big_sepS_empty.
      iSplit; first by iApply big_sepS_empty.
      iPureIntro.
      case_bool_decide; done.
    }
    iModIntro.

    (*@     for _, gid := range(ptgs) {                                         @*)
    (*@                                                                         @*)
    iDestruct "Hptgs" as (ptgsL) "(#HptgsL & %HptgsL & %Hnd)".
    set P := (λ (i : u64),
                "Hgcoords" ∷ own_backup_tcoord_gcoords tcoord ptgs rk ts γ ∗
                "Htks" ∷ [∗ set] gid ∈ list_to_set (drop (uint.nat i) ptgsL), local_gid_token α gid)%I.
    iDestruct (own_slice_small_sz with "HptgsL") as %Hlenptgs.
    wp_apply (wp_forSlice P with "[] [$HptgsL $Hgcoords Htks]"); last first; first 1 last.
    { by rewrite uint_nat_W64_0 drop_0 HptgsL. }
    { clear Φ.

      (*@         gcoord := tcoord.gcoords[gid]                                   @*)
      (*@                                                                         @*)
      iIntros (i gid Φ) "!> (HP & %Hinbound & %Hgid) HΦ".
      iNamed "HP". iNamed "Hgcoords".
      wp_loadField.
      assert (Hinptgs : gid ∈ ptgs).
      { apply list_elem_of_lookup_2 in Hgid.
        clear -Hgid HptgsL.
        set_solver.
      }
      iNamed "Hwrs".
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrs)) as Hdom.
        rewrite -Hvptgs in Hdom.
        clear -Hdom Hinptgs.
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

        (*@             stg, vdg := gcoord.Prepare(ts, rank, ptgs)                  @*)
        (*@                                                                         @*)
        iModIntro.
        wp_apply (wp_BackupGroupCoordinator__Prepare).
        { rewrite HtsW. apply Hvts. }
        { rewrite HtsW. by iFrame "Hlnrzed". }
        { rewrite HtsW. by iFrame "# %". }
        { by iFrame "# %". }
        { by rewrite HtsW HrkW. }
        iIntros (stg vdg) "#Hsafe".
        wp_pures.
        iAssert (∃ pwrs, safe_txn_pwrs γ gid ts pwrs)%I as "#Hsafepwrs".
        { iExists (wrs_group gid wrs).
          iFrame "Hwrs".
          iPureIntro.
          unshelve epose proof (elem_of_ptgroups_non_empty gid wrs _) as Hne.
          { by rewrite -Hvptgs. }
          done.
        }

        (*@             mu.Lock()                                                   @*)
        (*@             nr += 1                                                     @*)
        (*@             if !vdg {                                                   @*)
        (*@                 vd = false                                              @*)
        (*@             } else if stg == tulip.TXN_PREPARED {                       @*)
        (*@                 np += 1                                                 @*)
        (*@             } else {                                                    @*)
        (*@                 st = stg                                                @*)
        (*@             }                                                           @*)
        (*@             mu.Unlock()                                                 @*)
        (*@             cv.Signal()                                                 @*)
        (*@         }()                                                             @*)
        (*@     }                                                                   @*)
        (*@                                                                         @*)
        wp_apply (wp_Mutex__Lock with "Hmu").
        iIntros "[Hlocked HI]".
        iNamed "HI".
        wp_load. wp_store.
        destruct vdg; wp_pures; last first.
        { (* Case: [vdg = false]. *)
          wp_store.
          wp_apply (wp_Mutex__Unlock with "[-]").
          { iFrame "Hmu Hlocked HnpP HnrP HstP HvdP".
            iModIntro.
            iFrame "∗ # %".
          }
          wp_pures.
          by wp_apply (wp_Cond__Signal with "Hcv").
        }
        rewrite HtsW.
        destruct stg eqn:Hstg; wp_pures.
        { (* Case: [TxnPrepared] *)
          wp_load. wp_store.
          iAssert (|={⊤}=> is_group_prepared γ gid ts)%I as "Hprepared".
          { iInv "Hinv" as "> HinvO" "HinvC".
            iNamed "HinvO".
            iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
            { apply Hin. }
            iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]".
            { apply Hin. }
            iDestruct "Hsafe" as "[Hqp Hqv]".
            iDestruct "Hsafepwrs" as (pwrs) "Hsafepwrs".
            iMod (group_inv_prepare with "Hqv Hqp Hsafepwrs Htxnsys Hkeys Hrg Hgroup")
              as "(Htxnsys & Hkeys & Hrg & Hgroup & #Hprepared)".
            iDestruct ("HrgsC" with "Hrg") as "Hrgs".
            iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
            by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
          }
          iMod "Hprepared" as "#Hprepared".
          wp_apply (wp_Mutex__Unlock with "[-]").
          { iFrame "Hmu Hlocked HnpP HnrP HstP HvdP".
            iModIntro.
            iAssert (⌜gid ∉ gids⌝)%I as %Hnotin.
            { iIntros (Hgidin).
              iDestruct (big_sepS_elem_of with "Htks") as "Htk'"; first apply Hgidin.
              by iDestruct (local_gid_token_ne with "Htk Htk'") as %?.
            }
            iExists ({[gid]} ∪ gids).
            iSplitL "Htk Htks".
            { iApply (big_sepS_insert_2 with "Htk Htks"). }
            iSplit.
            { destruct st; [| done | done].
              by iApply big_sepS_insert_2.
            }
            iPureIntro.
            { split.
              { clear -Hgidsincl Hinptgs. set_solver. }
              split.
              { rewrite size_union; last set_solver.
                rewrite size_singleton Hsizegids.
                assert (Hszgids : (size gids ≤ size gids_all)%nat).
                { apply subseteq_size. etrans; first apply Hgidsincl.
                  rewrite Hvptgs.
                  apply subseteq_ptgroups.
                }
                pose proof size_gids_all as Hszgidsall.
                clear -Hszgids Hszgidsall Hsizegids. word.
              }
              set b := _ && _ in Hnpnr *.
              by destruct b; first rewrite Hnpnr.
            }
          }
          by wp_apply (wp_Cond__Signal with "Hcv").
        }
        { (* Case [TxnCommitted]. *)
          wp_store.
          wp_apply (wp_Mutex__Unlock with "[-]").
          { iFrame "Hmu Hlocked ∗".
            iModIntro.
            iExists TxnCommitted.
            iFrame "∗ #".
            iPureIntro.
            do 2 (split; first done).
            by rewrite bool_decide_eq_false_2; [rewrite andb_false_r |].
          }
          by wp_apply (wp_Cond__Signal with "Hcv").
        }
        { (* Case [TxnAborted]. *)
          wp_store.
          iAssert (|={⊤}=> is_txn_aborted γ ts)%I as "Habted".
          { iDestruct "Hsafe" as "[? | Hsafe]"; first done.
            iInv "Hinv" as "> HinvO" "HinvC".
            iNamed "HinvO".
            iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
            { apply Hin. }
            iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]".
            { apply Hin. }
            iDestruct "Hsafepwrs" as (pwrs) "Hsafepwrs".
            iMod (txnsys_group_inv_unprepare with "Hsafe Hsafepwrs Hrg Hgroup Htxnsys")
              as "(Hrg & Hgroup & Htxnsys & #Habted)".
            iDestruct ("HrgsC" with "Hrg") as "Hrgs".
            iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
            iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
            done.
          }
          iMod "Habted" as "#Habted".
          wp_apply (wp_Mutex__Unlock with "[-]").
          { iFrame "Hmu Hlocked ∗".
            iModIntro.
            iExists TxnAborted.
            iFrame "∗ #".
            iPureIntro.
            do 2 (split; first done).
            by rewrite bool_decide_eq_false_2; [rewrite andb_false_r |].
          }
          by wp_apply (wp_Cond__Signal with "Hcv").
        }
      }
      iApply "HΦ".
      iFrame "∗ # %".
      rewrite uint_nat_word_add_S; last first.
      { clear -Hinbound. word. }
      done.
    }
    iIntros "[HP _]".
    subst P. iNamed "HP".

    (*@     // Wait until either a higher-ranked coordinator is found (i.e., as @*)
    (*@     // indicated by @valid = false), or all participant groups have responded. @*)
    (*@     //                                                                  @*)
    (*@     // A note on the difference between this method and @txn.preapre. Unlike @*)
    (*@     // @txn.prepare() where it's OK (and good for performance) to terminate this @*)
    (*@     // phase once the transaction status is determined, the backup txn  @*)
    (*@     // coordinator should wait until it finds out the status of all participant @*)
    (*@     // groups to finalize the transaction outcome for every group.      @*)
    (*@     mu.Lock()                                                           @*)
    (*@                                                                         @*)
    wp_apply (wp_Mutex__Lock with "Hmu").
    iIntros "[Hlocked HI]".
    wp_pures.

    (*@     for vd && nr != uint64(len(ptgs)) {                                 @*)
    (*@         cv.Wait()                                                       @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (* Different from [I] in [Hlocked] and [Hcond]. *)
    set P := (λ cont : bool,
                ∃ (np nr : u64) (st : txnphase) (vd : bool) (gids : gset u64),
                  let allprep := vd && bool_decide (st = TxnPrepared) in
                  "HnpP" ∷ npP ↦[uint64T] #np ∗
                  "HnrP" ∷ nrP ↦[uint64T] #nr ∗
                  "HstP" ∷ stP ↦[uint64T] #(txnphase_to_u64 st) ∗
                  "HvdP" ∷ vdP ↦[boolT] #vd ∗
                  "Htks" ∷ ([∗ set] gid ∈ gids, local_gid_token α gid) ∗
                  "Hlocked" ∷ locked #muP ∗
                  "#Hst" ∷ (match st with
                            | TxnPrepared => [∗ set] gid ∈ gids, is_group_prepared γ gid ts
                            | TxnCommitted => (∃ wrs, is_txn_committed γ ts wrs)
                            | TxnAborted => is_txn_aborted γ ts
                            end) ∗
                  "%Hgidsincl" ∷ ⌜gids ⊆ ptgs⌝ ∗
                  "%Hsizegids" ∷ ⌜size gids = uint.nat np⌝ ∗
                  "%Hnpnr"     ∷ ⌜(if allprep then np = nr else True)⌝ ∗
                  "%Hcond"     ∷ ⌜(if cont
                                   then True
                                   else vd = false ∨ uint.nat nr = length ptgsL)⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [Hlocked HI]"); last first; first 1 last.
    { iNamed "HI". iFrame "∗ # %". }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      wp_load.
      destruct vd eqn:Hvd; wp_pures.
      { wp_load.
        wp_apply wp_slice_len.
        wp_pures.
        set c := bool_decide _.
        destruct c eqn:Hsize; wp_pures.
        { iApply "HΦ".
          iFrame "∗ # %".
          iPureIntro.
          right.
          rewrite bool_decide_eq_true in Hsize.
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
      by left.
    }
    iClear "Htks".
    iNamed 1.

    (*@     // Use the invariant saying that "if @st = TXN_PREPARED, then @np = @nr" to @*)
    (*@     // establish the postcondition.                                     @*)
    (*@                                                                         @*)
    (*@     status := st                                                        @*)
    (*@     valid := vd                                                         @*)
    (*@     mu.Unlock()                                                         @*)
    (*@                                                                         @*)
    do 2 wp_load.
    wp_apply (wp_Mutex__Unlock with "[Hlocked HnpP HnrP HstP HvdP Htks]").
    { by iFrame "Hmu Hlocked ∗ # %". }

    (*@     return status, valid                                                @*)
    (*@ }                                                                       @*)
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame "∗ # %".
    destruct vd; last done.
    destruct st; [| done | done].
    iNamed "Hwrs".
    iFrame "Hwrs".
    assert (gids = ptgroups (dom wrs)) as ->; last done.
    destruct Hcond as [Hcontra | Hnr]; first done.
    rewrite /= bool_decide_eq_true_2 in Hnpnr; last done. subst nr.
    rewrite -Hvptgs.
    apply set_subseteq_size_eq; first apply Hgidsincl.
    rewrite -HptgsL size_list_to_set; last apply Hnd.
    clear -Hsizegids Hnr. lia.
  Qed.

End program.
