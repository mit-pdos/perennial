From Perennial.program_proof.mvcc Require Import txnsite_prelude.
From Perennial.program_proof.mvcc Require Import txnsite_repr tid_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_TxnSite__Activate (site : loc) (sid : u64) γ :
  ⊢ is_txnsite site sid γ -∗
    {{{ True }}}
    <<< ∀∀ (ts : nat), ts_auth γ ts >>>
      TxnSite__Activate #site @ ↑mvccNGC ∪ ↑mvccNTID
    <<< ∃∃ ts', ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
    {{{ (tid : u64), RET #tid; active_tid γ tid sid ∧ ⌜uint.nat tid = ts'⌝ }}}.
Proof.
  (*@ func (site *TxnSite) activate() uint64 {                                @*)
  (*@     site.latch.Lock()                                                   @*)
  (*@                                                                         @*)
  iIntros "#Hsite !>" (Φ) "_ HAU".
  iNamed "Hsite".
  wp_rec. wp_pures.
  
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked HsiteOwn]".
  (* replace (W64 (Z.of_nat _)) with sid by word.  *)
  iNamed "HsiteOwn".
  wp_pures.

  (*@     var t uint64                                                        @*)
  (*@     t = tid.GenTID(site.sid)                                            @*)
  (*@                                                                         @*)
  wp_apply wp_ref_of_zero; first done.
  iIntros (tidRef) "HtidRef".
  wp_pures.
  wp_loadField.
  wp_apply (wp_GenTID with "Hinvtid Hsidtok").
  { done. }
  iInv "Hinvgc" as "> HinvgcO" "HinvgcC".
  (* Open GC invariant. *)
  iDestruct (big_sepL_lookup_acc with "HinvgcO") as "[HinvsiteO HinvsiteC]".
  { by apply sids_all_lookup. }
  iNamed "HinvsiteO".
  (* Obtain [ts_auth] from AU. *)
  iMod ncfupd_mask_subseteq as "Hadjust".
  2: iMod "HAU" as (ts) "[Hts HAUC]".
  1: solve_ndisj.
  (* Deduce [S tidmax ≤ ts]. *)
  iDestruct (ts_auth_lb_le with "Hts Htslb") as %Hle.
  iModIntro.
  iExists ts.
  iFrame "Hts".
  iIntros "%ts' [Hts' %Hgz]".
  (* Insert [ts'] into the set of active tids. *)
  iDestruct (site_active_tids_agree with "HactiveA HactiveAuth") as %->.
  iMod (site_active_tids_insert ts' with "HactiveA HactiveAuth") as
    "(HactiveA & HactiveAuth & HactiveFrag)".
  { intros contra.
    apply set_Forall_union_inv_2 in Hmax.
    apply Hmax in contra. lia.
  }
  (* Obtain a new lower bound on [tidmax]. *)
  iClear "Htslb".
  iDestruct (ts_witness with "Hts'") as "#Htslb".
  iMod ("HAUC" with "[Hts']") as "HΦ"; first by eauto with iFrame.
  (* Close GC invariant. *)
  iDestruct ("HinvsiteC" with "[HactiveA HminA]") as "Hinvsite".
  { iExists _, _, ts'.
    iFrame "∗ Htslb".
    iPureIntro.
    apply set_Forall_union_inv_1 in Hmax as Hminmax.
    rewrite set_Forall_singleton in Hminmax.
    apply set_Forall_union_inv_2 in Hmax.
    split.
    { apply set_Forall_union; last done.
      rewrite set_Forall_singleton. lia.
    }
    { apply set_Forall_union.
      { rewrite set_Forall_singleton. lia. }
      { apply set_Forall_union; first by rewrite set_Forall_singleton.
        apply (set_Forall_impl _ _ _ Hmax). lia.
      }
    }
  }
  iMod "Hadjust" as "_".
  iMod ("HinvgcC" with "Hinvsite") as "_".
  iModIntro.
  iIntros (tid) "[%Etid Hsidtok]".
  wp_store.

  (*@     // Assume TID never overflow.                                       @*)
  (*@     machine.Assume(t < 18446744073709551615)                            @*)
  (*@                                                                         @*)
  wp_load.
  wp_apply wp_Assume.
  iIntros "%Htidmax".
  apply bool_decide_eq_true_1 in Htidmax.

  (*@     site.tids = append(site.tids, t)                                    @*)
  (*@                                                                         @*)
  wp_load.
  wp_loadField.
  wp_apply (typed_slice.wp_SliceAppend (V := u64) with "HactiveL").
  iIntros (tidsactive') "HactiveL".
  wp_storeField.
  wp_loadField.
  
  (*@     site.latch.Unlock()                                                 @*)
  (*@                                                                         @*)
  wp_apply (wp_Mutex__Unlock with "[-HΦ HtidRef HactiveFrag]").
  { iFrame "Hlock Hlocked".
    iNext.
    do 3 iExists _.
    iFrame.
    iPureIntro.
    split.
    { (* Prove [HactiveLM]. *)
      rewrite fmap_app list_to_set_app_L HactiveLM.
      simpl.
      set_solver.
    }
    { (* Prove [HactiveND]. *)
      apply NoDup_app.
      split; first done.
      split; last apply NoDup_singleton.
      intros tidx Helem contra.
      rewrite list_elem_of_singleton in contra.
      apply set_Forall_union_inv_2 in Hmax.
      assert (Helem' : uint.nat tidx ∈ tidsactiveM).
      { rewrite -HactiveLM.
        rewrite elem_of_list_to_set.
        apply (list_elem_of_fmap_2 (λ x : u64, uint.nat x)).
        done.
      }
      apply Hmax in Helem'.
      rewrite contra Etid in Helem'.
      lia.
    }
  }
  wp_load.
  
  (*@     return t                                                            @*)
  (*@ }                                                                       @*)
  iApply "HΦ".
  iModIntro.
  iSplit; last done.
  unfold active_tid.
  rewrite Etid.
  iFrame. word.
Qed.

End program.
