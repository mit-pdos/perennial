From Perennial.program_proof.mvcc Require Import tuple_prelude tuple_repr.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func MkTuple() *Tuple                                         *)
(*****************************************************************)
Theorem wp_MkTuple (key : u64) γ p :
  mvcc_inv_gc γ -∗
  mvcc_inv_sst γ p -∗
  {{{ ptuple_auth γ (1/2) key [Nil; Nil] }}}
    MkTuple #()
  {{{ (tuple : loc), RET #tuple; is_tuple tuple key γ }}}.
Proof.
  iIntros "#Hinvgc #Hinv" (Φ) "!> Hvchain HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* tuple := new(Tuple)                                     *)
  (***********************************************************)
  wp_apply (wp_allocStruct).
  { apply zero_val_ty'.
    simpl.
    repeat split.
  }
  iIntros (tuple) "Htuple".
  iDestruct (struct_fields_split with "Htuple") as "Htuple".
  iNamed "Htuple".
  simpl.
  wp_pures.
  
  (***********************************************************)
  (* tuple.latch = new(sync.Mutex)                           *)
  (***********************************************************)
  wp_apply (wp_new_free_lock).
  iIntros (latch) "Hfree".
  wp_storeField.
  
  (***********************************************************)
  (* tuple.rcond = sync.NewCond(tuple.latch)                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_newCond' with "Hfree").
  iIntros (rcond) "[Hfree #HrcondC]".
  wp_storeField.
  
  (***********************************************************)
  (* tuple.owned = false                                     *)
  (* tuple.tidlast = 0                                       *)
  (***********************************************************)
  do 2 wp_storeField.
  
  (***********************************************************)
  (* tuple.vers = make([]Version, 1, 1)                      *)
  (* tuple.vers[0] = Version{                                *)
  (*     deleted : true,                                     *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_new_slice_cap); [auto | word |].
  iIntros (vers) "HversS".
  wp_storeField.
  wp_loadField.
  iDestruct (own_slice_small_acc with "HversS") as "[HversS HversC]".
  wp_apply (wp_SliceSet with "[HversS]").
  { iFrame.
    iPureIntro.
    split; last auto.
    by rewrite lookup_replicate_2; last word.
  }
  iIntros "HversS".
  iDestruct ("HversC" with "HversS") as "HversS".
  wp_pures.
  
  (***********************************************************)
  (* return tuple                                            *)
  (***********************************************************)
  
  (* Obtain [min_tid_lb γ 0]. *)
  iInv "Hinvgc" as "> HinvgcO" "HinvgcC".
  iDestruct (min_tid_lb_zero γ with "[HinvgcO]") as "#Hlb".
  { unfold mvcc_inv_gc_def.
    iApply (big_sepL_mono with "HinvgcO").
    iIntros (sidN sid) "%Hlookup H".
    iNamed "H".
    by eauto.
  }
  iMod ("HinvgcC" with "HinvgcO") as "_".
  
  set P := (own_tuple tuple key γ)%I.
  iMod (alloc_lock mvccN _ latch P with "[$Hfree] [-latch rcond HΦ]") as "#Hlock".
  { iNext.
    unfold P.
    unfold own_tuple.
    iExists false, (W64 1), (W64 0), [(W64 0, true, ""%go)], [Nil; Nil].
    iFrame.
    iSplit.
    { (* Prove [HtupleAbs]. *)
      iPureIntro.
      simpl.
      intros tid Htid.
      assert (H : uint.Z tid = 0 ∨ uint.Z tid = 1) by word.
      destruct H.
      - by replace tid with (W64 0) by word.
      - by replace tid with (W64 1) by word.
    }
    iSplit; first done.
    iSplit.
    { (* Prove [HvchainLen]. *)
      iPureIntro. set_solver.
    }
    iSplit.
    { (* Prove [Hgclb]. *)
      done.
    }
    iSplit.
    { (* Prove [HtidlastGt]. *)
      rewrite Forall_singleton.
      by simpl.
    }
    iPureIntro.
    split.
    { (* Prove [HexistsLt]. *)
      intros tid.
      rewrite Exists_cons.
      left. simpl. word.
    }
    split; [by simpl | done].
  }
  iApply "HΦ".
  do 3 iExists _.
  iMod (readonly_alloc_1 with "latch") as "$".
  iMod (readonly_alloc_1 with "rcond") as "$".
  by iFrame "#".
Qed.

End program.
