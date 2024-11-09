From Perennial.program_proof.mvcc Require Import tuple_prelude tuple_repr.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition post_tuple__Own ts key (ret : u64) γ : iProp Σ :=
  match uint.Z ret with
  | 0 => mods_token γ key ts
  | 200 | 400 => True
  | _ => False
  end.

(*****************************************************************)
(* func (tuple *Tuple) Own(tid uint64) bool                      *)
(*****************************************************************)
Theorem wp_tuple__Own tuple (tid : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid }}}
    Tuple__Own #tuple #tid
  {{{ (ret : u64), RET #ret;
      active_tid γ tid sid ∗
      post_tuple__Own (uint.nat tid) key ret γ
  }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Hactive HΦ".
  iAssert (⌜uint.Z tid > 0⌝)%I with "[Hactive]" as "%Htid".
  { iDestruct "Hactive" as "[_ %Htid]". word. }
  iNamed "Htuple".
  wp_rec. wp_pures.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iNamed "HtupleOwn".
  iNamed "Hphys".
  wp_pures.

  (***********************************************************)
  (* if tid < tuple.tidlast {                                *)
  (*   tuple.latch.Unlock()                                  *)
  (*   return common.RET_UNSERIALIZABLE                      *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hactive]").
    { eauto 15 with iFrame. }
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }

  (***********************************************************)
  (* if tuple.owned {                                        *)
  (*   tuple.latch.Unlock()                                  *)
  (*   return common.RET_RETRY                               *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hactive]").
    { eauto 15 with iFrame. }
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }

  (***********************************************************)
  (* tuple.owned = true                                      *)
  (***********************************************************)
  wp_storeField.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  iNamed "Hrepr".
  iDestruct (vchain_split (1 / 4) (1 / 4) with "Hptuple") as "[Hptuple Hptuple']"; first compute_done.
  wp_apply (wp_Mutex__Unlock with "[-HΦ Hactive Hptuple']").
  { iFrame "Hlock Hlocked".
    iNext.
    iExists true.
    do 4 iExists _.
    iSplitL "Howned Htidlast Hvers HversS".
    { eauto with iFrame. }
    iFrame "∗%".
    iFrame "∗ #".
  }
  wp_pures.
  iModIntro.

  (***********************************************************)
  (* return common.RET_SUCCESS                               *)
  (***********************************************************)
  iApply "HΦ".
  unfold post_tuple__Own.
  iFrame.
  iPureIntro.
  word.
Qed.

End proof.
