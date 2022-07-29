From Perennial.program_proof.mvcc Require Import tuple_common.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition post_tuple__Own ts key (ret : u64) γ : iProp Σ :=
  match int.Z ret with
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
      post_tuple__Own (int.nat tid) key ret γ
  }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Hactive HΦ".
  iAssert (⌜int.Z tid > 0⌝)%I with "[Hactive]" as "%Htid".
  { iDestruct "Hactive" as "[_ %Htid]". iPureIntro. word. }
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
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
    wp_apply (release_spec with "[-HΦ Hactive]").
    { eauto 15 with iFrame. }
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }

  (***********************************************************)
  (* if tuple.tidown != 0 {                                  *)
  (*   tuple.latch.Unlock()                                  *)
  (*   return common.RET_RETRY                               *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (release_spec with "[-HΦ Hactive]").
    { eauto 15 with iFrame. }
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }

  (***********************************************************)
  (* tuple.tidown = tid                                      *)
  (***********************************************************)
  wp_storeField.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  iNamed "Habst".
  iDestruct (vchain_split (1 / 4) (1 / 4) with "Hvchain") as "[Hchain Hvchain']"; first compute_done.
  wp_apply (release_spec with "[-HΦ Hactive Hvchain']").
  { iFrame "Hlock Hlocked".
    iNext.
    iExists tid.
    do 4 iExists _.
    iSplitL "Htidown Htidlast Hvers HversS".
    { eauto with iFrame. }
    iFrame "% ∗".
    case_decide.
    - by rewrite H in Htid.
    - iFrame "# ∗".
  }
  wp_pures.
  iModIntro.

  (***********************************************************)
  (* return common.RET_SUCCESS                               *)
  (***********************************************************)
  iApply "HΦ".
  unfold post_tuple__Own.
  iFrame.
  change (int.Z 0) with 0.
  simpl.
  unfold mods_token.
  iExists vchain.
  iFrame.
  iPureIntro.
  word.
Qed.

End proof.
