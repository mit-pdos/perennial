From Perennial.program_proof.mvcc Require Import tuple_common.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (tuple *Tuple) killVersion(tid uint64) bool              *)
(*****************************************************************)
Theorem wp_tuple__killVersion tuple (tid : u64) tidown tidlast vers :
  {{{ own_tuple_phys tuple tidown tidlast vers }}}
    Tuple__killVersion #tuple #tid
  {{{ (ok : bool), RET #ok; own_tuple_phys tuple (U64 0) (int.Z tid + 1) (vers ++ [(tid, true, (U64 0))]) }}}.
Proof.
  iIntros (Φ) "HtuplePhys HΦ".
  iNamed "HtuplePhys".
  wp_call.
  
  (***********************************************************)
  (* verNew := Version{                                      *)
  (*     begin   : tid,                                      *)
  (*     deleted : true,                                     *)
  (* }                                                       *)
  (* tuple.vers = append(tuple.vers, verNew)                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_SliceAppend with "[HversS]"); [done | auto 10 with iFrame |].
  iIntros (vers') "HversS". 
  wp_storeField.

  (***********************************************************)
  (* tuple.tidown = 0                                        *)
  (* tuple.tidlast = tid + 1                                 *)
  (***********************************************************)
  do 2 wp_storeField.

  iModIntro.
  iApply "HΦ".
  unfold own_tuple_phys.
  iExists _.
  iFrame.
  iExactEq "HversS".
  unfold named.
  f_equal.
  by rewrite fmap_app.
Qed.

Definition tuple_killed tuple (tid : u64) (key : u64) γ : iProp Σ :=
  ∃ (tidown tidlast tidgc : u64) (vers : list pver)
    (vchain : list dbval),
    (* physical state is updated, but logical state is not. *)
    let vers' := vers ++ [(tid, true, (U64 0))] in
    "Hphys" ∷ own_tuple_phys tuple (U64 0) (U64 (int.Z tid + 1)) vers' ∗
    "Habst" ∷ own_tuple_abst key tidown tidlast tidgc vers vchain γ ∗
    "%Htid" ∷ ⌜int.Z tidgc ≤ int.Z tid⌝.

(*****************************************************************)
(* func (tuple *Tuple) KillVersion(tid uint64) uint64            *)
(*****************************************************************)
Theorem wp_tuple__KillVersion tuple (tid : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid }}}
    Tuple__KillVersion #tuple #tid
  {{{ (latch : loc) (ret : u64), RET #ret;
      active_tid γ tid sid ∗
      tuple_locked tuple key latch γ ∗
      tuple_killed tuple tid key γ
  }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Hactive HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iNamed "HtupleOwn".
  iNamed "Habst".

  (***********************************************************)
  (* ok := tuple.killVersion(tid)                            *)
  (***********************************************************)
  iNamed "Hphys".
  wp_apply (wp_tuple__killVersion with "[$Htidown $Htidlast Hvers HversS]"); first eauto with iFrame.
  iIntros (ok) "Hphys".
  wp_pures.
  
  (***********************************************************)
  (* var ret uint64                                          *)
  (* if ok {                                                 *)
  (*     ret = common.RET_SUCCESS                            *)
  (* } else {                                                *)
  (*     ret = common.RET_NONEXIST                           *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (retR) "HretR".
  wp_pures.
  replace ok with (bool_decide (ok = true)); last first.
  { case_bool_decide.
    - done.
    - by apply not_true_is_false in H.
  }
  wp_apply (wp_If_join_evar with "[HretR]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    - wp_if_true.
      wp_store.
      iModIntro.
      iSplit; first done.
      replace #0 with #(if b' then 0 else 1) by by rewrite Eb'.
      iNamedAccu.
    - wp_if_false.
      wp_store.
      iModIntro.
      iSplit; first done.
      by rewrite Eb'.
  }
  iIntros "HretR".
  iNamed "HretR".
  wp_pures.
  
  (***********************************************************)
  (* tuple.rcond.Broadcast()                                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_condBroadcast with "[$HrcondC]").
  
  wp_pures.
  wp_load.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (active_ge_min with "HinvgcO Hactive Hgclb") as "%HtidGe".
  iMod ("HinvgcC" with "HinvgcO") as "_".
  iModIntro.
  rewrite ite_apply.
  iApply "HΦ".
  iFrame "# ∗".
  unfold tuple_killed.
  do 5 iExists _.
  iFrame "Hphys".
  iSplit; last done.
  iFrame "% # ∗".
Qed.

End proof.
