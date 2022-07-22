From Perennial.program_proof.mvcc Require Import tuple_common.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (tuple *Tuple) appendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__appendVersion tuple (tid : u64) (val : u64) tidown tidlast vers :
  {{{ own_tuple_phys tuple tidown tidlast vers }}}
    Tuple__appendVersion #tuple #tid #val
  {{{ RET #(); own_tuple_phys tuple (U64 0) (U64 (int.Z tid + 1)) (vers ++ [(tid, false, val)]) }}}.
Proof.
  iIntros (Φ) "Hphys HΦ".
  iNamed "Hphys".
  wp_call.
  
  (***********************************************************)
  (* verNew := Version{                                      *)
  (*     begin   : tid,                                      *)
  (*     val     : val,                                      *)
  (*     deleted : false,                                    *)
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

Definition tuple_appended tuple (tid : u64) (key : u64) (val : u64) γ : iProp Σ :=
  ∃ (tidown tidlast tidgc : u64) (vers : list pver)
    (vchain : list dbval),
    (* physical state is updated, but logical state is not. *)
    let vers' := vers ++ [(tid, false, val)] in
    "Hphys" ∷ own_tuple_phys tuple (U64 0) (U64 (int.Z tid + 1)) vers' ∗
    "Habst" ∷ own_tuple_abst key tidown tidlast tidgc vers vchain γ ∗
    "%Htid" ∷ ⌜int.Z tidgc ≤ int.Z tid⌝.

(*****************************************************************)
(* func (tuple *Tuple) AppendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__AppendVersion tuple (tid : u64) (val : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid }}}
    Tuple__AppendVersion #tuple #tid #val
  {{{ (latch : loc), RET #();
      active_tid γ tid sid ∗
      tuple_locked tuple key latch γ ∗
      tuple_appended tuple tid key val γ
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
  (* tuple.appendVersion(tid, val)                           *)
  (***********************************************************)
  iNamed "Hphys".
  wp_apply (wp_tuple__appendVersion with "[$Htidown $Htidlast Hvers HversS]"); first eauto with iFrame.
  iIntros "Hphys".
  (* iNamed "HtuplePhys". *)
  wp_pures.
  
  (***********************************************************)
  (* tuple.rcond.Broadcast()                                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_condBroadcast with "[$HrcondC]").
  
  wp_pures.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (active_ge_min with "HinvgcO Hactive Hgclb") as "%HtidGe".
  iMod ("HinvgcC" with "HinvgcO") as "_".
  iModIntro.
  iApply "HΦ".
  iFrame "# ∗".
  unfold tuple_appended.
  do 5 iExists _.
  iFrame "Hphys".
  iSplit; last done.
  iFrame "% # ∗".
Qed.

End proof.
