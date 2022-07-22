From Perennial.program_proof.mvcc Require Import tuple_common.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.
  
(*****************************************************************)
(* func (tuple *Tuple) Free(tid uint64)                          *)
(*****************************************************************)
Theorem wp_tuple__Free tuple (tid : u64) (key : u64) (vers : list (u64 * u64 * u64)) γ :
  is_tuple tuple key γ -∗
  {{{ mods_token γ key tid }}}
    Tuple__Free #tuple #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Htoken HΦ".
  rename vers into vers'.
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
  (* tuple.tidown = 0                                        *)
  (***********************************************************)
  wp_storeField.

  (***********************************************************)
  (* tuple.rcond.Broadcast()                                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_condBroadcast with "[$HrcondC]").
  wp_pures.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  iNamed "Habst".
  wp_apply (release_spec with "[-HΦ]").
  { iFrame "Hlock Hlocked".
    iNext.
    iExists (U64 0).
    do 4 iExists _.
    iSplitL "Htidown Htidlast Hvers HversS".
    { eauto with iFrame. }
    iFrame "% # ∗".
    iDestruct "Htoken" as (vchain') "[Hvchain' %HvchainLenLt]".
    case_decide; first iFrame.
    by iDestruct (vchain_combine (1 / 2) with "Hvchain Hvchain'") as "[Hvchain ->]"; first compute_done.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End proof.
