From Perennial.program_proof.mvcc Require Import tuple_prelude tuple_repr.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.
  
(*****************************************************************)
(* func (tuple *Tuple) Free(tid uint64)                          *)
(*****************************************************************)
Theorem wp_tuple__Free tuple (tid : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ mods_token γ key (uint.nat tid) }}}
    Tuple__Free #tuple
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Htoken HΦ".
  iNamed "Htuple".
  wp_rec. wp_pures.

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
  (* tuple.owned = false                                     *)
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
  iNamed "Hrepr".
  wp_apply (release_spec with "[-HΦ]").
  { iFrame "Hlock Hlocked".
    iNext.
    iExists false.
    do 4 iExists _.
    iSplitL "Howned Htidlast Hvers HversS".
    { eauto with iFrame. }
    iFrame "∗%#".
    iDestruct "Htoken" as (vchain') "[Hptuple' %HvchainLenLt]".
    destruct owned; last iFrame.
    by iDestruct (vchain_combine (1 / 2) with "Hptuple Hptuple'") as "[Hptuple ->]"; first compute_done.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End proof.
