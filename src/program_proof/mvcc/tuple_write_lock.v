From Perennial.program_proof.mvcc Require Import tuple_prelude tuple_repr.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (tuple *Tuple) WriteLock()                               *)
(*****************************************************************)
Theorem wp_tuple__WriteLock tuple (tid : nat) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ mods_token γ key tid }}}
    Tuple__WriteLock #tuple
  {{{ (phys : list dbval), RET #(); own_tuple_locked tuple key tid phys phys γ }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Htoken HΦ".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  iNamed "Htuple".
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  wp_pures.

  iNamed "HtupleOwn".
  iDestruct "Htoken" as (phys) "[Hptuple' %Hlen]".
  destruct owned; last first.
  { (* Obtain contradiction for case [owned = false]. *)
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of _ _ key with "Hkeys") as "Hkey"; first set_solver.
    iRename "Hptuple" into "Hptuple''".
    iNamed "Hkey".
    iDestruct (vchain_combine with "Hptuple Hptuple'") as "[Hptuple _]"; first done.
    iDestruct (vchain_combine with "Hptuple Hptuple''") as "[Hptuple _]"; first done.
    iDestruct (vchain_false with "Hptuple") as "contra"; done.
  }
  
  iDestruct (vchain_combine with "Hptuple Hptuple'") as "[Hptuple <-]"; first done.
  rewrite Qp.quarter_quarter.
  iModIntro.
  iApply "HΦ".
  do 4 iExists _.
  iFrame "Hptuple Hphys Hrepr".
  iSplit; [by eauto 10 with iFrame | done].
Qed.

End proof.
