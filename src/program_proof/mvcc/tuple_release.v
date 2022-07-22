From Perennial.program_proof.mvcc Require Import tuple_common.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (tuple *Tuple) Release()                                 *)
(*****************************************************************)
Theorem wp_tuple__Release tuple (key : u64) (sid : u64) (latch : loc) γ :
  {{{ tuple_locked tuple key latch γ ∗ own_tuple tuple key γ }}}
    Tuple__Release #tuple
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[Hlocked Hown] HΦ".
  iNamed "Hlocked".
  wp_call.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  { eauto 10 with iFrame. }
  wp_pures.
  by iApply "HΦ".
Qed.

End proof.
