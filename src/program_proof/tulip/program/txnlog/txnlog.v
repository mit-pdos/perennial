From Perennial.program_proof.tulip.program Require Import prelude.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition own_pwrs_slice (pwrsS : Slice.t) (c : ccommand) : iProp Σ :=
    match c with
    | CmdCommit _ pwrs => (∃ pwrsL : list dbmod, own_dbmap_in_slice pwrsS pwrsL pwrs)
    | _ => True
    end.

  Definition is_txnlog (txnlog : loc) (gid : u64) (γ : tulip_names) : iProp Σ.
  Admitted.

  #[global]
  Instance is_txnlog_persistent txnlog gid γ :
    Persistent (is_txnlog txnlog gid γ).
  Admitted.

  Theorem wp_TxnLog__Lookup (log : loc) (lsn : u64) (gid : u64) γ :
    is_txnlog log gid γ -∗
    {{{ True }}}
    <<< ∀∀ l, own_txn_log γ gid l >>>
      TxnLog__Lookup #log #lsn @ ↑txnlogN
    <<< ∃∃ l', own_txn_log γ gid l' >>>
    {{{ (c : ccommand) (ok : bool) (pwrsS : Slice.t), RET (ccommand_to_val pwrsS c, #ok);
        own_pwrs_slice pwrsS c ∗
        ⌜if ok then l' !! (uint.nat lsn) = Some c else True⌝
    }}}.
  Proof.
  Admitted.

  Theorem wp_TxnLog__SubmitAbort (log : loc) (ts : u64) (gid : u64) γ :
    is_txnlog log gid γ -∗
    {{{ True }}}
    <<< ∀∀ vs, own_txn_cpool γ gid vs >>>
      TxnLog__SubmitAbort #log #ts @ ↑txnlogN
    <<< own_txn_cpool γ gid ({[CmdAbort (uint.nat ts)]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term);
        is_proposed_txn_cmd γ gid (uint.nat lsn) (uint.nat term) (CmdAbort (uint.nat ts))
    }}}.
  Proof.
  Admitted.

  Theorem wp_TxnLog__SubmitCommit
    (log : loc) (ts : u64) (pwrsS : Slice.t)
    (pwrsL : list dbmod) (pwrs : dbmap) (gid : u64) γ :
    is_txnlog log gid γ -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs }}}
    <<< ∀∀ vs, own_txn_cpool γ gid vs >>>
      TxnLog__SubmitCommit #log #ts (to_val pwrsS) @ ↑txnlogN
    <<< own_txn_cpool γ gid ({[CmdCommit (uint.nat ts) pwrs]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term);
        is_proposed_txn_cmd γ gid (uint.nat lsn) (uint.nat term) (CmdCommit (uint.nat ts) pwrs)
    }}}.
  Proof.
  Admitted.

  Theorem wp_TxnLog__WaitUntilSafe
    (log : loc) (lsn : u64) (term : u64) (c : ccommand) (gid : u64) γ :
    is_txnlog log gid γ -∗
    is_proposed_txn_cmd γ gid (uint.nat lsn) (uint.nat term) c -∗
    {{{ True }}}
      TxnLog__WaitUntilSafe #log #lsn #term
    {{{ (ok : bool), RET #ok;
        if ok
        then ∃ l, is_txn_log_lb γ gid l ∧ ⌜l !! (uint.nat lsn) = Some c⌝
        else True
    }}}.
  Proof.
  Admitted.

End program.
