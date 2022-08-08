From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_txn__apply txn tid view γ τ :
  {{{ own_txn_appliable txn tid view γ τ }}}
    Txn__apply #txn
  {{{ RET #(); own_txn txn tid view γ τ }}}.
Proof.
  (***********************************************************)
  (* ents := txn.wrbuf.IntoEnts()                            *)
  (* for _, ent := range ents {                              *)
  (*     key, val, del := ent.Destruct()                     *)
  (*     idx := txn.idx                                      *)
  (*     tuple := idx.GetTuple(key)                          *)
  (*     if del {                                            *)
  (*         tuple.KillVersion(txn.tid)                      *)
  (*     } else {                                            *)
  (*         tuple.AppendVersion(txn.tid, val)               *)
  (*     }                                                   *)
  (* }                                                       *)
  (***********************************************************)
Admitted.

End program.
