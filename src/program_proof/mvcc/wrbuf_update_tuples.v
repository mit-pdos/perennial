From Perennial.program_proof.mvcc Require Import
     wrbuf_prelude wrbuf_repr
     tuple_repr tuple_append_version tuple_kill_version.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (wrbuf *WrBuf) UpdateTuples(tid uint64)                  *)
(*****************************************************************)
Theorem wp_wrbuf__UpdateTuples wrbuf (tid : u64) mods tpls γ :
  {{{ own_wrbuf wrbuf mods tpls ∗ own_tuples_updated (int.nat tid) mods tpls γ }}}
    WrBuf__UpdateTuples #wrbuf #tid
  {{{ RET #(); own_wrbuf_xtpls wrbuf mods }}}.
Proof.
  iIntros (Φ) "Hwrbuf HΦ".
  wp_call.
  iNamed "Hwrbuf".

  (***********************************************************)
  (* ents := wrbuf.ents                                      *)
  (* for _, ent := range ents {                              *)
  (*     tpl := ent.tpl                                      *)
  (*     if ent.wr {                                         *)
  (*         tpl.AppendVersion(tid, ent.val)                 *)
  (*     } else {                                            *)
  (*         tpl.KillVersion(tid)                            *)
  (*     }                                                   *)
  (* }                                                       *)
  (***********************************************************)
Admitted.

End heap.
