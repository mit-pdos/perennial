From Perennial.program_proof.mvcc Require Import
     wrbuf_prelude wrbuf_repr
     index_proof
     tuple_repr tuple_own tuple_free tuple_write_lock.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*********************************************************************)
(* func (wrbuf *WrBuf) OpenTuples(tid uint64, idx *index.Index) bool *)
(*********************************************************************)
Theorem wp_wrbuf__OpenTuples wrbuf (tid : u64) (idx : loc) m γ :
  {{{ own_wrbuf_xtpls wrbuf m }}}
    WrBuf__OpenTuples #wrbuf #tid #idx
  {{{ (ok : bool) (tpls : gmap u64 loc), RET #ok;
      own_wrbuf wrbuf m tpls ∗ own_tuples_locked (int.nat tid) tpls γ
  }}}.
Proof.
  iIntros (Φ) "Hwrbuf HΦ".
  wp_call.
  iNamed "Hwrbuf".
  
  (***********************************************************)
  (* ents := wrbuf.ents                                      *)
  (* var pos uint64 = 0                                      *)
  (* for pos < uint64(len(ents)) {                           *)
  (*     ent := ents[pos]                                    *)
  (*     tpl := idx.GetTuple(ent.key)                        *)
  (*     ents[pos] = WrEnt {                                 *)
  (*         key : ent.key,                                  *)
  (*         val : ent.val,                                  *)
  (*         wr  : ent.wr,                                   *)
  (*         tpl : tpl,                                      *)
  (*     }                                                   *)
  (*     ret := tpl.Own(tid)                                 *)
  (*     if ret != common.RET_SUCCESS {                      *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     pos++                                               *)
  (* }                                                       *)
  (***********************************************************)

  (**
   * Get [mods_token] and [is_tuple] for each element in [ents].
   *)

  (***********************************************************)
  (* if pos < uint64(len(ents)) {                            *)
  (*     var i uint64 = 0                                    *)
  (*     for i < pos {                                       *)
  (*         tpl := ents[i].tpl                              *)
  (*         tpl.Free()                                      *)
  (*         i++                                             *)
  (*     }                                                   *)
  (*     return false                                        *)
  (* }                                                       *)
  (***********************************************************)

  (***********************************************************)
  (* for _, ent := range ents {                              *)
  (*     ent.tpl.WriteLock()                                 *)
  (* }                                                       *)
  (* return true                                             *)
  (***********************************************************)

  (**
   * Get [own_tuple_locked] for each element in [ents].
   * Give [Hptuple] (proof of [ptuple_auth]) and [Hlen] to txn, and keep the remaining.
   * Should convert [ptuple_auth]s from [big_sepL] into [big_sepM].
   *)
Admitted.

End heap.
