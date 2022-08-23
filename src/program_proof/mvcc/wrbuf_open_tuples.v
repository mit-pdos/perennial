From Perennial.program_proof.mvcc Require Import
     wrbuf_prelude wrbuf_repr
     index_proof
     tuple_repr tuple_own tuple_free tuple_write_lock.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*********************************************************************)
(* func (wrbuf *WrBuf) OpenTuples(tid uint64, idx *index.Index) bool *)
(*********************************************************************)
Theorem wp_wrbuf__OpenTuples wrbuf (tid : u64) (idx : loc) sid m γ :
  is_index idx γ -∗
  {{{ own_wrbuf_xtpls wrbuf m ∗ active_tid γ tid sid }}}
    WrBuf__OpenTuples #wrbuf #tid #idx
  {{{ (ok : bool), RET #ok;
      active_tid γ tid sid ∗
      if ok
      then ∃ (tpls : gmap u64 loc), own_wrbuf wrbuf m tpls ∗ own_tuples_locked (int.nat tid) tpls γ
      else own_wrbuf_xtpls wrbuf m
  }}}.
Proof.
  iIntros "Hidx !>" (Φ) "[Hwrbuf Hactive] HΦ".
  wp_call.
  
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
  iNamed "Hwrbuf".
  wp_loadField.
  wp_pures.
  wp_apply (wp_ref_to); first by auto.
  iIntros (pos) "HposR".
  wp_pures.
  set P := (λ (b : bool), ∃ (i : u64) (tpls : gmap u64 loc),
              "Hactive"  ∷ active_tid γ tid sid ∗
              "HentsS"   ∷ is_slice entsS (struct.t WrEnt) 1 (wrent_to_val <$> ents) ∗
              "HposR"    ∷ pos ↦[uint64T] #i ∗
              "%Htpls"   ∷ ⌜tpls = list_to_map (wrent_to_key_tpl <$> (take (int.nat i) ents))⌝ ∗
              "Htokens"  ∷ ([∗ map] k ↦ _ ∈ tpls, mods_token γ k (int.nat tid)) ∗
              "#HtplsRP" ∷ ([∗ map] k ↦ t ∈ tpls, is_tuple t k γ)
           )%I.
  wp_apply (wp_forBreak_cond P with "[] [Hactive HentsS HposR]").
  { (* Loop body. *)
    clear Φ.
    iIntros (Φ) "!> HP HΦ".
    iNamed "HP".
    wp_load.
    wp_apply (wp_slice_len).
    admit.
  }
  { (* Loop entry. *)
    subst P. simpl.
    iExists _, ∅.
    iFrame.
    replace (int.nat 0) with 0%nat by word.
    rewrite take_0. simpl.
    by do 2 rewrite big_sepM_empty.
  }
  iIntros "HP". subst P. simpl.
  iNamed "HP".
  replace (take (int.nat i) ents) with ents in Htpls; last first.
  { admit. }

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
  wp_pures.
  wp_load.
  wp_apply wp_slice_len.
  wp_if_destruct.
  { (* Early return due to failure of acquiring all locks. *)
    admit.
  }

  (***********************************************************)
  (* for _, ent := range ents {                              *)
  (*     ent.tpl.WriteLock()                                 *)
  (* }                                                       *)
  (* return true                                             *)
  (***********************************************************)
  iDestruct (is_slice_small_acc with "HentsS") as "[HentsS HentsC]".
  set P := (λ (i : u64),
              let tpls_take := (list_to_map (wrent_to_key_tpl <$> (take (int.nat i) ents))) in
              let tpls_drop := (list_to_map (wrent_to_key_tpl <$> (drop (int.nat i) ents))) in
              "Htokens"  ∷ ([∗ map] k ↦ _ ∈ tpls_drop, mods_token γ k (int.nat tid)) ∗
              "HtplsOwn" ∷ own_tuples_locked (int.nat tid) tpls_take γ
           )%I.
  wp_apply (wp_forSlice P with "[] [$HentsS]").
  { (* Loop body. *)
    clear Φ.
    iIntros (j e).
    iIntros (Φ) "!> (HP & %Hbound & %Hlookup) HΦ".
    subst P. simpl.
    iNamed "HP".
    apply wrent_to_val_with_lookup in Hlookup as (k & v & w & t & Eqx & Hlookup).
    subst e.
    wp_pures.
    (* Retrieve [is_tuple] of key [k]. *)
    iDestruct (big_sepM_lookup _ _ k t with "HtplsRP") as "HtplRP".
    { rewrite Htpls.
      rewrite -elem_of_list_to_map; last admit. (* NoDup *)
      apply elem_of_list_lookup_2, (elem_of_list_fmap_1 wrent_to_key_tpl) in Hlookup.
      done.
    }
    (* Retrieve [mods_token] of key [k]. *)
    rewrite (drop_S _ _ _ Hlookup).
    rewrite fmap_cons.

    wp_apply (wp_tuple__WriteLock with "HtplRP").
    { admit. }
    admit.
  }
  { (* Loop entry. *)
    admit.
  }
  admit.
Admitted.

End heap.
