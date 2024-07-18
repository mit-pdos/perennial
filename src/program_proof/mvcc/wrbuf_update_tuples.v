From Perennial.program_proof.mvcc Require Import
     wrbuf_prelude wrbuf_repr
     tuple_repr tuple_append_version tuple_kill_version.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (wrbuf *WrBuf) UpdateTuples(tid uint64)                  *)
(*****************************************************************)
Theorem wp_wrbuf__UpdateTuples wrbuf (tid : u64) sid mods tpls γ :
  {{{ own_wrbuf wrbuf mods tpls ∗
      own_tuples_updated (uint.nat tid) mods tpls γ ∗
      active_tid γ tid sid
  }}}
    WrBuf__UpdateTuples #wrbuf #tid
  {{{ RET #(); own_wrbuf_xtpls wrbuf mods ∗ active_tid γ tid sid }}}.
Proof.
  iIntros (Φ) "(Hwrbuf & Htpls & Hactive) HΦ".
  wp_rec. wp_pures.
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
  wp_loadField.
  wp_pures.
  set P :=
    (λ (i : u64),
       let mods' := (list_to_map (wrent_to_key_dbval <$> (drop (uint.nat i) ents))) in
       let tpls' := (list_to_map (wrent_to_key_tpl <$> (drop (uint.nat i) ents))) in
       own_tuples_updated (uint.nat tid) mods' tpls' γ ∗ active_tid γ tid sid)%I.
  iDestruct (own_slice_small_acc with "HentsS") as "[HentsS HentsC]".
  wp_apply (wp_forSlice P with "[] [$HentsS Htpls $Hactive]").
  { clear Φ.
    iIntros (i x).
    iIntros "!>" (Φ) "(HP & %Hbound & %Hlookup) HΦ".
    subst P. simpl.
    iDestruct "HP" as "[Htpls Hactive]".
    apply wrent_to_val_with_lookup in Hlookup as (k & v & w & t & Eqx & Hlookup).
    subst x.
    wp_pures.
    (* Deduce [k ∉ (drop (S (uint.nat i)) ents).*1.*1.*1]. *)
    apply take_drop_middle in Hlookup as Eqents.
    rewrite -Eqents in HNoDup.
    do 3 rewrite fmap_app in HNoDup.
    do 3 rewrite fmap_cons in HNoDup.
    simpl in HNoDup.
    apply NoDup_app in HNoDup as (_ & _ & HNoDup).
    apply NoDup_cons in HNoDup as [Hnotin _].
    wp_if_destruct.
    { (* Case [AppendVersion]. *)
      replace (uint.nat (word.add _ _)) with (S (uint.nat i)) by word.
      rewrite (drop_S _ _ _ Hlookup).
      do 2 rewrite list_to_map_cons.
      unfold own_tuples_updated. simpl.
      rewrite big_sepM2_insert; last first.
      { apply not_elem_of_list_to_map_1. set_solver. }
      { apply not_elem_of_list_to_map_1. set_solver. }
      iDestruct "Htpls" as "[[%phys Htpl] Htpls]".
      wp_apply (wp_tuple__AppendVersion with "[$Hactive $Htpl]").
      iIntros "Hactive".
      iApply "HΦ".
      iFrame.
    }
    { (* Case [KillVersion]. *)
      replace (uint.nat (word.add _ _)) with (S (uint.nat i)) by word.
      rewrite (drop_S _ _ _ Hlookup).
      do 2 rewrite list_to_map_cons.
      unfold own_tuples_updated. simpl.
      rewrite big_sepM2_insert; last first.
      { apply not_elem_of_list_to_map_1. set_solver. }
      { apply not_elem_of_list_to_map_1. set_solver. }
      iDestruct "Htpls" as "[[%phys Htpl] Htpls]".
      wp_apply (wp_tuple__KillVersion with "[$Hactive $Htpl]").
      iIntros (ret) "Hactive".
      iApply "HΦ".
      iFrame.
    }
  }
  { subst P. simpl.
    replace (uint.nat 0) with 0%nat by word.
    rewrite drop_0.
    by rewrite -Hmods -Htpls.
  }
  iIntros "[[_ Hactive] HentsS]".
  iDestruct ("HentsC" with "HentsS") as "HentsS".
  wp_pures.
  iApply "HΦ".
  by iFrame.
Qed.

End heap.
