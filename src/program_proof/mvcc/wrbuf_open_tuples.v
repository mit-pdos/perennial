From Perennial.program_proof.mvcc Require Import
     wrbuf_prelude wrbuf_repr wrbuf_sort_ents_by_key
     index_proof
     tuple_repr tuple_own tuple_free tuple_write_lock.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*********************************************************************)
(* func (wrbuf *WrBuf) OpenTuples(tid uint64, idx *index.Index) bool *)
(*********************************************************************)
Theorem wp_wrbuf__OpenTuples wrbuf (tid : u64) (idx : loc) sid mods γ :
  is_index idx γ -∗
  {{{ own_wrbuf_xtpls wrbuf mods ∗ active_tid γ tid sid }}}
    WrBuf__OpenTuples #wrbuf #tid #idx
  {{{ (ok : bool), RET #ok;
      active_tid γ tid sid ∗
      if ok
      then ∃ (tpls : gmap u64 loc), own_wrbuf wrbuf mods tpls ∗ own_tuples_locked (uint.nat tid) tpls γ
      else own_wrbuf_xtpls wrbuf mods
  }}}.
Proof.
  iIntros "#Hidx !>" (Φ) "[Hwrbuf Hactive] HΦ".
  wp_call.
  
  (***********************************************************)
  (* wrbuf.sortEntsByKey()                                   *)
  (***********************************************************)
  wp_apply (wp_wrbuf__sortEntsByKey with "Hwrbuf").
  iIntros "Hwrbuf".
  wp_pures.
  
  (***********************************************************)
  (* ents := wrbuf.ents                                      *)
  (* var pos uint64 = 0                                      *)
  (* for pos < uint64(len(ents)) {                           *)
  (*     ent := ents[pos]                                    *)
  (*     tpl := idx.GetTuple(ent.key)                        *)
  (*     ret := tpl.Own(tid)                                 *)
  (*     if ret != common.RET_SUCCESS {                      *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     ents[pos] = WrEnt {                                 *)
  (*         key : ent.key,                                  *)
  (*         val : ent.val,                                  *)
  (*         wr  : ent.wr,                                   *)
  (*         tpl : tpl,                                      *)
  (*     }                                                   *)
  (*     pos++                                               *)
  (* }                                                       *)
  (***********************************************************)
  iNamed "Hwrbuf".
  (* Obtain [own_slice_small] and eq about length of [ents]. *)
  iDestruct (own_slice_sz with "HentsS") as "%HentsLen".
  rewrite fmap_length in HentsLen.
  iDestruct (own_slice_small_acc with "HentsS") as "[HentsS HentsC]".
  wp_loadField.
  wp_pures.
  wp_apply (wp_ref_to); first by auto.
  iIntros (pos) "HposR".
  wp_pures.
  set P := (λ (b : bool), ∃ (n : u64) (tpls : gmap u64 loc) (ents' : list wrent),
               let m : dbmap := list_to_map (wrent_to_key_dbval <$> ents) in
               "Hactive"  ∷ active_tid γ tid sid ∗
               "HentsS"   ∷ own_slice_small entsS (struct.t WrEnt) (DfracOwn 1) (wrent_to_val <$> ents') ∗
               "HposR"    ∷ pos ↦[uint64T] #n ∗
               "Htokens"  ∷ ([∗ map] k ↦ _ ∈ tpls, mods_token γ k (uint.nat tid)) ∗
               "#HtplsRP" ∷ ([∗ map] k ↦ t ∈ tpls, is_tuple t k γ) ∗
               "%Htpls"   ∷ ⌜tpls = list_to_map (wrent_to_key_tpl <$> (take (uint.nat n) ents'))⌝ ∗
               "%Hm"      ∷ ⌜m = list_to_map (wrent_to_key_dbval <$> ents')⌝ ∗
               "%Hlen"    ∷ ⌜length ents = length ents'⌝ ∗
               "%HNoDup"  ∷ ⌜NoDup ents'.*1.*1.*1⌝
           )%I.
  wp_apply (wp_forBreak_cond P with "[] [Hactive HentsS HposR]").
  { (* Loop body. *)
    clear Φ HNoDup.
    iIntros (Φ) "!> HP HΦ".
    iNamed "HP".
    wp_load.
    wp_apply (wp_slice_len).
    wp_if_destruct; last first.
    { (* Loop condition. *)
      iApply "HΦ".
      subst P. simpl.
      eauto 10 with iFrame.
    }
    wp_load.
    destruct (list_lookup_lt _ (wrent_to_val <$> ents') (uint.nat n)) as [ent Hlookup].
    { rewrite fmap_length. word. }
    wp_apply (wp_SliceGet with "[$HentsS]"); first done.
    iIntros "[HentsS %Hty]".
    wp_pures.
    apply val_to_wrent_with_val_ty in Hty as (k & v & w & t & Hent).
    subst ent.
    wp_pures.
    wp_apply (wp_index__GetTuple with "Hidx").
    iIntros (tpl) "#Htpl".
    wp_pures.
    wp_apply (wp_tuple__Own with "Htpl Hactive").
    iIntros (ret) "[Hactive HpostOwn]".
    wp_pures.
    unfold post_tuple__Own.
    wp_if_destruct.
    { (* Early return due to failed [tuple__Own]. *)
      iApply "HΦ".
      subst P. simpl.
      eauto 10 with iFrame.
    }
    wp_load.
    wp_apply (wp_SliceSet with "[$HentsS]"); first by auto 10.
    iIntros "HentsS".
    wp_load.
    wp_store.
    iApply "HΦ".
    subst P. simpl.
    replace (uint.Z 0) with 0 by word.
    set tpls := list_to_map (wrent_to_key_tpl <$> _).
    iExists _, (<[k := tpl]> tpls), _.
    rewrite wrent_to_val_unfold -list_fmap_insert.
    iFrame "HentsS Hactive HposR".
    replace (uint.nat (word.add _ _)) with (S (uint.nat n)) by word.
    rewrite take_S_insert; last word.
    (* Deduce [k ∉ (take (uint.nat i) ents).*1.*1.*1]. *)
    apply wrent_to_val_with_lookup in Hlookup as (k' & v' & w' & t' & Eqx & Hlookup).
    inversion Eqx. subst k' v' w' t'.
    apply take_drop_middle in Hlookup as Eqents.
    rewrite -Eqents in HNoDup.
    do 3 rewrite fmap_app in HNoDup.
    do 3 rewrite fmap_cons in HNoDup.
    simpl in HNoDup.
    (* Before we swap using [NoDup_app_comm], obtain [Hnotin'] which we'll need for proving [HNoDup]. *)
    apply NoDup_app in HNoDup as H.
    destruct H as (_ & Hnotin' & _).
    apply NoDup_app_comm in HNoDup.
    apply NoDup_app in HNoDup as (HNoDup1 & Hnotin & HNoDup2).
    pose proof (elem_of_list_here k (drop (S (uint.nat n)) ents').*1.*1.*1) as Helem.
    specialize (Hnotin k Helem).
    assert (HNone : tpls !! k = None).
    { apply not_elem_of_list_to_map_1. clear -Hnotin. set_solver. }
    rewrite big_sepM_insert; last done.
    iFrame "Htokens HpostOwn".
    iSplitL.
    { rewrite big_sepM_insert; last done. by iFrame "#". }
    iPureIntro.
    split.
    { rewrite fmap_snoc.
      unfold wrent_to_key_tpl. simpl. symmetry.
      apply list_to_map_snoc.
      clear -Hnotin. set_solver.
    }
    split.
    { rewrite Hm. f_equal.
      rewrite list_fmap_insert.
      unfold wrent_to_key_dbval. simpl.
      rewrite list_insert_id; first done.
      rewrite list_lookup_fmap Hlookup.
      done.
    }
    split.
    { rewrite Hlen. by rewrite insert_length. }
    { rewrite -Eqents.
      rewrite -insert_take_drop; last first.
      { rewrite -Hlen. word. }
      rewrite list_insert_insert.
      rewrite insert_take_drop; last first.
      { rewrite -Hlen. word. }
      do 3 rewrite fmap_app.
      do 3 rewrite fmap_cons.
      rewrite NoDup_app.
      split; done.
    }
  }
  { (* Loop entry. *)
    subst P. simpl.
    iExists _, ∅, _.
    iFrame.
    replace (uint.nat 0) with 0%nat by word.
    rewrite take_0. simpl.
    by do 2 rewrite big_sepM_empty.
  }
  iIntros "HP". subst P. simpl.
  clear HNoDup.
  iNamed "HP".
  (**
   * Here we have [mods_token] and [is_tuple] for each element in [ents].
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
    wp_apply (wp_ref_to); first by auto.
    iIntros (i) "HiR".
    wp_pures.
    set P := (λ (b : bool), ∃ (m : u64),
                 let tpls' := list_to_map (wrent_to_key_tpl <$> drop (uint.nat m) (take (uint.nat n) ents')) in
                 "HentsS"   ∷ own_slice_small entsS (struct.t WrEnt) (DfracOwn 1) (wrent_to_val <$> ents') ∗
                 "HposR"    ∷ pos ↦[uint64T] #n ∗
                 "HiR"      ∷ i ↦[uint64T] #m ∗
                 "Htokens"  ∷ ([∗ map] k ↦ _ ∈ tpls', mods_token γ k (uint.nat tid)))%I.
    wp_apply (wp_forBreak_cond P with "[] [HentsS HposR HiR Htokens]").
    { (* Loop body. *)
      clear Φ.
      iIntros (Φ) "!> HP HΦ".
      subst P. simpl.
      iNamed "HP".
      do 2 wp_load.
      wp_if_destruct; last first.
      { (* Loop condition. *)
        iApply "HΦ".
        eauto 10 with iFrame.
      }
      wp_load.
      destruct (list_lookup_lt _ (wrent_to_val <$> ents') (uint.nat m)) as [ent Hlookup].
      { rewrite fmap_length. word. }
      wp_apply (wp_SliceGet with "[$HentsS]"); first done.
      iIntros "[HentsS %Hty]".
      apply val_to_wrent_with_val_ty in Hty as (k & v & w & t & Hent).
      subst ent.
      wp_pures.
      (* Obtain [is_tuple] and [mods_token] for [t]. *)
      set ents'' := (take _ ents').
      apply wrent_to_val_with_lookup in Hlookup as (k' & v' & w' & t' & Eqx & Hlookup).
      inversion Eqx. subst k' v' w' t'.
      iDestruct (big_sepM_lookup _ _ k t with "HtplsRP") as "#HtplRP".
      { rewrite Htpls.
        rewrite -elem_of_list_to_map; last first.
        { pose proof HNoDup as HNoDup'.
          rewrite -(take_drop (uint.nat m) ents') in HNoDup.
          do 3 rewrite fmap_app in HNoDup.
          apply NoDup_app in HNoDup as [HNoDup _].
          replace _.*1 with ents''.*1.*1.*1; last first.
          { do 3 rewrite -list_fmap_compose. set_solver. }
          rewrite -(take_drop (uint.nat n) ents') in HNoDup'.
          do 3 rewrite fmap_app in HNoDup'.
          by apply NoDup_app in HNoDup' as [HNoDup' _].
        }
        apply (elem_of_list_lookup_2 _ (uint.nat m)).
        rewrite fmap_take.
        rewrite lookup_take; last word.
        by rewrite list_lookup_fmap Hlookup.
      }
      rewrite (drop_S _ (k, v, w, t)); last first.
      { subst ents''. rewrite lookup_take; [done | word]. }
      rewrite fmap_cons list_to_map_cons. simpl.
      rewrite big_sepM_insert; last first.
      { apply not_elem_of_list_to_map_1.
        apply take_drop_middle in Hlookup.
        rewrite -Hlookup in HNoDup.
        do 3 rewrite fmap_app in HNoDup.
        apply NoDup_app in HNoDup as (_ & _ & HNoDup).
        apply NoDup_cons in HNoDup as [Hnotin _]. simpl in Hnotin.
        rewrite -(take_drop (uint.nat n) ents') in Hnotin.
        rewrite drop_app_le in Hnotin; last first.
        { rewrite take_length_le; first word. rewrite -Hlen. word. }
        clear -Hnotin. set_solver.
      }
      iDestruct "Htokens" as "[Htoken Htokens]".
      wp_apply (wp_tuple__Free with "HtplRP Htoken").
      wp_pures.
      wp_load.
      wp_store.
      iApply "HΦ".
      iExists _.
      iFrame.
      replace (uint.nat (word.add _ _)) with (S (uint.nat m)) by word.
      by iFrame.
    }
    { subst P. simpl.
      iExists _. iFrame.
      replace (uint.nat 0) with 0%nat by word.
      rewrite drop_0. by subst tpls.
    }
    iIntros "HP".
    iNamed "HP".
    wp_pures.
    iApply "HΦ".
    iDestruct ("HentsC" with "HentsS") as "HentsS".
    rewrite Hm in Hmods.
    eauto 10 with iFrame.
  }

  (***********************************************************)
  (* for _, ent := range ents {                              *)
  (*     ent.tpl.WriteOpen()                                 *)
  (* }                                                       *)
  (***********************************************************)
  replace (take (uint.nat n) ents') with ents' in Htpls; last first.
  { apply Znot_lt_ge in Heqb. symmetry. apply take_ge. word. }
  set P := (λ (i : u64),
              let tpls_take := (list_to_map (wrent_to_key_tpl <$> (take (uint.nat i) ents'))) in
              let tpls_drop := (list_to_map (wrent_to_key_tpl <$> (drop (uint.nat i) ents'))) in
              "Htokens"  ∷ ([∗ map] k ↦ _ ∈ tpls_drop, mods_token γ k (uint.nat tid)) ∗
              "HtplsOwn" ∷ own_tuples_locked (uint.nat tid) tpls_take γ
           )%I.
  wp_apply (wp_forSlice P with "[] [$HentsS Htokens]").
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
      rewrite -elem_of_list_to_map; last first.
      { replace _.*1 with ents'.*1.*1.*1; first done.
        do 3 rewrite -list_fmap_compose. set_solver.
      }
      apply elem_of_list_lookup_2, (elem_of_list_fmap_1 wrent_to_key_tpl) in Hlookup.
      done.
    }
    (**
     * Deduce [k ∉ (drop (S (uint.nat i)) ents').*1.*1.*1], which we need in [big_sepM_insert].
     * Deduce [k ∉ (take (uint.nat i) ents').*1.*1.*1], which we need in [list_to_map_snoc] and [big_sepM_insert].
     *)
    apply take_drop_middle in Hlookup as Eqents.
    rewrite -Eqents in HNoDup.
    do 3 rewrite fmap_app in HNoDup.
    do 3 rewrite fmap_cons in HNoDup.
    simpl in HNoDup.
    apply NoDup_app_comm in HNoDup as HNoDup'.
    apply NoDup_app in HNoDup as (_ & _ & HNoDup).
    apply NoDup_cons in HNoDup as [Hnotin _].
    apply NoDup_app in HNoDup' as (_ & Hnotin' & _).
    specialize (Hnotin' k).
    pose proof (elem_of_list_here k (drop (S (uint.nat j)) ents').*1.*1.*1) as Helem.
    specialize (Hnotin' Helem).
    (* Q: How to rewrite [P -> Q] to [Q] and prove [P]. *)
    (* specialize (Hnotin' elem_of_list_here). doesn't work. *)
    (* Retrieve [mods_token] of key [k]. *)
    rewrite (drop_S _ _ _ Hlookup).
    rewrite fmap_cons list_to_map_cons. simpl.
    rewrite big_sepM_insert; last first.
    { apply not_elem_of_list_to_map_1. set_solver. }
    iDestruct "Htokens" as "[Htoken Htokens]".

    wp_apply (wp_tuple__WriteOpen with "HtplRP Htoken").
    iIntros (phys) "Htpl".
    iApply "HΦ".
    replace (uint.nat (word.add _ _)) with (S (uint.nat j)) by word.
    iFrame "Htokens".
    rewrite (take_S_r _ _ _ Hlookup).
    rewrite fmap_snoc list_to_map_snoc; last first.
    { simpl. rewrite -list_fmap_compose. set_solver. }
    unfold named. rewrite {2} /own_tuples_locked.
    rewrite big_sepM_insert; last first.
    { apply not_elem_of_list_to_map_1. set_solver. }
    iFrame "HtplsOwn".
    by iExists phys.
  }
  { (* Loop entry. *)
    subst P. simpl.
    replace (uint.nat 0) with 0%nat by word.
    rewrite drop_0 take_0 -Htpls. simpl.
    iFrame "Htokens".
    by iApply big_sepM_empty.
  }
  iIntros "[HP HentsS]".
  subst P. simpl.
  iNamed "HP".
  iDestruct ("HentsC" with "HentsS") as "HentsS".
  wp_pures.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iApply "HΦ".
  iFrame "Hactive".
  iExists _.
  rewrite -HentsLen Hlen firstn_all.
  iFrame "HtplsOwn".
  rewrite Hm in Hmods.
  eauto 10 with iFrame.
Qed.

End heap.
