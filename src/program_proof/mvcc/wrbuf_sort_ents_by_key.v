From Perennial.program_proof.mvcc Require Import
     wrbuf_prelude wrbuf_repr
     index_proof
     tuple_repr tuple_own tuple_free tuple_write_lock.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func swap(ents []WrEnt, i, j uint64)                          *)
(*****************************************************************)
Local Lemma wp_swap (entsS : Slice.t) (ents : list wrent) (i j : u64) :
  {{{ slice.own_slice_small entsS (structTy WrEnt) (DfracOwn 1) (wrent_to_val <$> ents) ∗
      ⌜(uint.nat i < length ents ∧ uint.nat j < length ents)%nat⌝
  }}}
    swap (to_val entsS) #i #j
  {{{ (ents' : list wrent), RET #();
      slice.own_slice_small entsS (structTy WrEnt) (DfracOwn 1) (wrent_to_val <$> ents') ∗
      ⌜ents' ≡ₚ ents⌝
  }}}.
Proof.
  iIntros (Φ) "[HentsS %Hbounds] HΦ".
  destruct Hbounds as [Hi Hj].
  apply list_lookup_lt in Hi as Hx.
  destruct Hx as [x Hx].
  apply list_lookup_lt in Hj as Hy.
  destruct Hy as [y Hy].
  iDestruct (own_slice_small_sz with "HentsS") as "%HentsLen".
  rewrite fmap_length in HentsLen.
  wp_call.
  
  (***********************************************************)
  (* tmp := ents[i]                                          *)
  (* ents[i] = ents[j]                                       *)
  (* ents[j] = tmp                                           *)
  (***********************************************************)
  wp_apply (wp_SliceGet with "[$HentsS]").
  { iPureIntro. by rewrite list_lookup_fmap Hx. }
  iIntros "[HentsS %Htyx]".
  wp_apply (wp_SliceGet with "[$HentsS]").
  { iPureIntro. by rewrite list_lookup_fmap Hy. }
  iIntros "[HentsS %Htyy]".
  wp_apply (wp_SliceSet with "[$HentsS]").
  { iPureIntro. split; last done. by rewrite list_lookup_fmap fmap_is_Some. }
  iIntros "HentsS".
  wp_apply (wp_SliceSet with "[$HentsS]").
  { iPureIntro. split; last done.
    rewrite -list_fmap_insert list_lookup_fmap fmap_is_Some.
    apply lookup_lt_is_Some_2.
    rewrite insert_length.
    word.
  }
  iIntros "HentsS".
  wp_pures.
  iApply "HΦ".
  iFrame.
  do 2 rewrite -list_fmap_insert.
  iFrame.
  iPureIntro.
  apply list_insert_insert_swap; done.
Qed.

(*********************************************************************)
(* func (wrbuf *WrBuf) sortEntsByKey()                               *)
(*********************************************************************)
Theorem wp_wrbuf__sortEntsByKey wrbuf mods :
  {{{ own_wrbuf_xtpls wrbuf mods }}}
    WrBuf__sortEntsByKey #wrbuf
  {{{ RET #(); own_wrbuf_xtpls wrbuf mods }}}.
Proof.
  iIntros (Φ) "Hwrbuf HΦ".
  wp_call.
  
  (***********************************************************)
  (* ents := wrbuf.ents                                      *)
  (* var i uint64 = 1                                        *)
  (***********************************************************)
  iNamed "Hwrbuf".
  wp_loadField.
  wp_pures.
  wp_apply (wp_ref_to); first by auto.
  iIntros (iRef) "HiRef".
  wp_pures.
  iDestruct (own_slice_small_acc with "HentsS") as "[HentsS HentsC]".
  iDestruct (own_slice_small_sz with "HentsS") as "%HentsLen".
  rewrite fmap_length in HentsLen.

  (***********************************************************)
  (* for i < uint64(len(ents)) {                             *)
  (*     var j uint64 = i                                    *)
  (*     for j > 0 {                                         *)
  (*         if ents[j - 1].key <= ents[j].key {             *)
  (*             break                                       *)
  (*         }                                               *)
  (*         swap(ents, j - 1, j)                            *)
  (*         j--                                             *)
  (*     }                                                   *)
  (*     i++                                                 *)
  (* }                                                       *)
  (***********************************************************)
  set P := (λ (b : bool), ∃ (ents' : list wrent) (i : u64),
               "HentsS" ∷ own_slice_small entsS (struct.t WrEnt) (DfracOwn 1) (wrent_to_val <$> ents') ∗
               "HiRef"  ∷ iRef ↦[uint64T] #i ∗
               "%Hperm" ∷ ⌜ents' ≡ₚ ents⌝
           )%I.
  wp_apply (wp_forBreak_cond P with "[] [HentsS HiRef]").
  { (* Outer loop body. *)
    clear Φ.
    iIntros (Φ) "!> HP HΦ".
    iNamed "HP".
    wp_load.
    wp_apply (wp_slice_len).
    wp_if_destruct; last first.
    { (* Outer loop condition. *)
      iApply "HΦ".
      subst P. simpl.
      eauto 10 with iFrame.
    }
    wp_load.
    wp_apply (wp_ref_to); first by auto.
    iIntros (jRef) "HjRef".
    wp_pures.

    (* Inner loop. *)
    set Q := (λ (b : bool), ∃ (ents'' : list wrent) (j : u64),
                "HentsS" ∷ own_slice_small entsS (struct.t WrEnt) (DfracOwn 1) (wrent_to_val <$> ents'') ∗
                "HjRef"  ∷ jRef ↦[uint64T] #j ∗
                "%Hperm" ∷ ⌜ents'' ≡ₚ ents'⌝ ∗
                "%Hle" ∷ ⌜uint.Z j ≤ uint.Z i⌝
            )%I.
    wp_apply (wp_forBreak_cond Q with "[] [HentsS HjRef]").
    { (* Inner loop body. *)
      clear Φ.
      iIntros (Φ) "!> HQ HΦ".
      iNamed "HQ".
      wp_load.
      wp_if_destruct; last first.
      { (* Inner loop condition. *)
        iApply "HΦ".
        subst Q. simpl.
        eauto 10 with iFrame.
      }
      wp_pures.

      assert (Hboundj : (uint.nat j < length ents'')%nat).
      { apply Permutation_length in Hperm, Hperm0. word. }

      (* Read key of entry at [j - 1]. *)
      wp_load.
      destruct (list_lookup_lt _ (wrent_to_val <$> ents'') (uint.nat (word.sub j (W64 1)))) as [entx Hlookupx].
      { rewrite fmap_length. word. }
      wp_apply (wp_SliceGet with "[$HentsS]"); first done.
      iIntros "[HentsS %Hty]".
      wp_pures.
      apply val_to_wrent_with_val_ty in Hty as (kx & vx & wx & tx & Hentx).
      subst entx.
      wp_pures.

      (* Read key of entry at [j]. *)
      wp_load.
      destruct (list_lookup_lt _ (wrent_to_val <$> ents'') (uint.nat j)) as [enty Hlookupy].
      { rewrite fmap_length. word. }
      wp_apply (wp_SliceGet with "[$HentsS]"); first done.
      iIntros "[HentsS %Hty]".
      wp_pures.
      apply val_to_wrent_with_val_ty in Hty as (ky & vy & wy & ty & Henty).
      subst enty.
      wp_pures.

      wp_if_destruct.
      { (* Early return of inner loop. *)
        iApply "HΦ". subst Q. simpl.
        eauto with iFrame.
      }
      (* Swap entries at [j - 1] and at [j]. *)
      do 2 wp_load.
      wp_apply (wp_swap with "[$HentsS]").
      { iPureIntro. word. }
        
      iIntros (ents1) "[HentsS %Hperm1]".
      wp_load.
      wp_store.
      iApply "HΦ".
      subst Q. simpl.
      do 2 iExists _.
      iFrame.
      iPureIntro.
      split; last by word.
      by rewrite -Hperm0.
    }
    { (* Inner loop entry. *)
      subst Q. simpl.
      eauto with iFrame.
    }
    
    (* Increment [i]. *)
    iIntros "HQ".
    subst Q. simpl.
    iNamed "HQ".
    wp_load.
    wp_store.
    iApply "HΦ".
    subst P. simpl.
    do 2 iExists _. iFrame.
    iPureIntro.
    by rewrite <- Hperm.
  }
  { (* Outer loop entry. *)
    subst P. simpl.
    eauto with iFrame.
  }

  (* RETURN. *)
  iIntros "HP".
  subst P. simpl.
  iNamed "HP".
  iDestruct ("HentsC" with "HentsS") as "HentsS".
  wp_pures.
  iApply "HΦ".
  do 2 iExists _.
  iFrame.
  iPureIntro.
  split.
  { (* Prove [NoDup]. *)
    by rewrite Hperm.
  }
  { (* Prove [list_to_map]. *)
    rewrite Hmods.
    apply list_to_map_proper; last by rewrite Hperm.
    by apply NoDup_wrent_to_key_dbval.
  }
Qed.

End heap.
