From Perennial.program_proof.tulip.invariance Require Import validate.
From Perennial.program_proof.tulip.program Require Import prelude replica_repr.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_writable_key replica_readable_key replica_acquire_key.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__acquire rp (tsW : u64) pwrsS pwrsL pwrs ptsm sptsm :
    valid_wrs pwrs ->
    let ts := uint.nat tsW in
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__acquire #rp #tsW (to_val pwrsS)
    {{{ (acquired : bool), RET #acquired;
        own_dbmap_in_slice pwrsS pwrsL pwrs ∗
        if acquired
        then own_replica_ptsm_sptsm rp (acquire ts pwrs ptsm) (acquire ts pwrs sptsm) ∗
             ⌜validated_ptsm ptsm pwrs⌝ ∗
             ⌜validated_sptsm sptsm ts pwrs⌝
        else own_replica_ptsm_sptsm rp ptsm sptsm
    }}}.
  Proof.
    iIntros (Hvw ts Φ) "[[HpwrsS %HpwrsL] Hrp] HΦ".
    wp_rec.
    iDestruct (own_replica_ptsm_sptsm_dom with "Hrp") as %[Hdomptsm Hdomsptsm].

    (*@ func (rp *Replica) acquire(ts uint64, pwrs []tulip.WriteEntry) bool {   @*)
    (*@     // Check if all keys are writable.                                  @*)
    (*@     var pos uint64 = 0                                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_ref_to); first by auto.
    iIntros (posP) "HposP".
    wp_pures.

    (*@     for pos < uint64(len(pwrs)) {                                       @*)
    (*@         ent := pwrs[pos]                                                @*)
    (*@         writable := rp.writableKey(ts, ent.Key)                         @*)
    (*@         if !writable {                                                  @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@         pos++                                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct (own_slice_sz with "HpwrsS") as %Hlen.
    iDestruct (own_slice_small_acc with "HpwrsS") as "[HpwrsS HpwrsC]".
    set P := (λ (cont : bool), ∃ (pos : u64),
      let pwrs' := list_to_map (take (uint.nat pos) pwrsL) in
      "HpwrsS"  ∷ own_slice_small pwrsS (struct.t WriteEntry) (DfracOwn 1) pwrsL ∗
      "HposP"   ∷ posP ↦[uint64T] #pos ∗
      "Hrp"     ∷ own_replica_ptsm_sptsm rp ptsm sptsm ∗
      "%Hptsm"  ∷ ⌜validated_ptsm ptsm pwrs'⌝ ∗
      "%Hsptsm" ∷ ⌜validated_sptsm sptsm ts pwrs'⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [HpwrsS HposP Hrp]"); last first; first 1 last.
    { (* Loop entry. *)
      iExists (W64 0).
      rewrite uint_nat_W64_0 take_0 list_to_map_nil.
      iFrame.
      iPureIntro.
      (* split; first done. *)
      split.
      { rewrite /validated_ptsm dom_empty_L.
        intros k n Hn.
        by apply map_lookup_filter_Some in Hn as [_ ?].
      }
      { rewrite /validated_sptsm dom_empty_L.
        intros k n Hn.
        by apply map_lookup_filter_Some in Hn as [_ ?].
      }
    }
    { (* Loop body. *)
      clear Φ. iIntros (Φ) "!> HP HΦ". iNamed "HP".
      wp_load.
      wp_apply (wp_slice_len).
      wp_if_destruct; last first.
      { (* Exit from the loop condition. *)
        iApply "HΦ".
        iExists pos.
        by iFrame "∗ %".
      }
      wp_load.
      destruct (lookup_lt_is_Some_2 pwrsL (uint.nat pos)) as [[k v] Hwr]; first word.
      wp_apply (wp_SliceGet with "[$HpwrsS]"); first done.
      iIntros "HpwrsL".
      wp_pures.
      wp_apply (wp_Replica__writableKey with "Hrp").
      { rewrite -HpwrsL in Hwr.
        apply elem_of_list_lookup_2, elem_of_map_to_list, elem_of_dom_2 in Hwr.
        clear -Hvw Hwr. set_solver.
      }
      iIntros (ok) "[Hrp %Hwritable]".
      wp_pures.
      destruct ok; wp_pures; last first.
      { iApply "HΦ".
        by iFrame "∗ %".
      }
      wp_load.
      wp_store.
      iApply "HΦ".
      iFrame "∗ %".
      iPureIntro.
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hwr) list_to_map_snoc; last first.
      { by eapply map_to_list_not_elem_of_take_key. }
      split.
      { intros x n Hn.
        apply map_lookup_filter_Some in Hn as [Hn Hx].
        rewrite /= dom_insert_L elem_of_union in Hx.
        destruct Hx as [Hx | Hx]; last first.
        { specialize (Hptsm x n). simpl in Hptsm.
          apply Hptsm.
          by apply map_lookup_filter_Some.
        }
        rewrite elem_of_singleton in Hx. subst x.
        destruct Hwritable as [Hwritable _].
        by rewrite /key_writable_ptsm Hn in Hwritable.
      }
      { intros x n Hn.
        apply map_lookup_filter_Some in Hn as [Hn Hx].
        rewrite /= dom_insert_L elem_of_union in Hx.
        destruct Hx as [Hx | Hx]; last first.
        { specialize (Hsptsm x n). simpl in Hsptsm.
          apply Hsptsm.
          by apply map_lookup_filter_Some.
        }
        rewrite elem_of_singleton in Hx. subst x.
        destruct Hwritable as [_ Hwritable].
        by rewrite /key_writable_sptsm Hn in Hwritable.
      }
    }
    iNamed 1. clear P.

    (*@     // Report error if some key cannot be locked.                       @*)
    (*@     if pos < uint64(len(pwrs)) {                                        @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_load.
    wp_apply wp_slice_len.
    wp_if_destruct.
    { iDestruct ("HpwrsC" with "HpwrsS") as "HpwrsS".
      iApply "HΦ".
      by iFrame "∗ %".
    }
    rewrite take_ge in Hptsm, Hsptsm; last word.
    rewrite -HpwrsL list_to_map_to_list in Hptsm, Hsptsm.

    (*@     // Acquire locks for each key.                                      @*)
    (*@     for _, ent := range(pwrs) {                                         @*)
    (*@         rp.acquireKey(ts, ent.Key)                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    set P := (λ (i : u64),
      let pwrs' := list_to_map (take (uint.nat i) pwrsL) in
      own_replica_ptsm_sptsm rp (acquire ts pwrs' ptsm) (acquire ts pwrs' sptsm))%I.
    wp_apply (wp_forSlice P with "[] [$HpwrsS Hrp]"); last first; first 1 last.
    { (* Loop entry. *)
      subst P. simpl.
      by rewrite uint_nat_W64_0 take_0 list_to_map_nil /acquire 2!setts_empty.
    }
    { (* Loop body. *)
      clear Φ.
      iIntros (i [k v]) "!>".
      iIntros (Φ) "(Hrp & %Hbound & %Hi) HΦ".
      subst P. simpl.
      wp_pures.
      wp_apply (wp_Replica__acquireKey with "Hrp").
      iIntros "Hrp".
      iApply "HΦ".
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hi) list_to_map_snoc; last first.
      { by eapply map_to_list_not_elem_of_take_key. }
      rewrite /acquire setts_insert; last first.
      { rewrite -HpwrsL in Hi.
        apply elem_of_list_lookup_2, elem_of_map_to_list, elem_of_dom_2 in Hi.
        clear -Hvw Hi Hdomptsm. set_solver.
      }
      rewrite /acquire setts_insert; last first.
      { rewrite -HpwrsL in Hi.
        apply elem_of_list_lookup_2, elem_of_map_to_list, elem_of_dom_2 in Hi.
        clear -Hvw Hi Hdomsptsm. set_solver.
      }
      done.
    }
    iIntros "[HP HpwrsS]".
    iNamed "HP". clear P.
    rewrite -Hlen firstn_all -HpwrsL list_to_map_to_list in Hptsmabs, Hsptsmabs.

    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    wp_pures.
    iDestruct ("HpwrsC" with "HpwrsS") as "HpwrsS".
    iApply "HΦ".
    by iFrame "HptsmP HsptsmP ∗ %".
  Qed.

End program.
