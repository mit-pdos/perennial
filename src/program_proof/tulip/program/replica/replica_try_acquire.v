From Perennial.program_proof.tulip.invariance Require Import validate.
From Perennial.program_proof.tulip.program Require Import prelude replica_repr.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_acquire replica_writable_key replica_readable_key replica_acquire_key.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__tryAcquire rp (tsW : u64) pwrsS pwrs ptsm sptsm :
    let ts := uint.nat tsW in
    valid_wrs pwrs ->
    is_dbmap_in_slice pwrsS pwrs -∗
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__tryAcquire #rp #tsW (to_val pwrsS)
    {{{ (acquired : bool), RET #acquired;
        if acquired
        then own_replica_ptsm_sptsm rp (acquire ts pwrs ptsm) (acquire ts pwrs sptsm) ∗
             ⌜validated_ptsm ptsm pwrs⌝ ∗
             ⌜validated_sptsm sptsm ts pwrs⌝
        else own_replica_ptsm_sptsm rp ptsm sptsm
    }}}.
  Proof.
    iIntros (ts Hvw) "#Hpwrs".
    iIntros (Φ) "!> Hrp HΦ".
    iPoseProof "Hpwrs" as "Hpwrs'".
    iDestruct "Hpwrs" as (pwrsL) "[HpwrsS %HpwrsL]".
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
    iMod (readonly_load with "HpwrsS") as (q) "HpwrsR".
    iDestruct (own_slice_small_sz with "HpwrsR") as %Hlen.
    set P := (λ (cont : bool), ∃ (pos : u64),
      let pwrs' := list_to_map (take (uint.nat pos) pwrsL) in
      "HpwrsR"  ∷ own_slice_small pwrsS (struct.t WriteEntry) (DfracOwn q) pwrsL ∗
      "HposP"   ∷ posP ↦[uint64T] #pos ∗
      "Hrp"     ∷ own_replica_ptsm_sptsm rp ptsm sptsm ∗
      "%Hptsm"  ∷ ⌜validated_ptsm ptsm pwrs'⌝ ∗
      "%Hsptsm" ∷ ⌜validated_sptsm sptsm ts pwrs'⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [HpwrsR HposP Hrp]"); last first; first 1 last.
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
      wp_apply (wp_SliceGet with "[$HpwrsR]"); first done.
      iIntros "HpwrsL".
      wp_pures.
      wp_apply (wp_Replica__writableKey with "Hrp").
      { apply list_elem_of_lookup_2 in Hwr.
        rewrite -HpwrsL in Hwr.
        apply elem_of_map_to_list, elem_of_dom_2 in Hwr.
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
    { iApply "HΦ".
      by iFrame "∗ %".
    }
    rewrite take_ge in Hptsm, Hsptsm; last word.
    pose proof (list_to_map_flip _ _ HpwrsL) as Hltm.
    rewrite -Hltm in Hptsm, Hsptsm.

    (*@     // Acquire locks for each key.                                      @*)
    (*@     rp.acquire(ts, pwrs)                                                @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__acquire with "Hpwrs' Hrp").
    { apply Hvw. }
    iIntros "Hrp".

    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ %".
  Qed.

End program.
