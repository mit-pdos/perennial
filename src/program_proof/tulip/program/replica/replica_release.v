From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_release_key.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__release rp pwrsS pwrs ptsm sptsm :
    valid_wrs pwrs ->
    {{{ own_dbmap_in_slice pwrsS pwrs ∗ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__release #rp (to_val pwrsS)
    {{{ RET #(); 
        own_dbmap_in_slice pwrsS pwrs ∗
        own_replica_ptsm_sptsm rp (release pwrs ptsm) sptsm
    }}}.
  Proof.
    iIntros (Hvw Φ) "[Hpwrs Hrp] HΦ".
    iDestruct "Hpwrs" as (pwrsL) "[HpwrsS %HpwrsL]".
    wp_rec.
    iDestruct (own_replica_ptsm_sptsm_dom with "Hrp") as %[Hdomptsm Hdomsptsm].

    (*@ func (rp *Replica) release(pwrs []tulip.WriteEntry) {                   @*)
    (*@     for _, ent := range pwrs {                                          @*)
    (*@         key := ent.Key                                                  @*)
    (*@         rp.releaseKey(key)                                              @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iDestruct (own_slice_sz with "HpwrsS") as %Hlenpwrs.
    iDestruct (own_slice_small_acc with "HpwrsS") as "[HpwrsS HpwrsC]".
    set P := (λ (i : u64),
      let pwrs' := list_to_map (take (uint.nat i) pwrsL) in
      own_replica_ptsm_sptsm rp (release pwrs' ptsm) sptsm)%I.
    wp_apply (wp_forSlice P with "[] [$HpwrsS Hrp]"); last first; first 1 last.
    { (* Loop entry. *)
      subst P. simpl.
      rewrite uint_nat_W64_0 take_0 list_to_map_nil.
      by rewrite release_empty.
    }
    { (* Loop body. *)
      clear Φ.
      iIntros (i [k v]) "!>".
      iIntros (Φ) "(Hrp & %Hbound & %Hi) HΦ".
      subst P. simpl.
      wp_pures.
      wp_apply (wp_Replica__releaseKey with "Hrp").
      iIntros "Hrp".
      iApply "HΦ".
      (* Obtain proof that the current key [k] has not been written. *)
      pose proof (map_to_list_not_elem_of_take_key _ _ _ _ HpwrsL Hi) as Htake.
      (* Adjust the goal. *)
      rewrite uint_nat_word_add_S; last by word.
      rewrite (take_S_r _ _ _ Hi) list_to_map_snoc; last apply Htake.
      set pwrs' := list_to_map _.
      rewrite /release setts_insert; last first.
      { apply elem_of_list_lookup_2 in Hi.
        rewrite -HpwrsL in Hi.
        apply elem_of_map_to_list, elem_of_dom_2 in Hi.
        clear -Hvw Hi Hdomptsm. set_solver.
      }
      done.
    }
    iIntros "[Hrp HpwrsS]".
    subst P. simpl.
    pose proof (list_to_map_flip _ _ HpwrsL) as Hltm.
    rewrite -Hlenpwrs firstn_all Hltm.
    iDestruct ("HpwrsC" with "HpwrsS") as "HpwrsS".
    wp_pures.
    iApply "HΦ".
    iFrame.
    by rewrite -Hltm.
  Qed.

End program.
