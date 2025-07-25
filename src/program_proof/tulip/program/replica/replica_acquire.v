From Perennial.program_proof.tulip.invariance Require Import validate.
From Perennial.program_proof.tulip.program Require Import prelude replica_repr.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_writable_key replica_readable_key replica_acquire_key.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__acquire rp (tsW : u64) pwrsS pwrs ptsm sptsm :
    let ts := uint.nat tsW in
    valid_wrs pwrs ->
    is_dbmap_in_slice pwrsS pwrs -∗
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__acquire #rp #tsW (to_val pwrsS)
    {{{ RET #();
        own_replica_ptsm_sptsm rp (acquire ts pwrs ptsm) (acquire ts pwrs sptsm)
    }}}.
  Proof.
    iIntros (ts Hvw) "#Hpwrs".
    iIntros (Φ) "!> Hrp HΦ".
    iDestruct "Hpwrs" as (pwrsL) "[HpwrsS %HpwrsL]".
    wp_rec.
    iDestruct (own_replica_ptsm_sptsm_dom with "Hrp") as %[Hdomptsm Hdomsptsm].

    (*@ func (rp *Replica) acquire(ts uint64, pwrs []tulip.WriteEntry) {        @*)
    (*@     for _, ent := range(pwrs) {                                         @*)
    (*@         rp.acquireKey(ts, ent.Key)                                      @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iMod (readonly_load with "HpwrsS") as (q) "HpwrsR".
    iDestruct (own_slice_small_sz with "HpwrsR") as %Hlen.
    set P := (λ (i : u64),
                let pwrs' := list_to_map (take (uint.nat i) pwrsL) in
                own_replica_ptsm_sptsm rp (acquire ts pwrs' ptsm) (acquire ts pwrs' sptsm))%I.
    wp_apply (wp_forSlice P with "[] [$HpwrsR Hrp]"); last first; first 1 last.
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
      { apply list_elem_of_lookup_2 in Hi.
        rewrite -HpwrsL in Hi.
        apply elem_of_map_to_list, elem_of_dom_2 in Hi.
        clear -Hvw Hi Hdomptsm. set_solver.
      }
      rewrite /acquire setts_insert; last first.
      { apply list_elem_of_lookup_2 in Hi.
        rewrite -HpwrsL in Hi.
        apply elem_of_map_to_list, elem_of_dom_2 in Hi.
        clear -Hvw Hi Hdomsptsm. set_solver.
      }
      done.
    }
    iIntros "[HP _]".
    iNamed "HP". clear P.
    pose proof (list_to_map_flip _ _ HpwrsL) as Hltm.
    rewrite -Hlen firstn_all -Hltm in Hptsmabs, Hsptsmabs.
    wp_pures.
    iApply "HΦ".
    by iFrame "HptsmP HsptsmP ∗ %".
  Qed.

End program.
