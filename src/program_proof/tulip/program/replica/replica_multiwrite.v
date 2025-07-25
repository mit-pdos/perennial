From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import replica_repr.
From Perennial.program_proof.tulip.program.tuple Require Import tuple.
From Perennial.program_proof.tulip.program.index Require Import index.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__multiwrite rp (tsW : u64) pwrsS pwrs histm gid γ α :
    let ts := uint.nat tsW in
    let histm' := multiwrite ts pwrs histm in
    valid_pwrs gid pwrs ->
    dom histm = keys_all ->
    safe_extension ts pwrs histm ->
    ([∗ map] k ↦ h ∈ filter_group gid histm', is_repl_hist_lb γ k h) -∗
    is_replica_idx rp γ α -∗
    is_dbmap_in_slice pwrsS pwrs -∗
    {{{ own_replica_histm rp histm α }}}
      Replica__multiwrite #rp #tsW (to_val pwrsS)
    {{{ RET #();  own_replica_histm rp histm' α }}}.
  Proof.
    iIntros (ts histm' Hvw Hdomhistm Hlenhistm) "#Hrlbs #Hidx #Hpwrs".
    iIntros (Φ) "!> Hhistm HΦ".
    iDestruct "Hpwrs" as (pwrsL) "[HpwrsS %HpwrsL]".
    wp_rec.

    (*@ func (rp *Replica) multiwrite(ts uint64, pwrs []tulip.WriteEntry) {     @*)
    (*@     for _, ent := range pwrs {                                          @*)
    (*@         key := ent.Key                                                  @*)
    (*@         value := ent.Value                                              @*)
    (*@         tpl := rp.idx.GetTuple(key)                                     @*)
    (*@         if value.Present {                                              @*)
    (*@             tpl.AppendVersion(ts, value.Content)                        @*)
    (*@         } else {                                                        @*)
    (*@             tpl.KillVersion(ts)                                         @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iMod (readonly_load with "HpwrsS") as (q) "HpwrsR".
    iDestruct (own_slice_small_sz with "HpwrsR") as %Hlenpwrs.
    set P := (λ (i : u64),
      let pwrs' := list_to_map (take (uint.nat i) pwrsL) in
      own_replica_histm rp (multiwrite ts pwrs' histm) α)%I.
    wp_apply (wp_forSlice P with "[] [$HpwrsR Hhistm]"); last first; first 1 last.
    { (* Loop entry. *)
      subst P. simpl.
      rewrite uint_nat_W64_0 take_0 list_to_map_nil.
      by rewrite multiwrite_empty.
    }
    { (* Loop body. *)
      clear Φ.
      iIntros (i [k v]) "!>".
      iIntros (Φ) "(Hhistm & %Hbound & %Hi) HΦ".
      subst P. simpl.
      iNamed "Hidx".
      wp_loadField.
      (* Prove [k] in the domain of [pwrs] and in [keys_all]. *)
      apply list_elem_of_lookup_2 in Hi as Hpwrsv.
      rewrite -HpwrsL elem_of_map_to_list in Hpwrsv.
      apply elem_of_dom_2 in Hpwrsv as Hdompwrs.
      assert (Hvk : k ∈ keys_all).
      { clear -Hvw Hdompwrs. set_solver. }
      wp_apply (wp_Index__GetTuple with "Hidx"); first apply Hvk.
      iIntros (tpl) "#Htpl".
      (* Obtain proof that the current key [k] has not been written. *)
      pose proof (NoDup_fst_map_to_list pwrs) as Hnd.
      rewrite HpwrsL in Hnd.
      pose proof (list_lookup_fmap fst pwrsL (uint.nat i)) as Hk.
      rewrite Hi /= in Hk.
      pose proof (not_elem_of_take _ _ _ Hnd Hk) as Htake.
      rewrite -fmap_take in Htake.
      apply not_elem_of_list_to_map_1 in Htake as Hnone.
      (* Adjust the goal. *)
      rewrite uint_nat_word_add_S; last by word.
      rewrite (take_S_r _ _ _ Hi) list_to_map_snoc; last done.
      set pwrs' := (list_to_map _) in Hnone *.
      assert (is_Some (histm !! k)) as [h Hh].
      { by rewrite -elem_of_dom Hdomhistm. }
      (* Obtain the length constraint. *)
      rewrite /safe_extension in Hlenhistm.
      set histmwr := filter _ _ in Hlenhistm.
      assert (Hhistmwrk : histmwr !! k = Some h).
      { by apply map_lookup_filter_Some_2. }
      specialize (Hlenhistm _ _ Hhistmwrk). simpl in Hlenhistm.
      (* Obtain the replicated history lb. *)
      assert (Hh' : histm' !! k = Some (last_extend ts h ++ [v])).
      { by rewrite (multiwrite_modified Hpwrsv Hh). }
      iDestruct (big_sepM_lookup _ _ k with "Hrlbs") as "Hrlb".
      { apply map_lookup_filter_Some_2; first apply Hh'. simpl.
        clear -Hdompwrs Hvw. set_solver.
      }
      (* Take the physical history out. *)
      iDestruct (big_sepM_delete with "Hhistm") as "[Hh Hhistm]".
      { rewrite multiwrite_unmodified; [apply Hh | apply Hnone]. }
      destruct v as [s |]; wp_pures.
      { (* Case: [@AppendVersion]. *)
        wp_apply (wp_Tuple__AppendVersion with "Hrlb Htpl Hh").
        { apply Hlenhistm. }
        iIntros "Hh".
        iDestruct (big_sepM_insert_2 with "Hh Hhistm") as "Hhistm".
        rewrite insert_delete_eq /multiwrite.
        erewrite insert_merge_l; last first.
        { by rewrite Hh. }
        iApply "HΦ".
        iFrame "∗ #".
      }
      { (* Case: [@KillVersion]. *)
        wp_apply (wp_Tuple__KillVersion with "Hrlb Htpl Hh").
        { apply Hlenhistm. }
        iIntros "Hh".
        iDestruct (big_sepM_insert_2 with "Hh Hhistm") as "Hhistm".
        rewrite insert_delete_eq /multiwrite.
        erewrite insert_merge_l; last first.
        { by rewrite Hh. }
        iApply "HΦ".
        iFrame "∗ #".
      }
    }
    iIntros "[Hhistm _]". subst P. simpl.
    wp_pures.
    iApply "HΦ".
    pose proof (list_to_map_flip _ _ HpwrsL) as Hltm.
    rewrite -Hlenpwrs firstn_all -Hltm.
    by iFrame.
  Qed.

End program.
