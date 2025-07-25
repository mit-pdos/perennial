From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr txn_key_to_group.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__setwrs (txn : loc) (key : byte_string) (value : dbval) wrs :
    valid_key key ->
    {{{ own_txn_wrs txn (DfracOwn 1) wrs }}}
      Txn__setwrs #txn #(LitString key) (dbval_to_val value)
    {{{ RET #(); own_txn_wrs txn (DfracOwn 1) (<[key := value]> wrs) }}}.
  Proof.
    iIntros (Hvk Φ) "Hwrs HΦ".
    wp_rec.

    (*@ func (txn *Txn) setwrs(key string, value Value) {                       @*)
    (*@     gid := KeyToGroup(key)                                              @*)
    (*@     pwrs := txn.wrs[gid]                                                @*)
    (*@                                                                         @*)
    wp_apply (wp_Txn__keyToGroup with "Hwrs").
    { apply Hvk. }
    iIntros (gid) "[Hwrs %Hgid]".
    do 2 iNamed "Hwrs".
    wp_loadField.
    wp_apply (wp_MapGet with "HpwrsmP").
    iIntros (pwrsP ok) "[%Hget HpwrsmP]".
    destruct ok; last first.
    { apply map_get_false in Hget as [Hget _].
      rewrite -not_elem_of_dom Hdomwrs -Hgid in Hget.
      by pose proof (elem_of_key_to_group key).
    }
    apply map_get_true in Hget.
    iAssert (⌜is_Some (pwrsm !! gid)⌝)%I as %[pwrs Hpwrs].
    { iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom.
      iPureIntro.
      by rewrite -elem_of_dom -Hdom elem_of_dom.
    }
    iDestruct (big_sepM2_delete with "Hpwrsm") as "[Hpwrs Hpwrsm]"; [done | done |].

    (*@     pwrs[key] = value                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_MapInsert with "Hpwrs"); first done.
    iIntros "Hpwrs".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hwrsp"); first done.
    iIntros "Hwrsp".
    wp_pures.
    iApply "HΦ".
    set pwrs' := <[key := value]> pwrs.
    iAssert ([∗ map] p; m ∈ pwrsmP; <[gid := pwrs']> pwrsm, own_map p (DfracOwn 1) m)%I
      with "[Hpwrsm Hpwrs]" as "Hpwrsm".
    { iDestruct (big_sepM2_insert_2 (λ k p m, own_map p (DfracOwn 1) m) _ _ gid with "Hpwrs Hpwrsm")
        as "Hpwrsm".
      rewrite insert_delete_id; last apply Hget.
      rewrite insert_delete_eq.
      done.
    }
    iFrame "∗ %".
    iPureIntro.
    intros g m Hgm.
    destruct (decide (gid = g)) as [-> | Hne].
    - rewrite lookup_insert_eq in Hgm. inv Hgm.
      specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
      by rewrite Hwrsg wrs_group_insert.
    - rewrite lookup_insert_ne in Hgm; last done.
      specialize (Hwrsg _ _ Hgm). simpl in Hwrsg.
      subst m.
      by rewrite wrs_group_insert_ne; last rewrite Hgid.
  Qed.

End program.
