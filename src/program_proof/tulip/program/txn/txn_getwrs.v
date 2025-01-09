From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr txn_key_to_group.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__getwrs (txn : loc) (key : byte_string) q wrs :
    valid_key key ->
    {{{ own_txn_wrs txn q wrs }}}
      Txn__getwrs #txn #(LitString key)
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok);
        own_txn_wrs txn q wrs ∗ ⌜wrs !! key = if ok then Some v else None⌝
    }}}.
  Proof.
    iIntros (Hvk Φ) "Hwrs HΦ".
    wp_rec.

    (*@ func (txn *Txn) getwrs(key string) (Value, bool) {                      @*)
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
    iDestruct (big_sepM2_lookup_acc with "Hpwrsm") as "[Hpwrs HpwrsmC]"; [done | done |].

    (*@     v, ok := pwrs[key]                                                  @*)
    (*@     return v, ok                                                        @*)
    (*@ }                                                                       @*)
    wp_apply (wp_MapGet with "Hpwrs").
    iIntros (v ok) "[%Hv Hpwrs]".
    wp_pures.
    iApply "HΦ".
    iDestruct ("HpwrsmC" with "Hpwrs") as "Hpwrsm".
    iFrame "∗ # %".
    iPureIntro.
    specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
    rewrite Hwrsg in Hv.
    destruct ok.
    - apply map_get_true in Hv.
      rewrite lookup_wrs_group_Some in Hv.
      by destruct Hv as [Hv _].
    - apply map_get_false in Hv as [Hv _].
      rewrite lookup_wrs_group_None in Hv.
      by destruct Hv.
  Qed.

End program.
