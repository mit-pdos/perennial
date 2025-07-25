From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__releaseKey rp key ptsm sptsm :
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__releaseKey #rp #(LitString key)
    {{{ RET #();
        own_replica_ptsm_sptsm rp (<[key := O]> ptsm) sptsm
    }}}.
  Proof.
    iIntros (Φ) "Hrp HΦ".
    wp_rec.
    (*@ func (rp *Replica) releaseKey(key string) {                             @*)
    (*@     delete(rp.ptsm, key)                                                @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapDelete with "HptsmM").
    iIntros "HptsmM".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ %".
    iPureIntro.
    intros k Hk.
    destruct (decide (k = key)) as [-> | Hne]; last first.
    { rewrite lookup_delete_ne; last done.
      rewrite lookup_insert_ne; last done.
      by apply Hptsmabs.
    }
    by rewrite lookup_delete_eq lookup_insert_eq.
  Qed.

End program.
