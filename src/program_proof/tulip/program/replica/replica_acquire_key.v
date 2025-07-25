From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__acquireKey rp (ts : u64) key ptsm sptsm :
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__acquireKey #rp #ts #(LitString key)
    {{{ RET #();
        own_replica_ptsm_sptsm rp (<[key := uint.nat ts]> ptsm) (<[key := uint.nat ts]> sptsm)
    }}}.
  Proof.
    iIntros (Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) acquireKey(ts uint64, key string) {                  @*)
    (*@     rp.ptsm[key]  = ts                                                  @*)
    (*@     rp.sptsm[key] = ts                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapInsert with "HptsmM"); first done.
    iIntros "HptsmM".
    wp_loadField.
    wp_apply (wp_MapInsert with "HsptsmM"); first done.
    iIntros "HsptsmM".
    wp_pures.
    iApply "HΦ".
    iFrame "HptsmP HsptsmP ∗".
    iPureIntro.
    split.
    { intros k Hk.
      destruct (decide (k = key)) as [-> | Hne]; last first.
      { do 2 (rewrite lookup_insert_ne; last done).
        by apply Hptsmabs.
      }
      by rewrite 2!lookup_insert_eq.
    }
    { intros k Hk.
      destruct (decide (k = key)) as [-> | Hne]; last first.
      { do 2 (rewrite lookup_insert_ne; last done).
        by apply Hsptsmabs.
      }
      by rewrite 2!lookup_insert_eq.
    }
  Qed.

End program.
