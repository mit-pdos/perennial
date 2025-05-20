From Perennial.program_proof.tulip.program Require Import prelude replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__lastProposal rp (tsW : u64) psm rkm :
    let ts := uint.nat tsW in
    {{{ own_replica_psm_rkm rp psm rkm }}}
      Replica__lastProposal #rp #tsW
    {{{ (rank : u64) (pdec : bool) (ok : bool), RET (#rank, #pdec, #ok);
        own_replica_psm_rkm rp psm rkm ∗
        ⌜if ok
         then psm !! ts = Some (uint.nat rank, pdec)
         else psm !! ts = None ∧ rank = W64 0 ∧ pdec = false⌝
    }}}.
  Proof.
    iIntros (ts Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) lastProposal(ts uint64) (uint64, bool, bool) {       @*)
    (*@     ps, ok := rp.pstbl[ts]                                              @*)
    (*@     return ps.rank, ps.dec, ok                                          @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapGet with "Hpstbl").
    iIntros (psl ok) "[%Hok Hpstbl]".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ %".
    iPureIntro.
    destruct ok.
    { apply map_get_true in Hok.
      assert (Hpstbl : fmap ppsl_to_nat_bool pstbl !! tsW = Some (uint.nat psl.1, psl.2)).
      { by rewrite lookup_fmap Hok. }
      symmetry in Hpsmabs.
      pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hpsmabs Hpstbl) as (ts' & Hts' & Hpsmts).
      assert (ts' = ts) as ->.
      { subst ts. rewrite Hts'. lia. }
      done.
    }
    { apply map_get_false in Hok as [Hnone Hzv].
      assert (Hpstbl : fmap ppsl_to_nat_bool pstbl !! tsW = None).
      { by rewrite lookup_fmap Hnone. }
      symmetry in Hpsmabs.
      split.
      { apply (lookup_kmap_eq_None _ _ _ _ _ Hpsmabs Hpstbl).
        word.
      }
      by inv Hzv.
    }
  Qed.

End program.
