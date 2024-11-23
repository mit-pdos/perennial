From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__terminated rp (tsW : u64) cm :
    let ts := uint.nat tsW in
    {{{ own_replica_cm rp cm }}}
      Replica__terminated #rp #tsW
    {{{ RET #(bool_decide (ts ∈ dom cm)); own_replica_cm rp cm }}}.
  Proof.
    iIntros (ts Φ) "Hcm HΦ".
    wp_rec.

    (*@ func (rp *Replica) terminated(ts uint64) bool {                         @*)
    (*@     _, terminated := rp.txntbl[ts]                                      @*)
    (*@     return terminated                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hcm".
    wp_loadField.
    wp_apply (wp_MapGet with "Htxntbl").
    iIntros (v ok) "[%Hok Htxntbl]".
    wp_pures.
    case_bool_decide as Hts.
    { destruct ok; last first.
      { exfalso.
        apply map_get_false in Hok as [Hnone _].
        apply elem_of_dom in Hts as [b Hb].
        symmetry in Hcmabs.
        pose proof (lookup_kmap_eq_None _ _ _ _ _ Hcmabs Hnone) as Hcontra.
        specialize (Hcontra ts).
        unshelve epose proof (Hcontra _) as Hcmts; first word.
        by rewrite Hb in Hcmts.
      }
      iApply "HΦ". by iFrame "∗ %".
    }
    { destruct ok.
      { exfalso.
        apply map_get_true in Hok.
        apply not_elem_of_dom in Hts.
        pose proof (lookup_kmap_eq_None _ _ _ _ _ Hcmabs Hts) as Hcontra.
        specialize (Hcontra tsW).
        unshelve epose proof (Hcontra _) as Hcmts; first word.
        by rewrite Hok in Hcmts.
      }
      iApply "HΦ". by iFrame "∗ %".
    }
  Qed.

End program.
