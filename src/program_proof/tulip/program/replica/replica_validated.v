From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__validated (rp : loc) (tsW : u64) cpm :
    let ts := uint.nat tsW in
    {{{ own_replica_cpm rp cpm }}}
      Replica__validated #rp #tsW
    {{{ (pwrsP : Slice.t) (vd : bool), RET (to_val pwrsP, #vd);
        own_replica_cpm rp cpm ∗
        if vd
        then ∃ pwrs, is_dbmap_in_slice pwrsP pwrs ∧ ⌜cpm !! ts = Some pwrs⌝
        else True
    }}}.
  Proof.
    iIntros (ts Φ) "Hcpm HΦ".
    wp_rec.

    (*@ func (rp *Replica) validated(ts uint64) ([]tulip.WriteEntry, bool) {    @*)
    (*@     pwrs, ok := rp.prepm[ts]                                            @*)
    (*@     return pwrs, ok                                                     @*)
    (*@ }                                                                       @*)
    iNamed "Hcpm".
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (pwrsP ok) "[%Hget HprepmS]".
    wp_pures.
    iModIntro.
    destruct ok; last first.
    { iApply "HΦ". by iFrame "∗ # %". }
    apply map_get_true in Hget.
    iDestruct (big_sepM2_lookup_l with "Hprepm") as (pwrs) "[%Hpwrs Hpwrs]".
    { apply Hget. }
    iApply "HΦ".
    iFrame "∗ # %".
    iPureIntro.
    symmetry in Hcpmabs.
    pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hpwrs) as (ts' & Hts' & Hcpmts).
    by assert (ts' = ts) as -> by word.
  Qed.

End program.
