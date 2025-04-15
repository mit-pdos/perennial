From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__latestProposal (gpp : loc) pps rk ts cid gid γ :
    pps ≠ ∅ ->
    {{{ own_backup_gpreparer_pps gpp pps rk ts cid gid γ }}}
      BackupGroupPreparer__latestProposal #gpp
    {{{ (p : ppsl), RET (ppsl_to_val p); 
        own_backup_gpreparer_pps gpp pps rk ts cid gid γ ∗
        ⌜p ∈ (map_img pps : gset ppsl)⌝ ∧
        ⌜map_Forall (λ _ x, (uint.nat x.1 ≤ uint.nat p.1)%nat) pps⌝
    }}}.
  Proof.
    (*@ func (gpp *BackupGroupPreparer) latestProposal() tulip.PrepareProposal { @*)
    (*@     var latest tulip.PrepareProposal                                    @*)
    (*@                                                                         @*)
    (*@     for _, pp := range(gpp.pps) {                                       @*)
    (*@         if latest.Rank < pp.Rank {                                      @*)
    (*@             latest = pp                                                 @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return latest                                                       @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
