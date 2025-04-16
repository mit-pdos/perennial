From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (* Rather weak spec as it's used only in a performance optimization. *)
  Theorem wp_BackupGroupPreparer__validated (gpp : loc) (rid : u64) ts gid γ :
    {{{ own_backup_gpreparer_vdm gpp ts gid γ }}}
      BackupGroupPreparer__validated #gpp #rid
    {{{ (validated : bool), RET #validated; own_backup_gpreparer_vdm gpp ts gid γ }}}.
  Proof.
    iIntros (Φ) "Hvdm HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) validated(rid uint64) bool {            @*)
    (*@     _, validated := gpp.vdm[rid]                                        @*)
    (*@     return validated                                                    @*)
    (*@ }                                                                       @*)
    iNamed "Hvdm".
    wp_loadField.
    wp_apply (wp_MapGet with "Hvdm").
    iIntros (b ok) "[%Hget Hvdm]".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
