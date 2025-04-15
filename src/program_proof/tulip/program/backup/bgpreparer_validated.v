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
    (*@ func (gpp *BackupGroupPreparer) validated(rid uint64) bool {            @*)
    (*@     _, validated := gpp.vdm[rid]                                        @*)
    (*@     return validated                                                    @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
