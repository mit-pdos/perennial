From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (* Rather weak spec as it's used only in a performance optimization. *)
  Theorem wp_BackupGroupPreparer__inquired (gpp : loc) (rid : u64) pps rk ts cid gid γ :
    {{{ own_backup_gpreparer_pps gpp pps rk ts cid gid γ }}}
      BackupGroupPreparer__inquired #gpp #rid
    {{{ (inquired : bool), RET #inquired; own_backup_gpreparer_pps gpp pps rk ts cid gid γ }}}.
  Proof.
    (*@ func (gpp *BackupGroupPreparer) inquired(rid uint64) bool {             @*)
    (*@     _, inquired := gpp.pps[rid]                                         @*)
    (*@     return inquired                                                     @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
