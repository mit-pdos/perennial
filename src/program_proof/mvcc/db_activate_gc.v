From Perennial.program_proof.mvcc Require Import
     txn_prelude db_repr db_get_safe_ts
     index_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_DB__gc db γ :
  is_db db γ -∗
  {{{ True }}}
    DB__gc #db
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hdb" (Φ) "!> _ HΦ".
  wp_rec. wp_pures.

  (*@ func (db *DB) gc() {                                                    @*)
  (*@     tidMin := db.getSafeTS()                                            @*)
  (*@                                                                         @*)
  wp_apply (wp_DB__getSafeTS with "Hdb").
  iIntros (tid) "#Hminlb".
  wp_pures.
  iNamed "Hdb".
  
  (*@     if tidMin < config.TID_SENTINEL {                                   @*)
  (*@         db.idx.DoGC(tidMin)                                             @*)
  (*@     }                                                                   @*)
  (*@ }                                                                       @*)
  wp_if_destruct.
  { (* Actually do the GC. *)
    wp_loadField.
    wp_apply (wp_index__DoGC with "HidxRI Hminlb").
    wp_pures.
    by iApply "HΦ".
  }
  (* Do nothing as no active txns. *)
  by iApply "HΦ".
Qed.

Theorem wp_DB__ActivateGC db γ :
  is_db db γ -∗
  {{{ True }}}
    DB__ActivateGC #db
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hdb" (Φ) "!> _ HΦ".
  wp_rec. wp_pures.

  (*@ func (db *DB) ActivateGC() {                                            @*)
  (*@     go func() {                                                         @*)
  (*@         for {                                                           @*)
  (*@             db.gc()                                                     @*)
  (*@             machine.Sleep(1 * 1000000)                                  @*)
  (*@         }                                                               @*)
  (*@     }()                                                                 @*)
  (*@ }                                                                       @*)
  wp_apply wp_fork.
  { (* Forked process. *)
    wp_pures.
    wp_apply (wp_forBreak (λ _, True)%I); last done.
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.
    wp_apply (wp_DB__gc with "Hdb").
    wp_apply wp_Sleep.
    wp_pures.
    by iApply "HΦ".
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End program.
