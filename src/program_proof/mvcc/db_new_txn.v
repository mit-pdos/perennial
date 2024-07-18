From Perennial.program_proof.mvcc Require Import
     txn_prelude db_repr txnsite_repr txn_repr
     wrbuf_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_DB__NewTxn db γ :
  is_db db γ -∗
  {{{ True }}}
    DB__NewTxn #db
  {{{ (txn : loc), RET #txn; own_txn_uninit txn γ }}}.
Proof.
  iIntros "#Hdb" (Φ) "!> _ HΦ".
  iPoseProof "Hdb" as "Hdb'".
  iNamed "Hdb".
  wp_rec. wp_pures.

  (*@ func (db *DB) NewTxn() *Txn {                                           @*)
  (*@     db.latch.Lock()                                                     @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HdbOwn]".
  iNamed "HdbOwn".
  wp_pures.
  
  (*@     txn := &Txn { proph : db.proph }                                    @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (wp_allocStruct); first auto 10.
  iIntros (txn) "Htxn".
  iDestruct (struct_fields_split with "Htxn") as "Htxn".
  iNamed "Htxn".
  simpl.
  wp_pures.

  (*@     txn.site  = db.sites[db.sid]                                        @*)
  (*@                                                                         @*)
  do 2 wp_loadField.
  iMod (readonly_load with "HsitesS") as (q) "HsitesS'".
  list_elem sitesL (uint.nat sidcur) as site.
  wp_apply (wp_SliceGet with "[$HsitesS']").
  { iPureIntro.
    rewrite list_lookup_fmap.
    by rewrite Hsite_lookup.
  }
  iIntros "HsitesS'".
  wp_storeField.

  (*@     txn.wrbuf = wrbuf.MkWrBuf()                                         @*)
  (*@     txn.idx   = db.idx                                                  @*)
  (*@                                                                         @*)
  wp_apply (wp_MkWrBuf).
  iIntros (wrbuf) "HwrbufRP".
  wp_storeField.
  wp_loadField.
  wp_storeField.

  (*@     db.sid = db.sid + 1                                                 @*)
  (*@     if db.sid >= config.N_TXN_SITES {                                   @*)
  (*@         db.sid = 0                                                      @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_pures.
  wp_storeField.
  wp_loadField.
  wp_apply (wp_If_join_evar with "[Hsidcur]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    { wp_pures.
      wp_storeField.
      iSplit; first done.
      replace (W64 0) with (if b' then (W64 0) else (word.add sidcur (W64 1))) by by rewrite Eb'.
      iNamedAccu.
    }
    { wp_pures.
      iModIntro.
      subst.
      by iFrame "∗".
    }
  }
  iIntros "H".
  iNamed "H".
  wp_pures.

  (*@     db.latch.Unlock()                                                   @*)
  (*@     return txn                                                          @*)
  (*@ }                                                                       @*)
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hsidcur]").
  { iFrame "Hlock Hlocked".
    iNext.
    unfold own_db.
    iExists _.
    iFrame.
    iSplit; last done.
    iPureIntro.
    case_bool_decide; first done.
    apply Znot_le_gt in H.
    by apply Z.gt_lt.
  }
  wp_pures.
  iApply "HΦ".
  iMod (readonly_alloc_1 with "idx") as "#Hidx_txn".
  iMod (readonly_alloc_1 with "proph") as "#Hproph_txn".
  replace (uint.nat 0) with 0%nat by word.
  simpl.
  do 7 iExists _.
  iFrame.
  iDestruct (big_sepL_lookup with "HsitesRP") as "HsiteRP"; first done.
  eauto 20 with iFrame.
Qed.

End program.
