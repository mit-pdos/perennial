From Perennial.program_proof.mvcc Require Import txnsite_prelude.
From Perennial.program_proof.mvcc Require Import txnsite_repr tid_proof.
  
Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition init_txnsite sid γ : iProp Σ :=
  ∃ proph,
    "HactiveAuth"  ∷ site_active_tids_half_auth γ sid ∅ ∗
    "HsidOwn"      ∷ sid_own γ sid ∗
    "#Hinvtid"     ∷ have_gentid γ ∗
    "#Hinvgc"      ∷ mvcc_inv_gc γ ∗
    "#Hinvsst"     ∷ mvcc_inv_sst γ proph ∗
    "%HsidBounded" ∷ ⌜(int.Z sid) < N_TXN_SITES⌝.

Theorem wp_MkTxnSite (sid : u64) γ :
  {{{ init_txnsite sid γ }}}
    MkTxnSite #sid
  {{{ (site : loc), RET #site; is_txnsite site sid γ  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  wp_call.
  
  (*@ func MkTxnSite(sid uint64) *TxnSite {                                   @*)
  (*@     site := new(TxnSite)                                                @*)
  (*@     site.latch = new(cfmutex.CFMutex)                                   @*)
  (*@     site.tids  = make([]uint64, 0, 8)                                   @*)
  (*@     site.sid   = sid                                                    @*)
  (*@                                                                         @*)
  wp_apply (wp_allocStruct); first by auto 10.
  iIntros (site) "Hsite".
  iDestruct (struct_fields_split with "Hsite") as "Hsite".
  iNamed "Hsite". simpl.
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (latch) "Hfree".
  wp_storeField.
  wp_apply (wp_NewSliceWithCap (V:=u64)); first word.
  iIntros (tids) "HtidsR".
  do 2 wp_storeField.

  iNamed "H".
  iMod (readonly_alloc_1 with "latch") as "#Hlatch".
  iMod (alloc_lock mvccN _ latch (own_txnsite site sid γ) with "Hfree [-HΦ]") as "#Hlock".
  { iNext.
    unfold own_txnsite.
    iExists (Slice.mk tids 0 8), [], ∅.
    replace (int.nat (U64 0)) with 0%nat by word.
    iFrame "∗%#".
    iPureIntro.
    rewrite fmap_nil.
    split; [done | apply NoDup_nil_2].
  }
  
  (*@     return site                                                         @*)
  (*@ }                                                                       @*)
  iApply "HΦ".
  unfold is_txnsite.
  eauto 10 with iFrame.
Qed.

End program.
