From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_getTimestamp (sid : u64) γ :
    ⊢
    {{{ True }}}
    <<< ∀∀ (ts : nat), own_largest_ts γ ts >>>
      getTimestamp #sid @ ↑tsNS
    <<< ∃∃ (ts' : nat), own_largest_ts γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
    {{{ (tid : u64), RET #tid; ⌜uint.nat tid = ts'⌝ }}}.
  Proof.
    iIntros (Φ) "!> _ HAU".
    wp_rec.

    (*@ func getTimestamp(sid uint64) uint64 {                                  @*)
    (*@     ts := trusted_time.GetTime()                                        @*)
    (*@                                                                         @*)
    (*@     n := params.N_TXN_SITES                                             @*)
    (*@     tid := std.SumAssumeNoOverflow(ts, n) / n * n + sid                 @*)
    (*@                                                                         @*)
    (*@     for trusted_time.GetTime() <= tid {                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return tid                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Txn__begin (txn : loc) γ :
    ⊢ {{{ own_txn_uninit txn γ }}}
      <<< ∀∀ (ts : nat), own_largest_ts γ ts >>>
        Txn__begin #txn @ ↑tsNS
      <<< ∃∃ (ts' : nat), own_largest_ts γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
      {{{ RET #(); own_txn_init txn ts' γ }}}.
  Proof.
    iIntros (Φ) "!> Htxn HAU".
    wp_rec.

    (*@ func (txn *Txn) begin() {                                               @*)
    (*@     txn.ts = getTimestamp(txn.sid)                                      @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn". iNamed "Hsid".
    wp_loadField.
    wp_apply (wp_getTimestamp).
    iNamed "Hts".
    iMod "HAU" as (ts) "[Hts HAU]".
    iFrame "Hts".
    iIntros "!>" (ts') "[Hts %Hts]".
    iMod ("HAU" with "[$Hts]") as "HΦ"; first done.
    iModIntro.
    iIntros (tidW HtidW).
    wp_storeField.
    iApply "HΦ".
    iAssert (own_txn_ts txn ts')%I with "[$HtsW]" as "Hts"; first done.
    iFrame "∗ #".
    iPureIntro.
    rewrite /valid_ts. word.
  Qed.

End program.
