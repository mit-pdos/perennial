From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.goose_lang.trusted.github_com.mit_pdos.tulip Require Import trusted_proph.

Section proph.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Lemma wp_ResolveRead p (tid : u64) (key : string) (ts : nat) :
    ⊢
    {{{ ⌜uint.nat tid = ts⌝ }}}
    <<< ∀∀ acs, own_txn_proph p acs >>>
      ResolveRead #p #tid #(LitString key) @ ∅
    <<< ∃ acs', ⌜acs = ActRead ts key :: acs'⌝ ∗ own_txn_proph p acs' >>>
    {{{ RET #(); True }}}.
  Admitted.

  Lemma wp_ResolveAbort p (tid : u64) (ts : nat) :
    ⊢
    {{{ ⌜uint.nat tid = ts⌝ }}}
    <<< ∀∀ acs, own_txn_proph p acs >>>
      ResolveAbort #p #tid @ ∅
    <<< ∃ acs', ⌜acs = ActAbort ts :: acs'⌝ ∗ own_txn_proph p acs' >>>
    {{{ RET #(); True }}}.
  Admitted.

  Lemma wp_ResolveCommit
    p (tid : u64) (ts : nat) (wrsP : loc) q (wrs : dbmap) :
    ⊢
    {{{ ⌜uint.nat tid = ts⌝ ∗ own_map wrsP q wrs }}}
    <<< ∀∀ acs, own_txn_proph p acs >>>
      ResolveCommit #p #tid #wrsP @ ∅
    <<< ∃ acs', ⌜acs = ActCommit ts wrs :: acs'⌝ ∗ own_txn_proph p acs' >>>
    {{{ RET #(); own_map wrsP q wrs }}}.
  Admitted.

End proph.
