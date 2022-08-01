From Perennial.program_proof Require Export grove_prelude.
From Goose.github_com.mit_pdos.go_mvcc Require Import proph.
From Perennial.program_proof.mvcc Require Import mvcc_ghost wrbuf_proof.

Section proph.
Context `{!heapGS Σ}.

(* FIXME: define and prove these. *)

Definition mvcc_proph (γ : mvcc_names) (p : proph_id) (acs : list action) : iProp Σ.
Admitted.

Global Instance mvcc_proph_timeless γ p acs :
  Timeless (mvcc_proph γ p acs).
Admitted.

Lemma wp_NewProphActions γ :
  {{{ True }}}
    NewProph #()
  {{{ (p : proph_id) acs, RET #p; mvcc_proph γ p acs }}}.
Admitted.

Lemma wp_ResolveRead γ p (tid key : u64) (ts : nat) :
  ⊢ {{{ ⌜int.nat tid = ts⌝ }}}
    <<< ∀∀ acs, mvcc_proph γ p acs >>>
      ResolveRead #p #tid #key @ ∅
    <<< ∃ acs', ⌜acs = EvRead ts key :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
    {{{ RET #(); True }}}.
Admitted.

Lemma wp_ResolveAbort γ p (tid : u64) (ts : nat) :
  ⊢ {{{ ⌜int.nat tid = ts⌝ }}}
    <<< ∀∀ acs, mvcc_proph γ p acs >>>
      ResolveAbort #p #tid @ ∅
    <<< ∃ acs', ⌜acs = EvAbort ts :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
    {{{ RET #(); True }}}.
Admitted.

Lemma wp_ResolveCommit γ p (tid : u64) (ts : nat) (wrbuf : loc) (m : dbmap) :
  ⊢ {{{ ⌜int.nat tid = ts⌝ ∗ own_wrbuf wrbuf m }}}
    <<< ∀∀ acs, mvcc_proph γ p acs >>>
      ResolveCommit #p #tid #wrbuf @ ∅
    <<< ∃ acs', ⌜acs = EvCommit ts m :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
    {{{ RET #(); own_wrbuf wrbuf m }}}.
Admitted.

End proph.
