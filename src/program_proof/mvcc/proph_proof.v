From Perennial.program_proof Require Export grove_prelude.
From Goose.github_com.mit_pdos.go_mvcc Require Import proph.
From Perennial.program_proof.mvcc Require Import mvcc_ghost.

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

Lemma wp_ResolveRead γ p (tid key : u64) :
  ⊢ <<< ∀∀ acs, mvcc_proph γ p acs >>>
      ResolveRead #p #tid #key @ ∅
    <<< ∃ acs', ⌜acs = EvRead tid key :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
    {{{ RET #(); True }}}.
Admitted.

Lemma wp_ResolveAbort γ p (tid : u64) :
  ⊢ <<< ∀∀ acs, mvcc_proph γ p acs >>>
      ResolveAbort #p #tid @ ∅
    <<< ∃ acs', ⌜acs = EvAbort tid :: acs'⌝ ∗ mvcc_proph γ p acs' >>>
    {{{ RET #(); True }}}.
Admitted.

(*
FIXME needs a gmap representation of wrbuf?
Lemma wp_ResolveCommit γ p acs (tid : u64) (wrbuf : dbmap)  :
  {{{ mvcc_proph γ p acs }}}
    ResolveCommit #p #tid ??
  {{{ acs', RET #(); ⌜acs = EvCommit tid wrbuf :: acs⌝ ∗ mvcc_proph γ p acs' }}}.
Admitted.
*)

End proph.
