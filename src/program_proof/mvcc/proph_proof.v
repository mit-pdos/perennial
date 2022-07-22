From Perennial.program_proof Require Export grove_prelude.
From Goose.github_com.mit_pdos.go_mvcc Require Import proph.
From Perennial.program_proof.mvcc Require Import mvcc_ghost.

Section proph.
Context `{!heapGS Σ}.

(* FIXME: define and prove these. *)

Definition mvcc_proph (γ : mvcc_names) (p : proph_id) (acs : list action) : iProp Σ.
Admitted.

Lemma wp_ResolveRead γ p acs (tid key : u64) :
  {{{ mvcc_proph γ p acs }}}
    ResolveRead #p #tid #key
  {{{ acs', RET #(); ⌜acs = EvRead tid key :: acs⌝ ∗ mvcc_proph γ p acs' }}}.
Admitted.

Lemma wp_ResolveAbort γ p acs (tid : u64) :
  {{{ mvcc_proph γ p acs }}}
    ResolveAbort #p #tid
  {{{ acs', RET #(); ⌜acs = EvAbort tid :: acs⌝ ∗ mvcc_proph γ p acs' }}}.
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
