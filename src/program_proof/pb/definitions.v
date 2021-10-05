From Perennial.program_proof Require Import grove_prelude.


Section definitions.
Record pb_names :=
  {
  commit_gn:gname
  }.

Context `{!gooseGlobalGS Σ}.

Implicit Type γ : pb_names.

Definition config_ptsto γ (cn:u64) (conf:list u64): iProp Σ.
Admitted.

Definition Log := list u8.

Definition accepted_ptsto γ (cn:u64) (r:u64) (l:Log): iProp Σ.
Admitted.

Definition accepted_lb γ (cn:u64) (r:u64) (l:Log): iProp Σ.
Admitted.

Definition accepted_ptsto_ro γ (cn:u64) (r:u64) (l:Log): iProp Σ.
Admitted.

Definition commit_ptsto γ (l:Log): iProp Σ.
Admitted.

Definition degen_ptsto γ (cn:u64): iProp Σ.
Admitted.

Definition nondegen_witness γ (cn:u64): iProp Σ.
Admitted.

Context {γ}.

Notation "'config(' cn ')↦□' conf" := (config_ptsto γ cn conf)
(at level 20, format "config( cn )↦□ conf") : bi_scope.

Notation "'accepted(' r ',' cn ')↦□' l" := (accepted_ptsto_ro γ cn r l)
(at level 20, format "accepted( r , cn )↦□ l") : bi_scope.

Notation "'accepted(' r ',' cn ')≥' l" := (accepted_lb γ cn r l)
(at level 20, format "accepted( r , cn )≥ l") : bi_scope.

Notation "'proposal(' cn ')≥' l" := (accepted_lb γ cn 0 l)
(at level 20, format "proposal( cn )≥ l") : bi_scope.

Notation "'commit↦' l" := (commit_ptsto γ l)
(at level 20, format "commit↦ l") : bi_scope.

Notation "'degen(' cn ')'" := (degen_ptsto γ cn)
(at level 20, format "degen( cn )") : bi_scope.

Notation "'nondegen(' cn ')'" := (nondegen_witness γ cn)
(at level 20, format "nondegen( cn )") : bi_scope.

(* System-wide invariant for primary/backup replication with many replicas with
   configuration changes *)
Definition pb_invariant : iProp Σ :=
  ∃ cn_latest l_committed,
  "Hconfig" ∷ (∀ cn' conf, ⌜cn' < cn_latest⌝ → config(cn')↦□ conf -∗ ∃ r l, ⌜r ∈ conf⌝ ∗
               accepted(r,cn')↦□ l ∗ proposal(cn_latest)≥ l
              ) ∗
  "Hcommit" ∷ commit↦ l_committed ∗
  "Hprop" ∷ proposal(cn_latest)≥ l_committed ∗
  "Haccepted" ∷ (
    degen(cn_latest) ∗ ∃ cn' conf, config(cn')↦□ conf ∗ (∀ r, ⌜r ∈ conf⌝ → accepted(r,cn')≥ l_committed)
      ∨
    nondegen(cn_latest) ∗ ∃ conf, config(cn_latest)↦□ conf ∗ (∀ r, ⌜r ∈ conf⌝ → accepted(r,cn_latest)≥ l_committed)
  )
.

(*
  Lemma 1.
  Primary wants to commit something after getting accept(-,cn)≥ l_with_op from all replicas.
  It opens pb_invariant.
  if l_with_op > l_committed:
    updates commit↦ l_committed.
    To prove "Hprop":
      if cn == cn_latest:
        produce proposal(cn_latest)≥ l_with_op via one of the
        acceptances/produce it by virtue of us being the primary
      else:
        we know that cn < cn_latest
        We can apply Hconfig, and know that one of the acceptances we have in
        hand is smaller than an l that shows up in Hconfig, which gives us the
        proposal(cn)≥ l
  else:
    We know that l_with_op ≤ l_committed, because of the proposal(cn)≥
    l_committed and proposal(cn)≥ l_with_op, so we can extract a commit_lb
    witness.

  Lemma 2.
  Backup becomes primary after config change.
  Open pb_invariant. Increment cn_latest by VersionedPut.
  Need to prove "Hprop". How?
  Need to know that backup's accepted log is at least as big as the logically committed log.
  If we

  Degenerate "Haccepted": ∃ cn', blah blah. No new nodes can be added.
  Nondegenerate "Haccepted": in cn_latest, all replicas have accepted l.
  "HacceptedNondegen" ∷ config(cn_latest)↦□ conf ∗ (∀ r, ⌜r ∈ conf⌝ → accepted(r, cn_latest)≥ l)
  Then,


  Lemma 3.
  Primary wants to add a new node to the system.
  It opens invariant.
  Increments cn_latest by doing a VersionedPut on the configuration service.
  To prove "Hprop":
    knows that it is the primary the previous configuration.
    ???
  To prove "Hconfig":
    ???
 *)

End definitions.
