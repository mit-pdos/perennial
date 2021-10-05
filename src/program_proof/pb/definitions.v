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

(* System-wide invariant for primary/backup replication with many replicas with
   configuration changes *)
Definition pb_invariant : iProp Σ :=
  ∃ cn l,
  "Hconfig" ∷ (∀ cn' conf, ⌜cn' < cn⌝ → config(cn)↦□ conf -∗ ∃ r l, ⌜r ∈ conf⌝ ∗
               accepted(r,cn)↦□ l ∗ proposal(cn)≥ l
              ) ∗
  "Hcommit" ∷ commit↦ l ∗
  "Haccepted" ∷ (∃ cn' conf, config(cn')↦□ conf ∗ (∀ r, ⌜r ∈ conf⌝ → accepted(r,cn')≥ l))
.

End definitions.
