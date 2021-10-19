From Perennial.program_proof Require Import grove_prelude.

Record pb_names :=
  {
  commit_gn:gname
  }.

Definition Log := list u8.

Definition log_po (lhs rhs:Log) : Prop :=
  prefix lhs rhs.

Notation "lhs ⪯ rhs" := (log_po lhs rhs)
(at level 20, format "lhs ⪯ rhs") : bi_scope.

Section definitions.

Context `{!gooseGlobalGS Σ}.

Implicit Type γ : pb_names.

Definition config_ptsto γ (cn:u64) (conf:list u64): iProp Σ.
Admitted.

Definition proposal_ptsto γ (cn:u64) (l:Log): iProp Σ.
Admitted.

Definition proposal_lb γ (cn:u64) (l:Log): iProp Σ.
Admitted.

(* Probably not needed *)
Definition proposal_ptsto_ro γ (cn:u64) (l:Log): iProp Σ.
Admitted.

Definition accepted_ptsto γ (cn:u64) (r:u64) (l:Log): iProp Σ.
Admitted.

Definition accepted_lb γ (cn:u64) (r:u64) (l:Log): iProp Σ.
Admitted.

Definition accepted_ptsto_ro γ (cn:u64) (r:u64) (l:Log): iProp Σ.
Admitted.

Definition commit_ptsto γ (l:Log): iProp Σ.
Admitted.

Definition commit_lb γ (l:Log): iProp Σ.
Admitted.

Global Instance proposal_lb_pers γ cn l :
  Persistent (proposal_lb γ cn l).
Admitted.

Global Instance accepted_lb_pers γ cn r l :
  Persistent (accepted_lb γ cn r l).
Admitted.

Global Instance committed_lb_pers γ l :
  Persistent (commit_lb γ l).
Admitted.

Definition accepted_by γ cn l : iProp Σ :=
  ∃ conf, config_ptsto γ cn conf ∗
      ∀ (r:u64), ⌜r ∈ conf⌝ → accepted_lb γ cn r l.

(* oldconfmax *)
Definition φ γ (cn:u64) log : iProp Σ :=
  □(∀ cn_old log_old ,
   ⌜int.Z cn_old < int.Z cn⌝ →
   accepted_by γ cn_old log_old → ⌜log_old ⪯ log⌝).

(* System-wide invariant for primary/backup replication with many replicas with
   configuration changes *)
Definition pb_invariant γ : iProp Σ :=
  ∃ cn_committed l_committed,
  "Hcommit" ∷ commit_ptsto γ l_committed ∗
  "Haccepted" ∷ accepted_by γ cn_committed l_committed ∗ φ γ cn_committed l_committed
.

End definitions.
