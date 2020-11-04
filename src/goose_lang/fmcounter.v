(** Crash instances for fmcounter. *)
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import mnat.
From Perennial.goose_lang Require Import crash_modality lifting.

Section instances.
Context `{ffi_semantics: ext_semantics}.
Context `{!ffi_interp ffi}.
Context `{!mnatG Σ, !heapG Σ}.

Global Instance mnat_own_lb_durable γ n:
  IntoCrash (mnat_own_lb γ n) (λ _, mnat_own_lb γ n).
Proof. rewrite /IntoCrash. iApply post_crash_nodep. Qed.

Global Instance mnat_own_auth_durable γ q n:
  IntoCrash (mnat_own_auth γ q n) (λ _, mnat_own_auth γ q n).
Proof. rewrite /IntoCrash. iApply post_crash_nodep. Qed.
End instances.
