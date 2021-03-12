(** Crash instances for mono_nat. *)
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic.lib Require Export mono_nat.
From Perennial.goose_lang Require Import crash_modality lifting.

Set Default Proof Using "Type".

Section instances.
Context `{ffi_semantics: ext_semantics}.
Context `{!ffi_interp ffi}.
Context `{!mono_natG Σ, !heapG Σ}.

Global Instance mono_nat_lb_own_durable γ n:
  IntoCrash (mono_nat_lb_own γ n) (λ _, mono_nat_lb_own γ n).
Proof. rewrite /IntoCrash. iApply post_crash_nodep. Qed.

Global Instance mono_nat_auth_own_durable γ q n:
  IntoCrash (mono_nat_auth_own γ q n) (λ _, mono_nat_auth_own γ q n).
Proof. rewrite /IntoCrash. iApply post_crash_nodep. Qed.
End instances.
