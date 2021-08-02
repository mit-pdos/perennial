From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy dist_weakestpre.
From Perennial.goose_lang Require Import crash_modality typing adequacy lang wpr_lifting.
Set Default Proof Using "Type".

Section wpd_definitions.

Context `{ffi_sem: ffi_semantics}.
Context {ext_tys: ext_types ext}.
Context `{interp: !ffi_interp ffi}.
Context `{@ffi_interp_adequacy ffi interp ext ffi_sem}.

Class heap_globalG Σ := {
  heap_globalG_preG :> heapGpreS Σ;
  heap_globalG_names : ffi_global_names;
  heap_globalG_credit_names : cr_names;
  heap_globalG_inv_names : inv_names;
  (*
  heap_globalG_invG :> invGS Σ;
   *)
}.

Global Instance heap_globalG_invG {Σ} {hgG: heap_globalG Σ} : invGS Σ :=
  inv_update_pre (heap_preG_iris) (heap_globalG_inv_names).

Global Instance heap_globalG_creditGS {Σ} {hgG: heap_globalG Σ} : creditGS Σ :=
  creditGS_update_pre _ _ (heap_globalG_credit_names).

Program Global Instance heapG_groveG `{!heap_globalG Σ} : groveG goose_lang goose_crash_lang Σ :=
{
  grove_global_state_interp := λ g ns mj D κs,
    (ffi_pre_global_ctx Σ (heap_preG_ffi) (heap_globalG_names) g ∗
     @crash_borrow_ginv _ (heap_globalG_invG) _ ∗
     cred_interp ns ∗
     ⌜(/ 2 < mj ≤ 1) ⌝%Qp ∗
     pinv_tok mj D)%I;
  grove_num_laters_per_step := (λ n, 3 ^ (n + 1))%nat;
  grove_step_count_next := (λ n, 10 * (n + 1))%nat;
  grove_invG := heap_globalG_invG
}.

Definition hgG_extend_local_names {Σ} (hgG : heap_globalG Σ) (names : heap_local_names) : heap_names :=
  {| heap_heap_names := heap_local_heap_names names;
     heap_ffi_local_names := heap_local_ffi_local_names names;
     heap_trace_names := heap_local_trace_names names;
     heap_ffi_global_names := heap_globalG_names;
     heap_credit_names := heap_globalG_credit_names;
 |}.

Definition heap_globalG_heapG {Σ} (hgG: heap_globalG Σ) (Hc: crashG Σ) (names: heap_local_names) : heapGS Σ :=
  heap_update_pre Σ (heap_globalG_preG) (heap_globalG_invG)
                  {| crash_inG := (@crash_inPreG _ heap_preG_crash); crash_name := @crash_name _ Hc |}
                  (hgG_extend_local_names hgG names).

Definition wpd `{hgG: !heap_globalG Σ} (k: nat) (E: coPset)
           (cts: list (crashG Σ * heap_local_names)) (ers: list (expr * expr)) :=
  ([∗ list] i↦ct;er ∈ cts;ers, ∃ Φ Φrx Φinv,
    let hG := heap_globalG_heapG hgG (fst ct) (snd ct) in
    wpr NotStuck k E (fst er) (snd er) Φ Φinv Φrx)%I.

End wpd_definitions.
