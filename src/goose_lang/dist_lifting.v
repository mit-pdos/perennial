From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy dist_weakestpre.
From Perennial.goose_lang Require Import crash_modality typing adequacy lang recovery_lifting.
Set Default Proof Using "Type".

Section wpd_definitions.

Context `{ffi_sem: ffi_semantics}.
Context {ext_tys: ext_types ext}.
Context `{interp: !ffi_interp ffi}.
Context `{@ffi_interp_adequacy ffi interp ext ffi_sem}.

(** Global ghost state for distributed GooseLang
(parameterized by whatever the FFI needs) *)
Class dist_heapGS Σ := {
  dist_heapGpreS :> heapGpreS Σ;
  dist_heapGS_names : ffi_global_names;
  dist_heapGS_credit_names : cr_names;
  dist_heapGS_invG :> invGS Σ;
}.

Global Instance dist_heapGS_invGS {Σ} {hgG: dist_heapGS Σ} : invGS Σ :=
  inv_update_pre (heap_preG_iris) (dist_heapGS_inv_names).

Global Instance dist_heapGS_creditGS {Σ} {hgG: dist_heapGS Σ} : creditGS Σ :=
  creditGS_update_pre _ _ (dist_heapGS_credit_names).

Program Global Instance heapGS_perennialG `{!dist_heapGS Σ} : perennialG goose_lang goose_crash_lang heap_local_namesO Σ :=
{
  perennial_irisGS := heapGS_irisGS;
  perennial_generationGS := λ Hcrash hnames,
                     @heapGS_generationGS _ _ _ _ _ (heap_update_pre _ _ _ Hcrash (@pbundleT _ _ hnames));
  perennial_crashGS := λ _ _, eq_refl;
}.

{
  grove_global_state_interp := λ g ns mj D κs,
    (ffi_pre_global_ctx Σ (heap_preG_ffi) (dist_heapGS_names) g ∗
     @crash_borrow_ginv _ (dist_heapGS_invGS) _ ∗
     cred_interp ns ∗
     ⌜(/ 2 < mj ≤ 1) ⌝%Qp ∗
     pinv_tok mj D)%I;
  grove_num_laters_per_step := (λ n, 3 ^ (n + 1))%nat;
  grove_step_count_next := (λ n, 10 * (n + 1))%nat;
  grove_invG := dist_heapGS_invGS
}.

Definition dhG_extend_local_names {Σ} (dhG : dist_heapGS Σ) (names : heap_local_names) : heap_names :=
  {| heap_heap_names := heap_local_heap_names names;
     heap_ffi_local_names := heap_local_ffi_local_names names;
     heap_trace_names := heap_local_trace_names names;
     heap_ffi_global_names := dist_heapGS_names;
     heap_credit_names := dist_heapGS_credit_names;
 |}.

(* Not an instance! *)
Definition dist_heapGS_heapGS {Σ} (hgG: dist_heapGS Σ) (Hc: crashGS Σ) (names: heap_local_names) : heapGS Σ :=
  heap_update_pre Σ (dist_heapGpreS) (dist_heapGS_invGS)
                  {| crash_inG := (@crash_inPreG _ heap_preG_crash); crash_name := @crash_name _ Hc |}
                  (dhG_extend_local_names hgG names).

Definition wpd `{hgG: !dist_heapGS Σ} (k: nat) (E: coPset)
           (cts: list (crashGS Σ * heap_local_names)) (ers: list (expr * expr)) :=
  ([∗ list] i↦ct;er ∈ cts;ers, ∃ Φ Φrx Φinv,
    let hG := dist_heapGS_heapGS hgG (fst ct) (snd ct) in
    wpr NotStuck k E (fst er) (snd er) Φ Φinv Φrx)%I.

End wpd_definitions.
