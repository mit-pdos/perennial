From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import
     txn.typed_translate txn.twophase_refinement_defs txn.twophase_refinement_proof.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_adeq spec_assert.

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy jrnl_semantics.
Existing Instances spec_ffi_model_field spec_ffi_op_field spec_ext_semantics_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.

Lemma jrnl_refinement (es: @expr jrnl_op) σs gs e σ g (τ: @ty jrnl_ty.(@val_tys jrnl_op)) k:
  typed_translate.expr_transTy _ _ _ jrnl_trans jrnl_atomic_transTy ∅ es e τ →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  twophase_initP k σ σs →
  refinement.trace_refines e e σ g es es σs gs.
Proof.
  intros. intros ?.
  efeed pose proof sty_adequacy; eauto using jrnl_init_obligation1, jrnl_init_obligation2,
                                 jrnl_crash_inv_obligation, jrnl_crash_obligation,
                                 jrnl_rules_obligation, jrnl_atomic_obligation.
Qed.
