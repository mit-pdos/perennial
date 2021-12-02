From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import
     txn.typed_translate txn.twophase_refinement_defs txn.twophase_refinement_proof.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.goose_lang.ffi Require Import jrnl_ffi atomic_refinement.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_adeq spec_assert.

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy jrnl_semantics.
Existing Instances spec_ffi_model_field spec_ffi_op_field spec_ext_semantics_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.

(* This first result proves a refinement theorem showing that the GoTxn scheme of wrapping
   code in Begin/Commit txn wrappers is a refinement of the version where that code is placed in
   atomically blocks *)
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


Section txn_sequential_refinement.
  Context {spec_op: ffi_syntax}.
  Context {spec_ffi: ffi_model}.
  Context {spec_semantics: ffi_semantics spec_op spec_ffi}.

  Notation sexpr := (@expr spec_op).
  Notation sectx_item := (@ectx_item spec_op).
  Notation sval := (@val spec_op).
  Notation sstate := (@state spec_op spec_ffi).
  Notation sffi_state := (@ffi_state spec_ffi).
  Notation sffi_global_state := (@ffi_global_state spec_ffi).
  Notation sgstate := (@global_state spec_ffi).
  Notation iexpr := (@expr jrnl_op).
  Notation iectx_item := (@ectx_item jrnl_op).
  Notation ival := (@val jrnl_op).
  Notation istate := (@state jrnl_op jrnl_model).
  Notation igstate := (@global_state jrnl_model).
  Notation iffi_state := (@ffi_state jrnl_model).
  Notation iffi_global_state := (@ffi_global_state jrnl_model).

  Canonical Structure spec_lang : language :=
    @goose_lang (spec_op) (spec_ffi) (spec_semantics).
  Canonical Structure spec_crash_lang : crash_semantics spec_lang :=
    @goose_crash_lang (spec_op) (spec_ffi) (spec_semantics).
  Notation scfg := (@cfg spec_lang).

  (* op_impl gives a lambda implementing each spec op code into the jrnl interface *)
  Context (op_impl: @ffi_opcode spec_op → ival).
  Context (ffi_abstraction: sffi_state → sffi_global_state →
                            iffi_state → iffi_global_state → Prop).

  Context (wf : sexpr → scfg → Prop).
  Context (wf_closed : ∀ sr sσ sg stp, wf sr (stp, (sσ, sg)) →
                                       metatheory.is_closed_expr [] sr ∧ Forall (metatheory.is_closed_expr []) stp).
  Context (wf_preserved_step : ∀ sr sρ sρ' s,
              wf sr sρ →
              erased_rsteps (CS := spec_crash_lang) sr sρ sρ' s →
              wf sr sρ').

  Context (op_impl_succ_ok: ∀ o, op_simulated_succ (impl_semantics := jrnl_semantics)
                                                   op_impl ffi_abstraction wf o (op_impl o)).
  Context (op_impl_abort_ok: ∀ o, op_simulated_abort (impl_semantics := jrnl_semantics)
                                                     op_impl ffi_abstraction o (op_impl o)).
  Context (op_impl_safe_ok: ∀ o, op_safe (impl_semantics := jrnl_semantics) op_impl ffi_abstraction o (op_impl o)).

  Context (crash_ok: crash_simulated ffi_abstraction).

  Theorem txn_sequential_refinement se ie e dσ sσ sg iσ ig k :
    (* se compiles to ie by replacing ExternalOps with op_impl wrapped by Atomically () *)
    expr_impl op_impl se ie →
    (* ie 'compiles' to e when plugging in journal implementations / Begin/Commit for Atomically () *)
    (∃ τ, typed_translate.expr_transTy _ _ _ jrnl_trans jrnl_atomic_transTy ∅ ie e τ) →
    abstraction ffi_abstraction sσ sg iσ ig →
    dσ.(trace) = iσ.(trace) →
    dσ.(oracle) = iσ.(oracle) →
    twophase_initP k dσ iσ →
    wf se ([se], (sσ, sg)) →
    fo_rsteps se ([se], (sσ, sg)) →
    refinement.trace_refines e e dσ ig se se sσ sg.
  Proof using wf_closed op_impl_succ_ok op_impl_abort_ok wf_preserved_step crash_ok op_impl_safe_ok.
    intros Himpl Htype Habstraction Htrace Horacle Hinit Hwf Hfo.
    intros Hsafe.
    destruct Htype as (τ&Htype).
    edestruct (@atomic_concurrent_refinement); try eassumption.
    edestruct (@jrnl_refinement); try eassumption.
    intuition eauto.
  Qed.
  (*
  Print Assumptions txn_sequential_refinement.
   *)
End txn_sequential_refinement.
