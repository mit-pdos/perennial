From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import twophase.typed_translate twophase.wrapper_proof twophase.twophase_refinement_defs.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_adeq spec_assert.
From Perennial.program_logic Require Import ghost_var.

From Goose Require github_com.mit_pdos.goose_nfsd.txn.

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy.

Section refinement.
Context {PARAMS : jrnlInit_params}.

Notation jrnl_nat_K :=
(leibnizO (nat * ((@spec_lang jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics).(language.expr)
                           → (@spec_lang jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics).(language.expr)))).

Lemma jrnl_init_obligation1: sty_init_obligation1 jrnlTy_update_model jrnl_initP.
Proof.
  rewrite /sty_init_obligation1//=.
  iIntros (? hG hRG hJrnl σs σi Hinit) "Hdisk".
  rewrite /jrnl_start /jrnl_init/jrnl_init.
  inversion Hinit as [Hnn [Heqi Heqs]]. rewrite Heqs Heqi.
  iIntros "(Hclosed_frag&Hjrnl_frag)".
  eauto.
Qed.

Lemma jrnl_init_obligation2: sty_init_obligation2 jrnl_initP.
Proof.
  intros ?? (?&?&?). rewrite //=. split_and!; eauto. eexists; split; eauto.
  admit.
Admitted.

Lemma jrnl_rules_obligation:
  @sty_rules_obligation _ _ disk_semantics _ _ _ _ _ _ jrnlTy_model jrnl_trans.
Proof.
  intros vs0 vs v0 v0' t1 t2 Htype0 Htrans.
  inversion Htype0 as [op Heq]; subst.
  - iIntros (????) "#Hinv #Hspec #Hval".
    iIntros (j K Hctx) "Hj".
    admit.
Admitted.

Lemma jrnl_crash_inv_obligation:
  @sty_crash_inv_obligation _ _ disk_semantics _ _ _ _ _ _ jrnlTy_model.
Proof.
  rewrite /sty_crash_inv_obligation//=.
  iIntros (? hG hRG hJrnl e Φ) "Hinit Hspec Hwand".
  rewrite /jrnl_inv/jrnl_init/jrnl_inv.
Admitted.

Lemma jrnl_crash_obligation:
  @sty_crash_obligation _ _ disk_semantics _ _ _ _ _ _ jrnlTy_model.
Proof.
  rewrite /sty_crash_obligation//=.
  iIntros (? hG hRG hJrnl) "Hinv Hcrash_cond".
Admitted.

Lemma jrnl_atomic_obligation:
  @sty_atomic_obligation _ _ disk_semantics _ _ _ _ _ _ jrnlTy_model jrnl_atomic_transTy.
Proof.
  rewrite /sty_atomic_obligation//=.
  iIntros (? hG hRG hJrnl el1 el2 tl e1 e2 t Γsubst Htrans) "Hinv Hspec Htrace HΓ HhasTy".
Admitted.

Existing Instances jrnl_semantics.
Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.
(* XXX: might need to change typed_translate / refinement to use the spec_ wrappers around type classes *)

Lemma jrnl_refinement (es: @expr jrnl_op) σs e σ (τ: @ty jrnl_ty.(@val_tys jrnl_op)):
  typed_translate.expr_transTy _ _ _ jrnl_trans jrnl_atomic_transTy ∅ es e τ →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  jrnl_initP σ σs →
  refinement.trace_refines e e σ es es σs.
Proof.
  intros. intros ?.
  efeed pose proof sty_adequacy; eauto using jrnl_init_obligation1, jrnl_init_obligation2,
                                 jrnl_crash_inv_obligation, jrnl_crash_obligation,
                                 jrnl_rules_obligation, jrnl_atomic_obligation.
Qed.
End refinement.
