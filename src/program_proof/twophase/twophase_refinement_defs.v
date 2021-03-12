From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import twophase.typed_translate twophase.wrapper_proof.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_adeq spec_assert.
From Perennial.base_logic Require Import ghost_var.

From Goose Require github_com.mit_pdos.goose_nfsd.txn.

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy.

Class jrnlInit_params :=
  {
    SIZE : nat;
    SIZE_nonzero : 0 < SIZE;
    SIZE_bounds: int.nat SIZE = SIZE
  }.

Section refinement_defs.
Context `{!heapG Σ}.
Context `{!refinement_heapG Σ}.
Context `{stagedG Σ}.

Existing Instance jrnlG0.
Context {PARAMS: jrnlInit_params}.

Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Notation sstate := (@state (@spec_ext_op_field jrnl_spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ext_op_field jrnl_spec_ext)).
Notation sval := (@val (@spec_ext_op_field jrnl_spec_ext)).

Class jrnlG (Σ: gFunctors) :=
  { jrnl_stagedG :> stagedG Σ; }.

Definition jrnl_names := unit.
Definition jrnl_get_names (Σ: gFunctors) (hG: jrnlG Σ) := tt.
Definition jrnl_update (Σ: gFunctors) (hG: jrnlG Σ) (n: jrnl_names) := hG.

Definition LVL_INIT : nat := 100.
Definition LVL_INV : nat := 75.
Definition LVL_OPS : nat := 50.
Existing Instance jrnlG0.

Definition jrnl_inv {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {aG : jrnlG Σ} : iProp Σ
  := True%I.
Definition jrnl_init {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {aG : jrnlG Σ} : iProp Σ
  := True%I.
Definition jrnl_crash_cond {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {aG : jrnlG Σ} : iProp Σ
  := True.
Definition jrnl_crash_tok {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} : iProp Σ
  := False.
Definition jrnlN : coPset := (∅ : coPset).
Definition jrnl_val_interp {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {aG : jrnlG Σ}
           (ty: @ext_tys (@val_tys _ jrnl_ty)) : val_semTy :=
  λ vspec vimpl, False%I.

Instance jrnlTy_model : specTy_model jrnl_ty.
Proof using PARAMS.
 refine
  {| styG := jrnlG;
     sty_names := jrnl_names;
     sty_get_names := jrnl_get_names;
     sty_update := jrnl_update;
     sty_inv := @jrnl_inv;
     sty_init := @jrnl_init;
     sty_crash_cond := @jrnl_crash_cond;
     sty_crash_tok := @jrnl_crash_tok;
     styN := jrnlN;
     sty_lvl_init := LVL_INIT;
     sty_lvl_ops := LVL_OPS;
     sty_val_interp := @jrnl_val_interp |}.
 - intros ? [] [] => //=.
 - intros ? [] => //=.
 - intros ?? [] [] => //=.
 - auto.
 - rewrite /sN/jrnlN. apply disjoint_empty_r.
 - auto.
Defined.
(* XXX: some of the fields should be opaque/abstract here, because they're enormous proof terms.
  perhaps specTy_model should be split into two typeclasses? *)

Existing Instances subG_stagedG.

Definition jrnlΣ := #[stagedΣ].

Instance subG_jrnlPreG: ∀ Σ, subG jrnlΣ Σ → jrnlG Σ.
Proof. solve_inG. Qed.
Parameter init_jrnl_map : jrnl_map.
Definition jrnl_initP (σimpl: @state disk_op disk_model) (σspec : @state jrnl_op jrnl_model) : Prop :=
  (null_non_alloc σspec.(heap)) ∧
  (σimpl.(world) = init_disk ∅ SIZE) ∧
  (σspec.(world) = Closed init_jrnl_map).
Definition jrnl_update_pre (Σ: gFunctors) (hG: jrnlG Σ) (n: jrnl_names) : jrnlG Σ := hG.

Program Instance jrnlTy_update_model : specTy_update jrnlTy_model :=
  {| sty_preG := jrnlG;
            styΣ := jrnlΣ;
            subG_styPreG := subG_jrnlPreG;
            sty_update_pre := @jrnl_update_pre |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.

End refinement_defs.
