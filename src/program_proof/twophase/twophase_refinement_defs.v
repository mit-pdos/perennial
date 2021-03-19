From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import twophase.typed_translate twophase.wrapper_proof.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_adeq spec_assert.
From Perennial.base_logic Require Import ghost_var.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require buftxn.sep_buftxn_invariant.

From Goose Require github_com.mit_pdos.goose_nfsd.txn.

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy.

Class twophaseInit_params :=
  {
    SIZE : nat;
    SIZE_nonzero : 0 < SIZE;
    SIZE_bounds: int.nat SIZE = SIZE
  }.

Section refinement_defs.
Context `{!heapG Σ}.
Context `{!refinement_heapG Σ}.

Existing Instance jrnlG0.
Context {PARAMS: twophaseInit_params}.

Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Notation sstate := (@state (@spec_ext_op_field jrnl_spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ext_op_field jrnl_spec_ext)).
Notation sval := (@val (@spec_ext_op_field jrnl_spec_ext)).

Class twophaseG (Σ: gFunctors) :=
  { twophase_stagedG :> stagedG Σ;
    twophase_lockmapG :> lockmapG Σ;
    twophase_buftxnG :> sep_buftxn_invariant.buftxnG Σ
  }.

Definition twophase_names := unit.
Definition twophase_get_names (Σ: gFunctors) (hG: twophaseG Σ) := tt.
Definition twophase_update (Σ: gFunctors) (hG: twophaseG Σ) (n: twophase_names) := hG.

Definition LVL_INIT : nat := 100.
Definition LVL_INV : nat := 75.
Definition LVL_OPS : nat := 50.

Definition twophase_inv {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ} : iProp Σ
  := True%I.
Definition twophase_init {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ} : iProp Σ
  := True%I.
Definition twophase_crash_cond {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ} : iProp Σ
  := True.
Definition twophase_crash_tok {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} : iProp Σ
  := False.
Definition twophaseN : coPset := (∅ : coPset).
Definition twophase_val_interp {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ}
           (ty: @ext_tys (@val_tys _ jrnl_ty)) : val_semTy :=
  λ vspec vimpl, False%I.

Instance twophaseTy_model : specTy_model jrnl_ty.
Proof using PARAMS.
 refine
  {| styG := twophaseG;
     sty_names := twophase_names;
     sty_get_names := twophase_get_names;
     sty_update := twophase_update;
     sty_inv := @twophase_inv;
     sty_init := @twophase_init;
     sty_crash_cond := @twophase_crash_cond;
     sty_crash_tok := @twophase_crash_tok;
     styN := twophaseN;
     sty_lvl_init := LVL_INIT;
     sty_lvl_ops := LVL_OPS;
     sty_val_interp := @twophase_val_interp |}.
 - intros ? [] [] => //=.
 - intros ? [] => //=.
 - intros ?? [] [] => //=.
 - auto.
 - rewrite /sN/twophaseN. apply disjoint_empty_r.
 - auto.
Defined.
(* XXX: some of the fields should be opaque/abstract here, because they're enormous proof terms.
  perhaps specTy_model should be split into two typeclasses? *)

Existing Instances subG_stagedG.

Definition twophaseΣ := #[stagedΣ; lockmapΣ; sep_buftxn_invariant.buftxnΣ].

Instance subG_twophaseG: ∀ Σ, subG twophaseΣ Σ → twophaseG Σ.
Proof. solve_inG. Qed.
Parameter init_jrnl_map : jrnl_map.
Definition twophase_initP (σimpl: @state disk_op disk_model) (σspec : @state jrnl_op jrnl_model) : Prop :=
  (null_non_alloc σspec.(heap)) ∧
  (σimpl.(world) = init_disk ∅ SIZE) ∧
  (σspec.(world) = Closed init_jrnl_map).
Definition twophase_update_pre (Σ: gFunctors) (hG: twophaseG Σ) (n: twophase_names) : twophaseG Σ := hG.

Program Instance twophaseTy_update_model : specTy_update twophaseTy_model :=
  {| sty_preG := twophaseG;
            styΣ := twophaseΣ;
            subG_styPreG := subG_twophaseG;
            sty_update_pre := @twophase_update_pre |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.

End refinement_defs.
