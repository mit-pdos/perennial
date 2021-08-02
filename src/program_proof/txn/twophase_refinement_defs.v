From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import txn.typed_translate txn.wrapper_proof.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_adeq spec_assert crash_borrow.
From Perennial.base_logic Require Import ghost_var.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require jrnl.sep_jrnl_invariant.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof obj.obj_proof.
From Perennial.program_proof Require Import jrnl.sep_jrnl_proof.
From Perennial.program_proof Require Import txn.txn_proof.
From Perennial.program_proof Require Import alloc.alloc_proof.

From Goose Require github_com.mit_pdos.go_journal.obj.

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy.

Section refinement_defs.
Context `{!heapGS Σ}.
Context `{!refinement_heapG Σ}.
Context (JRNL_SIZE: nat).

Existing Instance jrnlG0.

Existing Instances spec_ffi_model_field spec_ffi_op_field spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Notation sstate := (@state (@spec_ffi_op_field jrnl_spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ffi_op_field jrnl_spec_ext)).
Notation sval := (@val (@spec_ffi_op_field jrnl_spec_ext)).

Notation jrnl_nat_K :=
(leibnizO (nat * ((@spec_lang jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics).(language.expr)
                           → (@spec_lang jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics).(language.expr)))).

Class twophaseG (Σ: gFunctors) :=
  { twophase_stagedG :> stagedG Σ;
    twophase_lockmapG :> lockmapG Σ;
    twophase_jrnlG :> sep_jrnl_invariant.jrnlG Σ;
    twophase_nat_ctx :> ghost_varG Σ (nat * (spec_lang.(language.expr) → spec_lang.(language.expr)))%type;
  }.

Definition twophase_names := unit.
Definition twophase_get_names (Σ: gFunctors) (hG: twophaseG Σ) := tt.
Definition twophase_update (Σ: gFunctors) (hG: twophaseG Σ) (n: twophase_names) := hG.


Definition LVL_INIT : nat := 1 + JRNL_SIZE.
Definition LVL_INV : nat := 125.
Definition LVL_OPS : nat := 100.

Definition twophase_crash_cond_full
           {Σ: gFunctors} {hG: heapGS Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ}  γ dinit logm mt : iProp Σ
  := ("%Hvalids" ∷ ⌜ map_Forall (mapsto_valid γ) mt ⌝ ∗
      "Htxn_durable" ∷ is_txn_durable γ dinit logm ∗
      "#Hdom" ∷ jrnl_dom (dom _ mt) ∗
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(jrnl_txn_names).(txn_kinds) ∗
      "Hmapstos" ∷ ([∗ map] a ↦ obj ∈ mt,
      "Hdurable_mapsto" ∷ durable_mapsto_own γ a obj ∗
      "Hjrnl_mapsto" ∷ jrnl_mapsto_own a obj) ∗
      "%Hdomsize" ∷ ⌜ size mt = JRNL_SIZE ⌝).

Definition twophase_crash_cond_partial
           {Σ: gFunctors} {hG: heapGS Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ}  γ dinit logm mt : iProp Σ
  := ("%Hvalids" ∷ ⌜ map_Forall (mapsto_valid γ) mt ⌝ ∗
      "Htxn_durable" ∷ is_txn_durable γ dinit logm ∗
      "#Hdom" ∷ jrnl_dom (dom _ mt) ∗
      "#Hjrnl_kinds_lb" ∷ jrnl_kinds γ.(jrnl_txn_names).(txn_kinds) ∗
      "Hmapstos" ∷ ([∗ map] a ↦ obj ∈ mt,
      "Hdurable_mapsto" ∷ durable_mapsto_own γ a obj ∗
      "Hjrnl_mapsto" ∷ jrnl_mapsto a 1 (bufObj_to_obj obj)) ∗
      "%Hdomsize" ∷ ⌜ size mt = JRNL_SIZE ⌝).

Definition twophase_crash_cond
           {Σ: gFunctors} {hG: heapGS Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ} : iProp Σ
  := ∃ γ dinit logm mt, twophase_crash_cond_partial γ dinit logm mt.

Definition twophase_na_crash_inv
           {Σ: gFunctors} {hG: heapGS Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ} : iProp Σ
  := crash_borrow (∃ γ dinit logm mt',
                                  ([∗ map] _ ↦ _ ∈ mt', pre_borrow) ∗
                                  twophase_crash_cond_full γ dinit logm mt')%I
                             (∃ γ dinit logm mt',
                                  twophase_crash_cond_full γ dinit logm mt')%I.

(* don't use [id] to avoid universe trouble *)
Definition expr_id (e: spec_lang.(language.expr)) : spec_lang.(language.expr) := e.

Definition twophase_inv_inner {Σ: gFunctors} {hG: heapGS Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ} γ : iProp Σ
  := (twophase_na_crash_inv ∗ jrnl_closed_frag ∗ ghost_var γ 1 (0, expr_id)) ∨ jrnl_open.

Definition twophaseInitN := nroot.@"init".

Definition twophase_inv {Σ: gFunctors} {hG: heapGS Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ} : iProp Σ
  := ∃ γ, inv twophaseInitN (twophase_inv_inner γ) ∗ spec_crash_ctx (jrnl_crash_ctx).

Definition twophase_crash_tok {Σ: gFunctors} {hG: heapGS Σ} {rG: refinement_heapG Σ} : iProp Σ
  := jrnl_crash_ctx.

Definition twophase_init {Σ: gFunctors} {hG: heapGS Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ} : iProp Σ
  := (∃ γ dinit logm mt, twophase_crash_cond_full γ dinit logm mt ∗
          auth_map.map_ctx jrnlG_crash_toks_name 1 ((λ _, tt) <$> (bufObj_to_obj <$> mt)) ∗
          jrnl_full_crash_tok ∗ jrnl_closed_frag ∗
          pre_borrow ∗
          ([∗ map] _ ↦ _ ∈ mt, pre_borrow)).

Definition twophaseN : coPset := (∅ : coPset).

Definition twophase_val_interp {Σ: gFunctors} {hG: heapGS Σ} {rG: refinement_heapG Σ} {aG : twophaseG Σ}
           (ty: @ext_tys (@val_tys _ jrnl_ty)) : val_semTy :=
  λ vspec vimpl,
  match ty with
  | JrnlT => (∃ (l: loc) γ γ' dinit objs_dom,
                 ⌜ vimpl = #l ⌝ ∗ ⌜ vspec = #true ⌝ ∗ is_twophase_pre l γ γ' dinit objs_dom ∗ jrnl_open)%I
  | AllocT => (∃ (ls li: loc) (max : u64),
                 ⌜ vimpl = #li ⌝ ∗ ⌜ vspec = #ls ⌝ ∗ ⌜ (0 < int.Z max)%Z ⌝ ∗ is_alloc max li ∗ jrnl_alloc ls max)%I
  end.

Instance twophaseTy_model : specTy_model jrnl_ty.
Proof using JRNL_SIZE.
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
 - intros.
   iDestruct 1 as (m) "(?&?&?)".
   iDestruct 1 as (m') "(?&?&?)".
   iApply (jrnl_full_crash_tok_excl with "[$] [$]").
 - rewrite /sN/twophaseN. apply disjoint_empty_r.
 - iIntros (? hG hRG hG' hS τ vs v).
   induction τ; eauto => //=; apply _.
 - iIntros (? hG hRG hG' hS τ vs v).
   destruct τ.
   * iDestruct 1 as (l γ γ' dinit objs_dom -> ->) "(H1&H2)".
     iPureIntro. split; eauto.
   * iDestruct 1 as (??? -> ->) "H"; eauto.
Defined.
(* XXX: some of the fields should be opaque/abstract here, because they're enormous proof terms.
  perhaps specTy_model should be split into two typeclasses? *)

Existing Instances subG_stagedG.

Definition twophaseΣ := #[stagedΣ; lockmapΣ; sep_jrnl_invariant.jrnlΣ;
                         ghost_varΣ (nat * (spec_lang.(language.expr) → spec_lang.(language.expr)))].

Instance subG_twophaseG: ∀ Σ, subG twophaseΣ Σ → twophaseG Σ.
Proof. solve_inG. Qed.
Definition twophase_update_pre (Σ: gFunctors) (hG: twophaseG Σ) (n: twophase_names) : twophaseG Σ := hG.

Program Instance twophaseTy_update_model : specTy_update twophaseTy_model :=
  {| sty_preG := twophaseG;
            styΣ := twophaseΣ;
            subG_styPreG := subG_twophaseG;
            sty_update_pre := @twophase_update_pre |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.

End refinement_defs.
