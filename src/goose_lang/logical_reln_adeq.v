From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map frac_count big_op.
From Perennial.goose_lang Require Import proofmode notation wpc_proofmode.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy spec_assert language_ctx.
From Perennial.goose_lang Require Import typing typed_translate adequacy refinement.
From Perennial.goose_lang Require Export recovery_adequacy spec_assert refinement_adequacy.
From Perennial.goose_lang Require Import metatheory.
From Perennial.Helpers Require Import Qextra.
From Perennial.Helpers Require List.
From Perennial.goose_lang Require Import logical_reln_defns logical_reln_fund.

Set Default Proof Using "Type".

Section adeq.

Existing Instances spec_ffi_model_field spec_ffi_op_field spec_ext_semantics_field spec_ffi_interp_field
         spec_ffi_interp_adequacy_field.

Context {ext: ffi_syntax}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ffi_semantics ext ffi}.
Context `{interp: !ffi_interp ffi}.
Context `{interp_adeq: !ffi_interp_adequacy}.
Context (impl_ty: ext_types ext).

Context {spec_ext: spec_ffi_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{spec_interp: @spec_ffi_interp spec_ffi}.
Context `{spec_adeq: !spec_ffi_interp_adequacy}.
Context (spec_ty: ext_types (@spec_ffi_op_field spec_ext)).

Notation sstate := (@state (@spec_ffi_op_field spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ffi_op_field spec_ext)).
Notation sval := (@val (@spec_ffi_op_field spec_ext)).
Notation istate := (@state ext).
Notation iexpr := (@expr ext).
Notation ival := (@val ext).
Notation sty := (@ty (@val_tys _ spec_ty)).
Notation SCtx := (@Ctx (@val_tys _ spec_ty)).

Context `{hsT_model: !specTy_model spec_ty}.
Context (spec_trans: sval → ival → Prop).
Context (spec_atomic_transTy : SCtx -> sexpr -> iexpr -> sty -> sexpr -> iexpr -> sty -> Prop).
Context (upd: specTy_update hsT_model).

Existing Instance sty_inv_persistent.

Section pre_assumptions.

Context `{Hhpre: @heapGpreS ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.
Context `{Hcrashpre: crashPreG Σ}.
Context `{Hstypre: !sty_preG (hsT_model := hsT_model) (specTy_update := upd) Σ}.

Definition sty_derived_crash_condition :=
    (λ (hG: heapGS Σ) (hRG: refinement_heapG Σ), ∃ hS,
      ▷ ∀ (hG': heapGS Σ), |={⊤}=>
      ∀ σs,
      (∃ σ0 σ1, ffi_restart (heapG_ffiG) σ1.(world) ∗
      ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ0.(world) (heapG_ffiG (hG := hG')) σ1.(world)) -∗
      ffi_ctx (refinement_spec_ffiG) σs.(world) -∗
      ∃ (σs': sstate) (HCRASH: crash_prim_step (spec_crash_lang) σs σs'),
      ffi_ctx (refinement_spec_ffiG) σs.(world) ∗
      ∀ (hRG': refinement_heapG Σ),
      ffi_crash_rel Σ (refinement_spec_ffiG (hRG := hRG)) σs.(world)
                      (refinement_spec_ffiG (hRG := hRG')) σs'.(world) -∗
      ffi_restart (refinement_spec_ffiG) σs'.(world) -∗
      crash_borrow.pre_borrowN sty_lvl_init -∗
      |={styN}=> ∃ (new: sty_names), sty_init (sty_update Σ hS new))%I.

Lemma sty_inv_to_wpc hG hRG hS es e τ j:
  expr_transTy _ _ _ spec_trans spec_atomic_transTy ∅ es e τ →
  sty_crash_inv_obligation →
  sty_crash_obligation →
  sty_rules_obligation spec_trans →
  sty_atomic_obligation spec_atomic_transTy →
  spec_ctx -∗
  spec_crash_ctx (sty_crash_tok) -∗
  trace_ctx -∗
  sty_init hS -∗
  j ⤇ es -∗
  WPC e @ sty_lvl_init; ⊤ {{ _, True }}{{sty_derived_crash_condition hG hRG ∗ sty_crash_tok}}.
Proof.
  iIntros (Htype Hsty_crash_inv Hsty_crash Hsty_rules Hatomic) "#Hspec #Hspec_crash #Htrace Hinit Hj".
  rewrite /sty_crash_obligation in Hsty_crash.
  iMod (Hsty_crash_inv with "[$] [$] [$]") as "Hinit".
  iAssert (|={⊤}=> WPC e @ sty_lvl_init; ⊤ {{ _, True }}{{sty_inv hS ∗ sty_crash_cond hS ∗ sty_crash_tok}})%I with "[-]" as ">H".
  {
    rewrite /sty_crash_inv_obligation in Hsty_crash_inv.
    iModIntro.
    iPoseProof (sty_fundamental_lemma _ _ _ Hsty_rules Hatomic ∅ _ _ _ Htype) as "H"; eauto.
    iApply (init_cancel_elim with "Hinit").
    iIntros "#Hinv".
      iSpecialize ("H" $! ∅ with "[] [$] [$] [$] []").
      { iPureIntro. apply: fmap_empty. }
      { by rewrite big_sepM_empty. }
      rewrite /has_semTy.
      iSpecialize ("H" $! j id with "[] [Hj]").
      { iPureIntro. apply _. }
      { simpl. by rewrite fmap_empty subst_map_empty. }
      rewrite fmap_empty subst_map_empty.
      iApply wpc_idx_change.
      iApply (wpc_strong_mono _ _ _ _ _ _ _ _ (λ _, True%I) with "[$]"); eauto 10.
  }
  iApply (wpc_strong_mono with "[$]"); eauto.
  iSplit.
  - eauto.
  - iIntros "(?&?&?)".
    iIntros "Hc".
    iApply fupd_level_fupd.
    iMod (fupd_level_mask_subseteq (styN)) as "Hclo"; eauto.
    iMod (Hsty_crash with "[$] [$]") as "H".
    iMod "Hclo".
    iModIntro. iFrame. iExists _. iFrame.
Qed.
End pre_assumptions.

Existing Instances subG_cfgG subG_refinement_heapPreG subG_crashG.
Definition logical_relnΣ := #[styΣ; heapΣ; @cfgΣ spec_lang; refinement_heapΣ; crashΣ].

Lemma sty_adequacy es σs gs e σ g τ initP:
  sty_init_obligation1 upd initP →
  sty_init_obligation2 initP →
  sty_crash_inv_obligation →
  sty_crash_obligation →
  sty_rules_obligation spec_trans →
  sty_atomic_obligation spec_atomic_transTy →
  expr_transTy _ _ _ spec_trans spec_atomic_transTy ∅ es e τ →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  initP σ σs →
  trace_refines e e σ g es es σs gs.
Proof.
  intros Hsty_init1 Hsty_init2 Hsty_crash_inv Hsty_crash Hsty_rules Hatomic Htype Htrace Horacle Hinit.
  eapply @heap_wpc_refinement_adequacy with (spec_ext := spec_ext) (Σ := logical_relnΣ)
           (Φ := λ _ _ _, True%I) (Φc := sty_derived_crash_condition)
           (k := sty_lvl_init) (initP := initP); eauto.
  { apply _. }
  { apply _. }
  { apply _. }
  { apply _. }
  { intros. apply sty_crash_tok_timeless. }
  { intros. rewrite /excl_crash_token. iIntros. iApply (sty_crash_tok_excl with "[$] [$]"). }
  { clear dependent σ σs g gs. rewrite /wpc_init. iIntros (hG hRG σ g σs gs Hinit) "Hffi Hffi_spec".
    rewrite /sty_init_obligation1 in Hsty_init1.
    rewrite /wpc_obligation.
    iIntros "Hborrow Hj #Hspec #Hcrash_spec #Htrace".
    iApply fupd_wpc.
    iPoseProof (Hsty_init1 _ _ _ _  with "[$] [$] [$]") as "H"; first auto.
    iApply (fupd_mask_mono styN); first by set_solver+.
    iMod "H" as (names) "Hinit".
    iModIntro.
    iApply (sty_inv_to_wpc with "[$] [$] [$] [$]"); eauto.
  }
  { clear dependent σ σs.
    rewrite /wpc_post_crash.
    iIntros (??) "H". iDestruct "H" as (hS') "H". iNext.
    iIntros (hG'). iMod ("H" $! hG') as "H". iModIntro.
    iIntros. iSpecialize ("H" with "[$] [$]").
    iDestruct "H" as (σs' Hcrash) "(Hctx&Hrest)".
    iExists σs', Hcrash. iFrame. iIntros (hRG') "Hcrash_rel Hrestart".
    iSpecialize ("Hrest" $! hRG' with "[$] [$]").
    rewrite /wpc_obligation.
    iIntros "Hborrow Hj #Hspec #Hspec_crash #Htrace".
    iApply fupd_wpc.
    iApply (fupd_mask_mono styN); first by set_solver+.
    iMod ("Hrest" with "[$]") as (names) "Hinv".
    iModIntro.
    iApply (sty_inv_to_wpc _ _ (sty_update logical_relnΣ hS' names) with "[$] [$] [$] [$]"); eauto.
  }
  (* BUG: Coq v8.11 requires Grab Existential Variables and not Unshelve to get
  this obligation *)
  Unshelve.
  apply subG_styPreG, _.
Qed.

End adeq.
