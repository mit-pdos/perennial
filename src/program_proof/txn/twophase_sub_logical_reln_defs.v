From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.program_logic Require Export weakestpre.
From Perennial.algebra Require Import proph_map frac_count big_op.
From Perennial.goose_lang Require Import proofmode notation wpc_proofmode crash_borrow.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy spec_assert language_ctx.
From Perennial.goose_lang Require Import typing typed_translate adequacy refinement.
From Perennial.goose_lang Require Export recovery_adequacy spec_assert refinement_adequacy.
From Perennial.goose_lang Require Import metatheory.
From Perennial.goose_lang.lib Require Import list.
From Perennial.Helpers Require Import Qextra.
From Perennial.Helpers Require List.
From Perennial.program_proof Require Import lockmap_proof.

From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Perennial.program_proof Require Import addr.addr_proof.
From Perennial.program_proof Require Import txn.typed_translate.
From Perennial.program_proof Require Import txn.twophase_refinement_defs.
From Perennial.program_proof Require Import txn.wrapper_proof.
From Perennial.program_proof Require Import alloc.alloc_proof.
From Perennial.program_proof Require jrnl.sep_jrnl_proof.

Set Default Proof Using "Type".

Section reln.

  (* Records for the target language *)
  Notation ext := disk_op.
  Notation ffi := ffi_model.
  Notation ffi_semantics := (ffi_semantics ext ffi).
  Notation interp := (ffi_interp ffi).
  Notation interp_adeq := (ffi_interp ffi).
  Notation impl_ty := (ext_types ext).

Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp jrnl_spec_interp_adequacy.

  (* Records defining spec language extensions *)
  Notation spec_ext := jrnl_spec_ext.
  Notation spec_ffi := jrnl_spec_ffi_model.
  Notation spec_ffi_semantics := jrnl_spec_ext_semantics.
  Notation spec_interp := jrnl_spec_ffi_interp.
  Notation spec_ty := jrnl_ty.
  Notation spec_adeq := jrnl_spec_interp_adequacy.


  (*
  Notation sexpr := (@expr spec_ext).
  Notation sval := (@val spec_ext).
*)
  Notation iexpr := (@expr ext).
  Notation ival := (@val ext).
  (*
  Notation sty := (@ty (@val_tys _ spec_ty)).
  Notation SCtx := (@Ctx (@val_tys _ spec_ty)).
   *)

Notation sstate := (@state (@spec_ffi_op_field spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ffi_op_field spec_ext)).
Notation sval := (@val (@spec_ffi_op_field spec_ext)).
Notation istate := (@state ext).
Notation sty := (@ty (@val_tys _ spec_ty)).
Notation SCtx := (@Ctx (@val_tys _ spec_ty)).

Definition val_semTy `{!heapGS Σ} `{refinement_heapG Σ} := sval → ival → iProp Σ.

Import sep_jrnl_invariant.
Section reln_defs.
Context `{hG: !heapGS Σ}.
Context {hRG: refinement_heapG Σ}.
Context {htpG: twophaseG Σ}.
Context (JRNL_SIZE: nat).
Context (N: namespace).
Context (dinit : abstraction.disk).
Context (objs_dom : gset addr_proof.addr).
Context (γ γ': sep_jrnl_invariant.jrnl_names).
Context (tph: loc).
Existing Instance jrnlG0.


Existing Instances spec_ffi_model_field (* spec_ffi_op_field *) spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Definition atomically_has_semTy (es: sexpr) (e: iexpr) (vty: val_semTy) : iProp Σ :=
  (∀ (j: nat) K0 e0 (K: sexpr → sexpr) (CTX: LanguageCtx' K),
      is_twophase_started tph γ γ' dinit objs_dom j K0 e0 (K es) -∗
      WPC e @ (logical_reln_defns.sty_lvl_ops (specTy_model := twophaseTy_model JRNL_SIZE)); ⊤
                    {{ v, ∃ vs, is_twophase_started tph γ γ' dinit objs_dom j K0 e0 (K (of_val vs)) ∗
                                vty vs v }} {{ True }})%I.

Definition atomically_base_ty_interp (t: base_ty) :=
  λ (v1: sval) (v2: ival),
  match t with
    | uint64BT => (∃ x, ⌜ v1 = LitV $ LitInt x ∧ v2 = LitV $ LitInt x ⌝ : iProp Σ)%I
    | uint32BT => (∃ x, ⌜ v1 = LitV $ LitInt32 x ∧ v2 = LitV $ LitInt32 x ⌝ : iProp Σ)%I
    | byteBT => (∃ x, ⌜ v1 = LitV $ LitByte x ∧ v2 = LitV $ LitByte x ⌝ : iProp Σ)%I
    | boolBT => (∃ x, ⌜ v1 = LitV $ LitBool x ∧ v2 = LitV $ LitBool x ⌝ : iProp Σ)%I
    | unitBT => (⌜ v1 = LitV $ LitUnit ∧ v2 = LitV $ LitUnit ⌝ : iProp Σ)%I
    | stringBT => (∃ x, ⌜ v1 = LitV $ LitString x ∧ v2 = LitV $ LitString x ⌝ : iProp Σ)%I
  end.

Definition atomically_prodT_interp (t1 t2: sty) val_interp : sval → ival → iProp Σ :=
  λ vs v, (∃ v1 v2 vs1 vs2, ⌜ v = (v1, v2)%V ∧ vs = (vs1, vs2)%V⌝
                   ∗ val_interp t1 vs1 v1
                   ∗ val_interp t2 vs2 v2)%I.

Fixpoint atomically_listT_interp_aux (val_interp : sval → ival → iProp Σ)
         (lvs : list sval) (lv : list ival) : iProp Σ :=
  (match lvs, lv with
  | nil, nil => True%I
  | vs :: lvs, v :: lv =>
    val_interp vs v ∗ atomically_listT_interp_aux val_interp lvs lv
  | _, _ => False%I
  end)%I.

Definition atomically_listT_interp (t: sty) (val_interp : sty → sval → ival → iProp Σ) : sval → ival → iProp Σ :=
  λ vs v, (∃ lvs lv, ⌜ vs = val_of_list lvs ∧ v = val_of_list lv ⌝ ∗ atomically_listT_interp_aux (val_interp t) lvs lv)%I.

Definition atomically_sumT_interp (t1 t2: sty) val_interp : sval → ival → iProp Σ :=
  λ vs v, ((∃ v' vs', ⌜ v = InjLV v' ∧
                                vs = InjLV vs'⌝
                              ∗ val_interp t1 vs' v')
                     ∨
                   (∃ v' vs', ⌜ v = InjRV v' ∧
                                vs = InjRV vs'⌝
                              ∗ val_interp t2 vs' v'))%I.

Definition atomically_arrowT_interp (t1 t2: sty) (val_interp: sty → sval → ival → iProp Σ) :
  sval → ival → iProp Σ :=
  λ vs v,
    (∃ f x e fs xs es,
        ⌜ v = RecV f x e ∧
          vs = RecV fs xs es ⌝
        ∗ □ (∀ varg vsarg,
              val_interp t1 vsarg varg -∗
              atomically_has_semTy (App vs vsarg) (App v varg) (val_interp t2)))%I.

Fixpoint atomically_val_interp (t: sty) {struct t} :=
  match t with
  | baseT bt => atomically_base_ty_interp bt
  | prodT t1 t2 => atomically_prodT_interp t1 t2 atomically_val_interp
  | listT t => atomically_listT_interp t atomically_val_interp
  | sumT t1 t2 => atomically_sumT_interp t1 t2 atomically_val_interp
  | arrowT t1 t2 => atomically_arrowT_interp t1 t2 atomically_val_interp
  | extT AllocT => λ vspec vimpl,
    (∃ (ls li: loc) (max : u64),
                 ⌜ vimpl = #li ⌝ ∗ ⌜ vspec = #ls ⌝ ∗ ⌜ (0 < int.Z max)%Z ⌝ ∗ is_alloc max li ∗ jrnl_alloc ls max)%I
  | _ => λ _ _, False%I
  end.

Lemma atomically_val_interp_list_unfold t:
  atomically_val_interp (listT t) = atomically_listT_interp t (atomically_val_interp).
Proof. rewrite //=. Qed.

Record subst_tuple :=
  { subst_ty : sty ; subst_sval : sval; subst_ival: ival }.
Definition subst_ctx := gmap string subst_tuple.

Definition ctx_has_semTy `{hG: !heapGS Σ} `{hRG: !refinement_heapG Σ}
           (Γ: Ctx) es e τ : iProp Σ :=
  ∀ Γsubst (HPROJ: subst_ty <$> Γsubst = Γ),
  spec_ctx -∗
  ([∗ map] x ↦ t ∈ Γsubst, (atomically_val_interp (subst_ty t) (subst_sval t) (subst_ival t))) -∗
  atomically_has_semTy (subst_map (subst_sval <$> Γsubst) es)
            (subst_map (subst_ival <$> Γsubst) e)
            (atomically_val_interp τ).

Global Instance base_interp_pers es e t:
      Persistent (atomically_base_ty_interp t es e).
Proof. destruct t; apply _. Qed.

Instance atomically_listT_interp_aux_pers ls l
       (vTy: sval → ival → iProp Σ) :
       (∀ es' e', Persistent (vTy es' e')) →
       Persistent (atomically_listT_interp_aux vTy ls l).
Proof. intros ?. revert l. induction ls; destruct l => //=; apply _. Qed.

Instance atomically_listT_interp_pers  es e t
       (vTy: sty → sval → ival → iProp Σ) :
       (∀ t' es' e', Persistent (vTy t' es' e')) →
       Persistent (atomically_listT_interp t vTy es e).
Proof. intros. rewrite /atomically_listT_interp. apply _. Qed.

Global Instance atomically_val_interp_pers es e t:
      Persistent (atomically_val_interp t es e).
Proof. revert es e. induction t => ?? //=; try apply _. destruct x; apply _. Qed.

Global Instance sty_ctx_prop_pers (Γsubst: gmap string subst_tuple) :
      Persistent ([∗ map] t ∈ Γsubst, atomically_val_interp (subst_ty t) (subst_sval t) (subst_ival t))%I.
Proof.
  apply big_sepM_persistent => ??. apply atomically_val_interp_pers.
Qed.

Lemma atomically_listT_interp_refl_obj v :
  ⊢ atomically_listT_interp byteT atomically_val_interp (val_of_obj' (objBytes v)) (val_of_obj (objBytes v)).
Proof.
  induction v => //=.
  - rewrite /atomically_listT_interp. iExists [], []. eauto.
  - rewrite /atomically_listT_interp.
    iDestruct IHv as (lvs lv (Heq1&Heq2)) "H".
    simpl.
    rewrite /val_of_obj/val_of_obj' ?fmap_cons //= -/val_of_obj/val_of_obj'.
    iExists (_ :: lvs), (_ :: lv). rewrite //=.
    iSplit.
    { iPureIntro. rewrite /val_of_obj'/val_of_obj in Heq1 Heq2. split; f_equal; f_equal; eauto. }
    eauto.
Qed.

Lemma atomically_listT_interp_obj_inv vs v :
  atomically_listT_interp byteT atomically_val_interp vs v -∗
  ⌜ ∃ o, vs = val_of_obj' (objBytes o) ∧ v = val_of_obj (objBytes o) ⌝.
Proof.
  iIntros "H".
  iDestruct "H" as (lvs lv) "H". iDestruct "H" as ((Heq1&Heq2)) "H".
  subst.
  iInduction lvs as [| a lvs] "IH" forall (lv).
  { destruct lv as [| a lv].
    - iExists []. eauto.
    - rewrite /atomically_listT_interp_aux. iDestruct "H" as %[].
  }
  destruct lv as [| a' lv].
  { rewrite /atomically_listT_interp_aux. iDestruct "H" as %[]. }
  rewrite /atomically_listT_interp_aux -/atomically_listT_interp_aux.
  iDestruct "H" as "(Heq&H)".
  iDestruct ("IH" with "[$]") as %[o (Heq1&Heq2)].
  iDestruct "Heq" as %[? [-> ->]].
  iExists (_ :: o).
  rewrite //= /val_of_obj/val_of_obj' ?fmap_cons //=.
  iPureIntro. rewrite /val_of_obj'/val_of_obj in Heq1 Heq2. split; f_equal; f_equal; eauto.
Qed.

(*
Arguments val_interp {ext ffi ffi_semantics interp spec_ext spec_ffi spec_ffi_semantics spec_interp _ Σ hG hRG
  smodel hS} _%heap_type (_ _)%val_scope.

Arguments ctx_has_semTy {ext ffi ffi_semantics interp spec_ext spec_ffi spec_ffi_semantics spec_interp _
  hsT_model Σ hG hRG hS} _ (_ _)%expr_scope _%heap_type.

Arguments specTy_model {ext ffi interp spec_ext spec_ffi spec_ffi_semantics spec_interp} spec_ty.
*)

Scheme expr_typing_ind := Induction for atomic_body_expr_transTy Sort Prop with
    val_typing_ind := Induction for atomic_body_val_transTy Sort Prop.

Lemma disc_crash_true E k :
  ⊢ <disc> (|C={E}_k=> True).
Proof. auto. Qed.

Tactic Notation "spec_bind" open_constr(efoc) " as " ident(H) :=
  iStartProof;
  lazymatch goal with
  | |- context[ (is_twophase_started _ _ _ _ _ _ _ _ (?Kinit ?e))%I ] =>
    let H' := fresh H in
    refine_reshape_expr e ltac:(fun K' e' => unify e' efoc; destruct (tac_refine_bind' Kinit K' e e') as (->&H'); [split; eauto|])
    || fail "spec_bind: cannot find" efoc "in" e
  end.

Lemma ctx_has_semTy_subst
      e (es: sexpr) (t: sty) x v vs tx Γ:
      ctx_has_semTy (<[x:=tx]> Γ) es e t -∗
      atomically_val_interp tx vs v -∗
      ctx_has_semTy Γ (subst' x vs es) (subst' x v e) t.
Proof.
  rewrite /ctx_has_semTy.
  iIntros "Hhasty Hval".
  iIntros (Γsubst Hproj) "Hspec Hctx".
  destruct x as [|x] => //=.
  { iApply ("Hhasty" with "[] [$] [$]").
    eauto.
  }
  rewrite -?subst_map_insert'.
  iSpecialize ("Hhasty" $! (<[x := {| subst_ty := tx; subst_sval := vs; subst_ival := v |}]> Γsubst)
                 with "[] [$] [Hctx Hval]").
  { iPureIntro. rewrite -Hproj. apply: fmap_insert. }
  { iPoseProof (big_sepM_insert_2 with "[Hval] [Hctx]") as "$".
    * iFrame.
    * eauto.
  }
  rewrite ?fmap_insert //=.
Qed.

Lemma comparableTy_val_eq t vs1 v1 vs2 v2:
  is_comparableTy t = true →
  atomically_val_interp t vs1 v1 -∗
  atomically_val_interp t vs2 v2 -∗
  ⌜ v1 = v2 ↔ vs1 = vs2 ⌝.
Proof.
  revert vs1 v1 vs2 v2.
  induction t => vs1 v1 vs2 v2; try (inversion 1; fail).
  - intros. destruct t; iPureIntro; naive_solver.
  - intros (?&?)%andb_prop.
    intros.
    iDestruct 1 as (?? ?? (->&->)) "(H1&H2)".
    iDestruct 1 as (?? ?? (->&->)) "(H1'&H2')".
    rewrite -/atomically_val_interp.
    iPoseProof (IHt1 with "H1 H1'") as "%"; eauto.
    iPoseProof (IHt2 with "H2 H2'") as "%"; eauto.
    iPureIntro. naive_solver.
  - intros (?&?)%andb_prop.
    intros.
    iDestruct 1 as "[H|H]";
    iDestruct 1 as "[H'|H']";
    iDestruct "H" as (?? (->&->)) "H";
    iDestruct "H'" as (?? (->&->)) "H'".
    * iPoseProof (IHt1 with "H H'") as "%"; eauto.
      iPureIntro. split; inversion 1; subst; f_equal; naive_solver.
    * iPureIntro; split; inversion 1.
    * iPureIntro; split; inversion 1.
    * iPoseProof (IHt2 with "H H'") as "%"; eauto.
      iPureIntro. split; inversion 1; subst; f_equal; naive_solver.
  - intros. iIntros "[] H2".
  - intros. iIntros "[] H2".
Qed.

Opaque is_twophase_started.
Opaque crash_borrow.

Lemma atomically_fundamental_lemma:
  ∀ Γ (es : sexpr) (e : iexpr) τ, atomic_body_expr_transTy Γ (of_val #tph) es e τ →
    ⊢ ctx_has_semTy Γ es e τ.
Proof.
  iIntros (???? Htyping).
  remember (of_val #tph) as tph'.
  revert Heqtph'.
  induction Htyping using @expr_typing_ind with
      (P := (λ Γ tph' (es : sexpr) (e : iexpr) τ
             (HTYPE: atomic_body_expr_transTy Γ tph' es e τ),  tph' = of_val #tph →
               ⊢ ctx_has_semTy Γ es e τ))
      (P0 := (λ Γ tph' vs v τ
             (HTYPE: atomic_body_val_transTy Γ tph' vs v τ), tph' = of_val #tph →
               ⊢ spec_ctx -∗ atomically_val_interp τ vs v)); intros ->;
      try (iIntros (Γsubst HPROJ) "#Hspec #Hctx";
           iIntros (j K0 e0 K Hctx) "Hj").
  - subst.
    rewrite lookup_fmap in e.
    apply fmap_Some_1 in e as (t'&?&?). subst.
    iDestruct (big_sepM_lookup with "Hctx") as "H"; first eauto.
    rewrite /= ?lookup_fmap H //=.
    iApply wpc_value; iSplit.
    * iModIntro. iExists _; iFrame "H"; iFrame.
    * eauto.
  - subst.
    simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; first done.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) x2).
    spec_bind (subst_map ((subst_sval <$> Γsubst)) x1) as Hctx'.
    rewrite /atomically_has_semTy.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    wpc_bind (subst_map _ f2).
    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; first done.
    iSpecialize ("H" $! j _ _ (λ x, K (ectx_language.fill [AppLCtx (vs2)] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx'; last done. apply ectx_lang_ctx'. }
    iApply (wpc_mono' with "[Hv2] [] H"); last by eauto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    simpl. iDestruct "Hv1" as (?????? (Heq1&Heq2)) "#Hinterp".
    iSpecialize ("Hinterp" $! _ _ with "Hv2").
    rewrite /atomically_has_semTy.
    clear Hctx'.
    iApply ("Hinterp" with "Hj").
  - subst.
    iApply wp_wpc. iApply wp_value. iExists _. iFrame.
    iApply (IHHtyping); auto.
  - subst. simpl.
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. econstructor; eauto.
      { simpl. econstructor; eauto. }
      { econstructor; eauto. }
    }
    wp_pures; eauto.
    iExists _; iFrame. iModIntro.
    iExists _, _, _, _, _, _; iSplit; first eauto.
    iLöb as "IH".
    iModIntro. iIntros (v vs) "Hval".
    clear j K Hctx.
    iIntros (j ? ? K Hctx) "Hj".
    wpc_pures.
    { iClear "∗ #". auto. }
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. econstructor; eauto.
    }
    iPoseProof (ctx_has_semTy_subst with "[] []") as "H1".
    { iApply IHHtyping. eauto. }
    { simpl. iExists _, _, _, _, _, _. iFrame "IH"; eauto. }
    iPoseProof (ctx_has_semTy_subst with "[] Hval") as "H2".
    { iApply "H1". }
    iSpecialize ("H2" with "[//] [$] [$] [//] [Hj]").
    { do 2 (rewrite -subst_map_binder_insert' subst_map_binder_insert).
      iEval (rewrite (binder_delete_commute f x)). iFrame. }
    { do 2 (rewrite -subst_map_binder_insert' subst_map_binder_insert).
      iEval (rewrite {2}binder_delete_commute). iApply wpc_wp. iFrame. }
  - subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) cond').
    spec_bind (_ _ cond) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last auto.

    iIntros (vcond) "H". iDestruct "H" as (vscond) "(Hj&Hvcond)".
    (* split on the value of the bool *)
    iDestruct "Hvcond" as %(b&->&->).
    destruct b.
    * wpc_pures; first by (iClear "∗ #"; auto). simpl.
      iApply wp_wpc.
      iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
      { intros ??.
        apply head_prim_step_trans'. econstructor; eauto.
      }
      iApply wpc_wp.
      iApply (IHHtyping2 with "[//] [$] [$]"); eauto.
    * wpc_pures; first by (iClear "∗ #"; auto). simpl.
      iApply wp_wpc.
      iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
      { intros ??.
        apply head_prim_step_trans'. econstructor; eauto.
      }
      iApply wpc_wp.
      iApply (IHHtyping3 with "[//] [$] [$]"); eauto.
  - (* panic_expr_transTy *)
    subst. simpl.
    iApply wp_wpc.
    iDestruct (twophase_started_ub_det with "Hj") as "H".
    { set_solver+. }
    { intros; eapply stuck_Panic'. }
    wp_bind (Skip)%E.
    iApply (wpc_nval_elim_wp with "H"); eauto.
    wp_pures. iIntros "!> []".
  - subst. simpl.
    iApply wp_wpc.
    iApply wp_ncfupd.
    iApply wp_ArbitraryInt; first auto.
    iNext.
    iIntros.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    iModIntro. iExists _. iFrame. iExists _. iPureIntro; eauto.
  - subst. simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; first auto.
    iSpecialize ("H" $! j _ _ (λ x, K (ectx_language.fill [UnOpCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx'; last done. apply ectx_lang_ctx'. }
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u64), ⌜ un_op_eval ToUInt64Op v1 = Some #vres ∧
                            un_op_eval ToUInt64Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /atomically_val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
    }
    wp_pures; eauto.
  - subst. simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; first auto.
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u32), ⌜ un_op_eval ToUInt32Op v1 = Some #vres ∧
                            un_op_eval ToUInt32Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /atomically_val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
    }
    wp_pures; eauto.
  - subst. simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; first auto.
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u8), ⌜ un_op_eval ToUInt8Op v1 = Some #vres ∧
                            un_op_eval ToUInt8Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /atomically_val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
    }
    wp_pures; eauto.
  - subst. simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; first auto.
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: string), ⌜ un_op_eval ToStringOp v1 = Some #(LitString vres) ∧
                            un_op_eval ToStringOp vs1 = Some #(LitString vres) ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /atomically_val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
    }
    wp_pures; eauto.
  - (* un_op_transTy *)
    destruct op; try inversion e; subst. simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; first auto.
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iDestruct "Hv1" as (?) "(%&%)"; subst.
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    wp_pures; eauto.
  - subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    wpc_bind (subst_map _ e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
    simpl. spec_bind (_ _ e2) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    wp_pures; auto.
    iExists _. iFrame. iExists (bool_decide (vs1 = vs2)); eauto.
    iDestruct (comparableTy_val_eq with "Hv1 Hv2") as %Heq; auto.
    iPureIntro. split; first auto. do 2 f_equal.
    by apply bool_decide_iff.
  - subst. simpl.
    wpc_bind (subst_map _ e1').
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    simpl.

    wpc_bind (subst_map _ e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
    spec_bind (_ _ e2) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    simpl.

    iDestruct "Hspec" as "(#Hsrc&#Hstate)".
    (* Be patient, this is handling a bunch of cases. *)
    iApply wp_wpc.
    destruct op; inversion e; subst;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iDestruct "Hv2" as (?) "(%&%)"; subst;
    (iDestruct (twophase_started_step_puredet with "Hj") as "Hj";
        [ intros ??; apply head_prim_step_trans'; repeat econstructor; eauto
        | wp_pures; eauto; iExists _; iFrame; eauto]).
  - subst. simpl.
    wpc_bind (subst_map _ e1').
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    simpl.

    wpc_bind (subst_map _ e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
    spec_bind (_ _ e2) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    simpl.

    iDestruct "Hspec" as "(#Hsrc&#Hstate)".
    (* Be patient, this is handling a bunch of cases. *)
    iApply wp_wpc.
    destruct op; inversion e; subst;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iDestruct "Hv2" as (?) "(%&%)"; subst;
    (iDestruct (twophase_started_step_puredet with "Hj") as "Hj";
        [ intros ??; apply head_prim_step_trans'; repeat econstructor; eauto
        | wp_pures; eauto; iExists _; iFrame; eauto]).
  - subst. simpl.
    wpc_bind (subst_map _ e1').
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    simpl.

    wpc_bind (subst_map _ e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
    spec_bind (_ _ e2) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    simpl.

    iDestruct "Hspec" as "(#Hsrc&#Hstate)".
    iApply wp_wpc.
    subst;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iDestruct "Hv2" as (?) "(%&%)"; subst;
    (iDestruct (twophase_started_step_puredet with "Hj") as "Hj";
        [ intros ??; apply head_prim_step_trans'; repeat econstructor; eauto
        | wp_pures; eauto; iExists _; iFrame; eauto]).
  (* data *)
  - (* pair_transTy *)
    subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    wpc_bind (subst_map _ e2').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e2) as Hctx'.
    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
    iSpecialize ("H" $! j _ _ _ Hctx'  with "Hj").
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    simpl.
    clear Hctx'.

    spec_bind (_ ,_)%E as Hctx'.
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    wp_pures; auto.
    iExists _. iFrame. iExists _, _, _, _. iFrame. eauto.
  - subst. simpl.
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v) "H". iDestruct "H" as (vs) "(Hj&Hv)".
    clear Hctx'.
    simpl.
    iDestruct "Hv" as (???? (->&->)) "(?&?)".

    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    wp_pures; eauto.
  - subst. simpl.
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v) "H". iDestruct "H" as (vs) "(Hj&Hv)".
    clear Hctx'.
    simpl.
    iDestruct "Hv" as (???? (->&->)) "(?&?)".

    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    wp_pures; eauto.
  - subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H1"; eauto.
    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H2"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) ehd').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) ehd) as Hctx'.
    iSpecialize ("H1" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[H2] [] H1"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) etl').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) etl) as Hctx'.
    iSpecialize ("H2" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hv1] [] H2"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    clear Hctx'.
    simpl.

    spec_bind (vs1, vs2)%E as Hctx'.
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _ (λ x : sexpr, K (ectx_language.fill [InjRCtx] x))
                 with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    iDestruct (twophase_started_step_puredet with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    iApply wp_wpc.
    wp_pures; auto.
    iExists _. iFrame. iModIntro.
    rewrite /atomically_listT_interp.
    iDestruct "Hv2" as (lvs lv (->&->)) "H".
    iExists (vs1 :: lvs), (v1 :: lv). iSplit; first by eauto.
    simpl. iFrame.
  - subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H1"; eauto.
    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H2"; eauto.
    iPoseProof (IHHtyping3 with "[//] [$] [$]") as "H3"; eauto.
    rewrite /impl.ListMatch.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) consfun').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) consfun) as Hctx'.
    iSpecialize ("H3" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[H1 H2] [] H3"); last by auto.
    iIntros (vconsfun) "H". iDestruct "H" as (vsconsfun) "(Hj&Hvconsfun)".
    clear Hctx'.
    simpl.

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) nilfun').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) nilfun) as Hctx'.
    iSpecialize ("H2" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[H1 Hvconsfun] [] H2"); last by auto.
    iIntros (vnilfun) "H". iDestruct "H" as (vsnilfun) "(Hj&Hvnilfun)".
    clear Hctx'.
    simpl.

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) el').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) el) as Hctx'.
    iSpecialize ("H1" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hvnilfun Hvconsfun] [] H1"); last by auto.
    iIntros (vl) "H". iDestruct "H" as (vsl) "(Hj&Hvsl)".
    clear Hctx'.
    simpl.
    iApply wp_wpc.

    spec_bind (App _ vsl)%E as Hctx'.
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                 (λ x, K (ectx_language.fill [AppLCtx vsnilfun; AppLCtx vsconsfun] x))  with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    wp_pures; eauto.
    clear Hctx'.
    simpl.

    spec_bind (λ: _, _)%E as Hctx'.
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                 (λ x, K (ectx_language.fill [AppLCtx vsnilfun; AppLCtx vsconsfun] x))  with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    simpl.
    clear Hctx'.

    spec_bind (App _ vsnilfun)%E as Hctx'.
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                 (λ x, K (ectx_language.fill [AppLCtx vsconsfun] x))  with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    spec_bind (λ: _, _)%E as Hctx'.
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                 (λ x, K (ectx_language.fill [AppLCtx vsconsfun] x))  with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    spec_bind (App _ vsconsfun)%E as Hctx'.
    iDestruct (twophase_started_step_puredet  with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    iDestruct "Hvsl" as (lvs lv (->&->)) "H".
    destruct lvs as [|vs lvs];
    destruct lv as [|v lv]; try (iDestruct "H" as %[]; done).

    * simpl.
      iDestruct (twophase_started_step_puredet  with "Hj") as "Hj".
      { intros ??.
        apply head_prim_step_trans'. repeat econstructor; eauto.
      }

      spec_bind (Rec BAnon _ (vsnilfun (LitV LitUnit)))%E as Hctx'.
      iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                   (λ x, K (ectx_language.fill [AppLCtx #()] x)) with "Hj") as "Hj".
      { intros ??.
        apply head_prim_step_trans'. repeat econstructor; eauto.
      }
      simpl.
      clear Hctx'.

      iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _ _ _
                   _ with "Hj") as "Hj".
      { intros ??.
        apply head_prim_step_trans'. repeat econstructor; eauto.
      }

      simpl.

      wp_pures.
      rewrite /atomically_arrowT_interp.
      iDestruct "Hvnilfun" as (f x e fs xs es (->&->)) "#Hwand".
      iSpecialize ("Hwand" $! #() #() with "[] Hj").
      { eauto. }
      iApply (wpc_wp _ _ _ _ _ True%I).
      iApply (wpc_mono' with "[] [] Hwand"); last by auto.
      iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
      iExists _. iFrame.
    * simpl.
      iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _ _ _
                   _ with "Hj") as "Hj".
      { intros ??.
        apply head_prim_step_trans'. repeat econstructor; eauto.
      }

      spec_bind (Rec _ _ ((vsconsfun
                      (Var "p"))))%E as Hctx'.
      iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                   (λ x : sexpr, K (ectx_language.fill [AppLCtx (vs, val_of_list lvs)] x)) with "Hj") as "Hj".
      { intros ??.
        apply head_prim_step_trans'. repeat econstructor; eauto.
      }
      simpl.
      clear Hctx'.

      iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _ _ _
                   _ with "Hj") as "Hj".
      { intros ??.
        apply head_prim_step_trans'. repeat econstructor; eauto.
      }
      simpl.

      wp_pures.
      rewrite /atomically_arrowT_interp.
      iDestruct "Hvconsfun" as (f x e fs xs es (->&->)) "#Hwand".
      iSpecialize ("Hwand" $! (v, list.val_of_list lv)%V (vs, list.val_of_list lvs)%V with "[H] Hj").
      { iExists _, _, _, _. iSplit; first by eauto.
        iDestruct "H" as "($&H)".
        iExists _, _. iSplit; first eauto. iFrame.
      }
      iApply (wpc_wp _ _ _ _ _ True%I).
      iApply (wpc_mono' with "[] [] Hwand"); last by auto.
      iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
      iExists _. iFrame.
  - subst. simpl.
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    simpl.
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _ _
                 _ with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    simpl.
    wp_pures; auto.
    iExists _. iFrame. iLeft. iExists _, _; iFrame; eauto.
  - subst. simpl.
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    simpl.
    iApply wp_wpc.
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _ _
                 _ with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    wp_pures; auto.
    iExists _. iFrame. iRight. iExists _, _; iFrame; eauto.
  - subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) cond').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) cond) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    iDestruct "Hv1" as "[Hleft|Hright]".
    {
      iDestruct "Hleft" as (?? (->&->)) "Hv".
      wpc_pures; first (iClear "# ∗"; auto).
      iApply wp_wpc.
      iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _ _
                                               _ with "Hj") as "Hj".
      { intros ??.
        apply head_prim_step_trans'. repeat econstructor; eauto.
      }
      iApply wpc_wp.
      wpc_bind (subst_map _ e1').
      iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
      spec_bind (subst_map _ e1) as Hctx'.
      iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
      iApply (wpc_mono' with "[Hv] [] H"); last first.
      { iIntros "H". iExact "H". }
      iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
      simpl. iDestruct "Hv1" as (?????? (Heq1&Heq2)) "#Hinterp".
      iSpecialize ("Hinterp" with "[$]").
      iSpecialize ("Hinterp" $! j _ _ _ Hctx with "Hj").
      iApply (wpc_mono' with "[] [] Hinterp"); last first.
      { iIntros "H". iExact "H". }
      { iIntros (v'') "H". iDestruct "H" as (vs'') "(Hj&Hv')".
        iExists _. iFrame. }
    }
    {
      iDestruct "Hright" as (?? (->&->)) "Hv".
      wpc_pures; first (iClear "# ∗"; auto).
      iApply wp_wpc.
      iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _ _
                                               _ with "Hj") as "Hj".
      { intros ??.
        apply head_prim_step_trans'. repeat econstructor; eauto.
      }
      iApply (wpc_wp _ _).
      wpc_bind (subst_map _ e2').
      iPoseProof (IHHtyping3 with "[//] [$] [$]") as "H"; eauto.
      spec_bind (subst_map _ e2) as Hctx'.
      iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
      iApply (wpc_mono' with "[Hv] [] H"); last first.
      { iIntros "H". iExact "H". }
      iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
      simpl. iDestruct "Hv1" as (?????? (Heq1&Heq2)) "#Hinterp".
      iSpecialize ("Hinterp" with "[$]").
      iSpecialize ("Hinterp" $! j _ _ _ Hctx with "Hj").
      iApply (wpc_mono' with "[] [] Hinterp"); last by auto.
      iIntros (v'') "H". iDestruct "H" as (vs'') "(Hj&Hv')".
      iExists _. iFrame.
    }
  (* Journal operations *)
  - subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e2').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e2) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    clear Hctx'.
    simpl.
    iDestruct "Hv2" as %[? [Heq1 Heq2]].
    subst.
    iDestruct "Hv1" as %(?&?&?&?&(Heq1&Heq2)&(a&Heqa&Heqa')&Hrest).
    destruct Hrest as (?&?&?&?&(->&->)&Hrest). subst.
    destruct Hrest as ((o&?&?)&?&?). subst.
    replace (#a, (#o, #()))%V with (addr2val (a,o)) by auto.
    replace (#a, (#o, #()))%V with (addr2val' (a,o)) by auto.
    iApply wp_wpc.
    spec_bind (addr2val' (a, o)%core, #x)%E as Hctx'.
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                 (λ x : sexpr, K (ectx_language.fill [ExternalOpCtx _] x)) with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    iPoseProof (wp_Txn__ReadBuf' tph _ _ _ _ _ _ _ _ (a, o) x with "Hj") as "H".
    iApply "H".
    iNext. iIntros (v) "H". iExists _. iFrame.
    iApply atomically_listT_interp_refl_obj.
  - subst. simpl.
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    iDestruct "Hv1" as %(?&?&?&?&(Heq1&Heq2)&(a&Heqa&Heqa')&Hrest).
    destruct Hrest as (?&?&?&?&(->&->)&Hrest). subst.
    destruct Hrest as ((o&?&?)&?&?). subst.
    replace (#a, (#o, #()))%V with (addr2val (a,o)) by auto.
    replace (#a, (#o, #()))%V with (addr2val' (a,o)) by auto.
    iApply wp_wpc.
    iPoseProof (wp_Txn__ReadBufBit' tph _ _ _ _ _ _ _ _ (a, o) with "Hj") as "H".
    iApply "H".
    iNext. iIntros (v) "H". iExists _. iFrame.
    iExists _. eauto.
  - subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e2').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e2) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    clear Hctx'.
    simpl.
    iDestruct "Hv1" as %(?&?&?&?&(Heq1&Heq2)&(a&Heqa&Heqa')&Hrest).
    destruct Hrest as (?&?&?&?&(->&->)&Hrest). subst.
    destruct Hrest as ((o&?&?)&?&?). subst.
    replace (#a, (#o, #()))%V with (addr2val (a,o)) by auto.
    replace (#a, (#o, #()))%V with (addr2val' (a,o)) by auto.
    iApply wp_wpc.
    iDestruct (atomically_listT_interp_obj_inv with "Hv2") as %[v [-> ->]].
    spec_bind (addr2val' (a, o)%core, (val_of_obj' (objBytes v)))%E as Hctx'.
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                 (λ x : sexpr, K (ectx_language.fill [ExternalOpCtx _] x)) with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    iPoseProof (wp_Txn__OverWrite' tph _ _ _ _ _ _ _ _ (a, o) (objBytes v) with "Hj") as "H".
    iApply "H".
    iNext. iIntros "H". iExists _. iFrame.
    eauto.
  - subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e2').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e2) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    clear Hctx'.
    simpl.
    iDestruct "Hv1" as %(?&?&?&?&(Heq1&Heq2)&(a&Heqa&Heqa')&Hrest).
    destruct Hrest as (?&?&?&?&(->&->)&Hrest). subst.
    destruct Hrest as ((o&?&?)&?&?). subst.
    replace (#a, (#o, #()))%V with (addr2val (a,o)) by auto.
    replace (#a, (#o, #()))%V with (addr2val' (a,o)) by auto.
    iApply wp_wpc.
    iDestruct "Hv2" as (b) "(->&->)".
    replace (#b) with (val_of_obj (objBit b)); auto.
    replace (#b) with (val_of_obj' (objBit b)); auto.
    spec_bind (addr2val' (a, o)%core, (val_of_obj' (objBit b)))%E as Hctx'.
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                 (λ x : sexpr, K (ectx_language.fill [ExternalOpCtx _] x)) with "Hj") as "Hj".
    { intros ??.
      apply head_prim_step_trans'. repeat econstructor; eauto.
    }
    iPoseProof (wp_Txn__OverWriteBit' tph _ _ _ _ _ _ _ _ (a, o) (objBit b) with "Hj") as "H".
    iApply "H".
    iNext. iIntros "H". iExists _. iFrame.
    eauto.
  - subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e2').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e2) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    simpl.
    iDestruct "Hv1" as (ls li max -> -> Hgt0) "(His_alloc&Hjrnl_alloc)".
    iDestruct "Hv2" as %(n&->&->).
    iApply wp_wpc.
    rewrite /op_wrappers.Alloc__MarkUsed'.
    assert (LanguageCtx' (λ x : sexpr, K (ectx_language.fill [@ExternalOpCtx (spec_ffi_op_field) MarkUsedOp] x))).
    { apply comp_ctx'; eauto. apply ectx_lang_ctx'. }
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                 (λ x : sexpr, K (ectx_language.fill [ExternalOpCtx _] x)) _  with "Hj") as "Hj";
              first (intros ??; apply head_prim_step_trans'; repeat econstructor; eauto).
    wp_bind (#li, #n)%E.
    iDestruct (twophase_started_ub_det_with_alloc' with "[$] [$]") as "H".
    { set_solver. }
    iApply (wpc_nval_elim_wp with "H"); auto.
    wp_pures.
    iIntros "!> H".
    iNamed "H".
    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnotstuck).
    apply not_stuck'_MarkUsedOp_inv in Hnotstuck
      as (σj&max'&Hopen&Hlookup1&Hlt_max); last auto.
    assert (max = max').
    { destruct Halways_steps as (?&Hsub'&?).
      destruct Hsub' as (?&?&Heq_allocs&?). rewrite Heq_allocs in Hin.
      destruct Hsub as (?&Hopen'&?&?&Hsub_alloc).
      rewrite Hopen in Hopen'. inversion Hopen'. subst.
      eapply map_subseteq_spec in Hsub_alloc; eauto. rewrite Hlookup1 in Hsub_alloc. congruence.
    }
    iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl'";
      [eassumption|eassumption|].
    subst.
    wp_apply (wp_MarkUsed with "[$]").
    { lia. }
    iExists (#()). iSplit; last eauto.
    iExists _, _, _, _. iFrame "# ∗ %".
    iPureIntro.
    eapply always_steps_trans; first by eapply Halways_steps.
    unshelve (eapply always_steps_bind); eauto.
    eapply always_steps_MarkUsedOp; eauto.
    { intuition. }
    { destruct Halways_steps as (?&Hsub'&?).
      destruct Hsub' as (?&?&Heq_allocs&?). rewrite Heq_allocs in Hin.
      eauto.
    }
  - subst. simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    iPoseProof (IHHtyping2 with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e2').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e2) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    clear Hctx'.
    simpl.
    iDestruct "Hv1" as (ls li max -> -> Hgt0) "(His_alloc&Hjrnl_alloc)".
    iDestruct "Hv2" as %(n&->&->).
    iApply wp_wpc.
    wp_bind (#li, #n)%E.
    assert (LanguageCtx' (λ x : sexpr, K (ectx_language.fill [@ExternalOpCtx (spec_ffi_op_field) FreeNumOp] x))).
    { apply comp_ctx'; eauto. apply ectx_lang_ctx'. }
    iDestruct (twophase_started_step_puredet _ _ _ _ _ _ _
                 (λ x : sexpr, K (ectx_language.fill [ExternalOpCtx _] x)) _  with "Hj") as "Hj";
              first (intros ??; apply head_prim_step_trans'; repeat econstructor; eauto).
    iDestruct (twophase_started_ub_det_with_alloc' with "[$] [$]") as "H".
    { set_solver. }
    iApply (wpc_nval_elim_wp with "H"); auto.
    rewrite /op_wrappers.Alloc__FreeNum'.
    wp_pures.
    iIntros "!> H".
    iNamed "H".
    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnotstuck).
    apply not_stuck'_FreeNumOp_inv in Hnotstuck
      as (σj&max'&Hopen&Hlookup1&Hlt_max); last auto.
    assert (max = max').
    { destruct Halways_steps as (?&Hsub'&?).
      destruct Hsub' as (?&?&Heq_allocs&?). rewrite Heq_allocs in Hin.
      destruct Hsub as (?&Hopen'&?&?&Hsub_alloc).
      rewrite Hopen in Hopen'. inversion Hopen'. subst.
      eapply map_subseteq_spec in Hsub_alloc; eauto. rewrite Hlookup1 in Hsub_alloc. congruence.
    }
    iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl'";
      [eassumption|eassumption|].
    subst.
    wp_apply (wp_FreeNum with "[$]").
    { lia. }
    { lia. }
    iExists (#()). iSplit; last eauto.
    iExists _, _, _, _. iFrame "# ∗ %".
    iPureIntro.
    eapply always_steps_trans; first by eapply Halways_steps.
    eapply always_steps_bind.
    eapply always_steps_FreeNumOp; eauto.
    { intuition. }
    { destruct Halways_steps as (?&Hsub'&?).
      destruct Hsub' as (?&?&Heq_allocs&?). rewrite Heq_allocs in Hin.
      eauto.
    }
  - subst. simpl.
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.
    iDestruct "Hv1" as (ls li max -> -> Hgt0) "(His_alloc&Hjrnl_alloc)".
    iApply wp_wpc.
    wp_pure1.
    wp_bind (Skip)%E.
    iDestruct (twophase_started_ub_det_with_alloc' with "[$] [$]") as "H".
    { set_solver. }
    iApply (wpc_nval_elim_wp with "[$]"); auto.
    wp_pures.
    iIntros "!> H".
    iNamed "H".
    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnotstuck).
    iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl'";
      [eassumption|eassumption|].
    subst.
    wp_pures.
    wp_apply (wp_AllocNum with "[$]").
    iIntros (n Hlt_max).
    iExists (#n). iSplit; last eauto.
    iExists _, _, _, _. iFrame "Hj". iSplitL "Htwophase".
    { iExact "Htwophase". }
    iFrame "# ∗ %".
    iPureIntro.
    eapply always_steps_trans; first by eapply Halways_steps.
    eapply always_steps_bind.
    eapply always_steps_AllocOp; eauto.
    { intuition. }
    { destruct Halways_steps as (?&Hsub'&?).
      destruct Hsub' as (?&?&Heq_allocs&?). rewrite Heq_allocs in Hin.
      eauto.
    }
  - subst. simpl.
    iPoseProof (IHHtyping with "[//] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e1) as Hctx'.
    iSpecialize ("H" $! j _ _ _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.
    iDestruct "Hv1" as (ls li max -> -> Hgt0) "(His_alloc&Hjrnl_alloc)".
    iApply wp_wpc.
    wp_pure1.
    wp_bind (Skip)%E.
    iDestruct (twophase_started_ub_det_with_alloc' with "[$] [$]") as "H".
    { set_solver. }
    iApply (wpc_nval_elim_wp with "[$]"); auto.
    wp_pures.
    iIntros "!> H".
    iNamed "H".
    destruct Hnotstuck as (s&g&Hsub&Hdom&Hnotstuck).
    iDestruct (is_twophase_wf_jrnl with "Htwophase") as "%Hwf_jrnl'";
      [eassumption|eassumption|].
    subst.
    wp_apply (wp_NumFree with "[$]").
    iIntros (n Hle_max).
    iExists (#n). iSplit; last eauto.
    iExists _, _, _, _. iFrame "Hj". iSplitL "Htwophase".
    { iExact "Htwophase". }
    iFrame "# ∗ %".
    iPureIntro.
    eapply always_steps_trans; first by eapply Halways_steps.
    eapply always_steps_bind.
    eapply always_steps_NumFreeOp.
    { intuition. }
    { destruct Halways_steps as (?&Hsub'&?).
      destruct Hsub' as (?&?&Heq_allocs&?). rewrite Heq_allocs in Hin.
      eauto.
    }
    { lia. }
  (* Value typing *)
  - iIntros "Hctx".
    inversion a; subst; eauto.
  - iIntros "#Hctx".
    iPoseProof (IHHtyping with "[$]") as "Hv1"; eauto.
    iPoseProof (IHHtyping0 with "[$]") as "Hv2"; eauto.
    iExists _, _, _, _. iSplitL ""; first by eauto. iFrame.
  - iIntros "#Hctx". iExists [], []. simpl. eauto.
  - iIntros "#Hctx".
    iPoseProof (IHHtyping with "[$]") as "Hv1"; eauto.
    iPoseProof (IHHtyping0 with "[$]") as "Hv2"; eauto.
    iDestruct "Hv2" as (l l' (->&->)) "H".
    iExists (vhd :: l), (vhd' :: l').
    iSplit; first eauto. iFrame.
  - iIntros "#Hctx".
    iLeft. iExists _, _.
    iSplitL ""; first by eauto. iApply (IHHtyping with "[$]").
    eauto.
  - iIntros "#Hctx".
    iRight. iExists _, _.
    iSplitR ""; first by eauto. iApply (IHHtyping with "[$]").
    eauto.
Qed.

End reln_defs.
End reln.
