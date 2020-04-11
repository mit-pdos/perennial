From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation wpc_proofmode.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy spec_assert language_ctx.
From Perennial.goose_lang Require Import typing typed_translate adequacy refinement.
From Perennial.goose_lang Require Export recovery_adequacy spec_assert refinement_adequacy.
From Perennial.goose_lang Require Import metatheory.

Set Default Proof Using "Type".

Section reln.
Context {ext: ext_op}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ext_semantics ext ffi}.
Context `{interp: !ffi_interp ffi}.
Context `{interp_adeq: !ffi_interp_adequacy}.
Context (impl_ty: ext_types ext).

Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{spec_interp: @spec_ffi_interp spec_ffi}.
Context `{spec_adeq: !spec_ffi_interp_adequacy}.
Context (spec_ty: ext_types (@spec_ext_op_field spec_ext)).

Context {LVL_INIT: nat}.
Context {LVL_OPS: nat}.

Notation sstate := (@state (@spec_ext_op_field spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ext_op_field spec_ext)).
Notation sval := (@val (@spec_ext_op_field spec_ext)).
Notation istate := (@state ext).
Notation iexpr := (@expr ext).
Notation ival := (@val ext).
Notation sty := (@ty (@val_tys _ spec_ty)).

Definition val_semTy `{!heapG Σ} `{refinement_heapG Σ} `{crashG Σ} := sval → ival → iProp Σ.

Class specTy_model :=
  { styG : gFunctors → Set;
    sty_names : Set;
    sty_get_names : ∀ Σ : gFunctors, styG Σ → sty_names;
    sty_update : ∀ Σ : gFunctors, styG Σ → sty_names → styG Σ;
    sty_update_get : ∀ (Σ : gFunctors) (hF : styG Σ) (names : sty_names),
                       sty_get_names Σ (sty_update Σ hF names) = names;
    sty_get_update : ∀ (Σ : gFunctors) (hF : styG Σ), sty_update Σ hF (sty_get_names Σ hF) = hF;
    sty_update_update : ∀ (Σ : gFunctors) (hF : styG Σ) (names1 names2 : sty_names),
                          sty_update Σ (sty_update Σ hF names1) names2 = sty_update Σ hF names2;
    sty_inv : ∀ {Σ} `{!heapG Σ} `{!refinement_heapG Σ} `{crashG Σ}, styG Σ → iProp Σ;
    sty_init : ∀ {Σ} `{!heapG Σ} `{!refinement_heapG Σ} `{crashG Σ}, styG Σ → iProp Σ;
    sty_crash_cond : ∀ {Σ} `{!heapG Σ} `{!refinement_heapG Σ} `{crashG Σ}, styG Σ → iProp Σ;
    styN: coPset;
    styN_disjoint : ↑ sN ## styN;
    sty_val_interp : ∀ {Σ} `{!heapG Σ} `{!refinement_heapG Σ} `{crashG Σ} (hS: styG Σ),
                     @ext_tys (@val_tys (@spec_ext_op_field spec_ext) spec_ty) → val_semTy;
    sty_val_persistent:
      forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ) τ es e,
        Persistent (sty_val_interp hS τ es e);
    sty_inv_persistent:
      forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
        Persistent (sty_inv hS) }.

(*
Context `{Hhpre: @heapPreG ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.
*)

Section reln_defs.
Context `{hG: !heapG Σ}.
Context {hRG: refinement_heapG Σ}.
Context {hC: crashG Σ}.
Context `{hS: @styG smodel Σ}.


Existing Instances spec_ffi_model_field (* spec_ext_op_field *) spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Definition has_semTy (es: sexpr) (e: iexpr) (vty: val_semTy) : iProp Σ :=
  (∀ (j: nat) (K: sexpr → sexpr) (CTX: LanguageCtx K),
      j ⤇ K es -∗ WPC e @ NotStuck; LVL_OPS; ⊤; (⊤ ∖ ↑sN ∖ styN) {{ v, ∃ vs, j ⤇ K (of_val vs)
                                                                    ∗ vty vs v }}
                                                      {{ True }})%I.

Definition base_ty_interp (t: base_ty) :=
  λ (v1: sval) (v2: ival),
  match t with
    | uint64BT => (∃ x, ⌜ v1 = LitV $ LitInt x ∧ v2 = LitV $ LitInt x ⌝ : iProp Σ)%I
    | uint32BT => (∃ x, ⌜ v1 = LitV $ LitInt32 x ∧ v2 = LitV $ LitInt32 x ⌝ : iProp Σ)%I
    | byteBT => (∃ x, ⌜ v1 = LitV $ LitByte x ∧ v2 = LitV $ LitByte x ⌝ : iProp Σ)%I
    | boolBT => (∃ x, ⌜ v1 = LitV $ LitBool x ∧ v2 = LitV $ LitBool x ⌝ : iProp Σ)%I
    | unitBT => (⌜ v1 = LitV $ LitUnit ∧ v2 = LitV $ LitUnit ⌝ : iProp Σ)%I
    | stringBT => (∃ x, ⌜ v1 = LitV $ LitString x ∧ v2 = LitV $ LitString x ⌝ : iProp Σ)%I
  end.

Inductive loc_status :=
| loc_readable
| loc_writing.
Canonical Structure loc_statusO := leibnizO loc_status.

Definition loc_inv (ls: loc) (l: loc) (vTy: val_semTy) :=
  (∃ (stat: loc_status),
    match stat with
    | loc_readable => ∃ q vs v, vTy vs v ∗ ls s↦{q} vs ∗ l ↦{q} v
    | loc_writing => ∃ vs, na_heap_mapsto_st WSt ls 1 vs
   end)%I.

Definition locN := nroot.@"loc".

Definition is_loc ls l vTy :=
  inv locN (loc_inv ls l vTy).

Fixpoint val_interp (t: sty) (vs: sval) (v: ival) :=
  match t with
  | baseT bt => base_ty_interp bt vs v
  | prodT t1 t2 => (∃ v1 v2 vs1 vs2, ⌜ v = (v1, v2)%V ∧
                                       vs = (vs1, vs2)%V⌝
                   ∗ val_interp t1 vs1 v1
                   ∗ val_interp t2 vs2 v2)%I
  | sumT t1 t2 => ((∃ v' vs', ⌜ v = InjLV v' ∧
                                vs = InjLV vs'⌝
                              ∗ val_interp t1 vs' v')
                     ∨
                   (∃ v' vs', ⌜ v = InjRV v' ∧
                                vs = InjRV vs'⌝
                              ∗ val_interp t2 vs' v'))%I
  | arrayT t => ((∃ l ls (indices: list unit),
                     ⌜ vs = LitV $ LitLoc ls ∧ v = LitV $ LitLoc l ⌝ ∗
                     [∗ list] i↦_ ∈ indices, is_loc (ls +ₗ i) (l +ₗ i) (val_interp t))
                 ∨ (⌜ vs = #null ∧ v = #null⌝))%I
  | arrowT t1 t2 =>
    (∃ f x e fs xs es,
        ⌜ v = RecV f x e ∧
          vs = RecV fs xs es ⌝
        ∗ □ (∀ varg vsarg,
              val_interp t1 vsarg varg -∗
              has_semTy (App vs vsarg) (App v varg) (val_interp t2)))%I
  | extT x => sty_val_interp hS x vs v
  | mapValT vt => False%I
  | structRefT ts => False%I
  end.

End reln_defs.

Class specTy_update `(hsT_model: !specTy_model) :=
  { sty_preG : gFunctors → Type;
    styΣ: gFunctors;
    subG_styPreG : forall Σ, subG styΣ Σ -> sty_preG Σ;
    sty_update_pre: ∀ Σ, sty_preG Σ -> sty_names -> styG Σ;
    sty_update_pre_update: ∀ Σ (hPre: sty_preG Σ) names1 names2,
        sty_update Σ (sty_update_pre _ hPre names1) names2 =
        sty_update_pre _ hPre names2;
    sty_update_pre_get: ∀ Σ (hPre: sty_preG Σ) names,
        sty_get_names _ (sty_update_pre _ hPre names) = names;
  }.

Section reln_adeq.

Context `{hsT_model: !specTy_model} (spec_trans: sval → ival → Prop).

Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.

Context (upd: specTy_update hsT_model).

Definition sty_init_obligation1 (sty_initP: istate → sstate → Prop) :=
      forall Σ `(hG: !heapG Σ) `(hRG: !refinement_heapG Σ) `(hC: crashG Σ) (hPre: sty_preG Σ) σs σ
      (HINIT: sty_initP σ σs),
        ⊢ ffi_start (heapG_ffiG) σ.(world) -∗
         ffi_start (refinement_spec_ffiG) σs.(world) -∗
         |={styN}=> ∃ (names: sty_names), let H0 := sty_update_pre _ hPre names in sty_init H0.

Definition sty_init_obligation2 (sty_initP: istate → sstate → Prop) :=
  ∀ σ σs, sty_initP σ σs → ffi_initP σ.(world) ∧ ffi_initP σs.(world).

Definition sty_crash_obligation :=
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
      ⊢ sty_inv hS -∗ sty_crash_cond hS ={styN, ∅}=∗ ▷ ∀ (hG': heapG Σ), |={⊤}=>
      ∀ (hC': crashG Σ) σs,
      (∃ σ0 σ1, ffi_restart (heapG_ffiG) σ1.(world) ∗
      ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ0.(world) (heapG_ffiG (hG := hG')) σ1.(world)) -∗
      ffi_ctx (refinement_spec_ffiG) σs.(world) -∗
      ∃ (σs': sstate) (HCRASH: crash_prim_step (spec_crash_lang) σs σs'),
      ffi_ctx (refinement_spec_ffiG) σs.(world) ∗
      ∀ (hRG': refinement_heapG Σ),
      ffi_crash_rel Σ (refinement_spec_ffiG (hRG := hRG)) σs.(world)
                      (refinement_spec_ffiG (hRG := hRG')) σs'.(world) -∗
      ffi_restart (refinement_spec_ffiG) σs'.(world) -∗
      |={styN}=> ∃ (new: sty_names), sty_init (sty_update Σ hS new).

Definition sty_rules_obligation :=
  ∀ (es: sval) (vs: sval) e v t1 t2,
    get_ext_tys es (t1, t2) →
    spec_trans es e →
    forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ),
    sty_inv hS -∗
    spec_ctx -∗
    val_interp (hS := hS) t1 vs v -∗
    has_semTy (es vs) (e v) (val_interp (hS := hS) t2).

Definition sty_crash_inv_obligation :=
  (forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hS: styG Σ)
     e (Φ: ival → iProp Σ),
    ⊢ sty_init hS -∗
    spec_ctx -∗
    (sty_inv hS -∗ (WPC e @ NotStuck; LVL_OPS; ⊤; (⊤ ∖ ↑sN ∖ styN) {{ Φ }} {{ True%I }})) -∗
    |={⊤}=> sty_inv hS ∗
    WPC e @ NotStuck; LVL_INIT; ⊤; (⊤ ∖ ↑sN ∖ styN) {{ Φ }} {{ sty_crash_cond hS }}).

Record subst_tuple :=
  { subst_ty : sty ; subst_sval : sval; subst_ival: ival }.
Definition subst_ctx := gmap string subst_tuple.

Definition ctx_has_semTy `{hG: !heapG Σ} `{hC: !crashG Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ}
           (Γ: Ctx) es e τ : iProp Σ :=
  ∀ Γsubst (HPROJ: subst_ty <$> Γsubst = Γ),
  sty_inv hS -∗
  spec_ctx -∗
  trace_ctx -∗
  ([∗ map] x ↦ t ∈ Γsubst, (val_interp (hS := hS) (subst_ty t) (subst_sval t) (subst_ival t))) -∗
  has_semTy (subst_map (subst_sval <$> Γsubst) es)
            (subst_map (subst_ival <$> Γsubst) e)
            (val_interp (hS := hS) τ).

Instance base_interp_pers Σ es e t:
      Persistent (base_ty_interp (Σ := Σ) t es e).
Proof. destruct t; apply _. Qed.

Instance val_interp_pers `{hG: !heapG Σ} `{hC: !crashG Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ} es e t:
      Persistent (val_interp (hS := hS) t es e).
Proof.
 revert es e. induction t => ?? //=; try apply _.
 by apply sty_val_persistent.
Qed.

Instance sty_ctx_prop_pers `{hG: !heapG Σ} `{hC: !crashG Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ}
      (Γsubst: gmap string subst_tuple) :
      Persistent ([∗ map] t ∈ Γsubst, val_interp (hS := hS) (subst_ty t) (subst_sval t) (subst_ival t))%I.
Proof.
  apply big_sepM_persistent => ??. by apply val_interp_pers.
Qed.

Existing Instances sty_inv_persistent.

Lemma ctx_has_semTy_subst `{hG: !heapG Σ} `{hC: !crashG Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ}
      e es t x v vs tx Γ:
      ctx_has_semTy (hS := hS) (<[x:=tx]> Γ) es e t -∗
      val_interp (hS := hS) tx vs v -∗
      ctx_has_semTy (hS := hS) Γ (subst' x vs es) (subst' x v e) t.
Proof.
  rewrite /ctx_has_semTy.
  iIntros "Hhasty Hval".
  iIntros (Γsubst Hproj) "Hsty Hspec Htrace Hctx".
  destruct x as [|x] => //=.
  { iApply ("Hhasty" with "[] [$] [$] [$]").
    * rewrite insert_anon //=.
    * eauto.
  }
  rewrite -?subst_map_insert'.
  iSpecialize ("Hhasty" $! (<[x := {| subst_ty := tx; subst_sval := vs; subst_ival := v |}]> Γsubst)
                 with "[] [$] [$] [$] [Hctx Hval]").
  { iPureIntro. rewrite -Hproj. apply: fmap_insert. }
  { iPoseProof (big_sepM_insert_2 with "[Hval] [Hctx]") as "$".
    * iFrame.
    * eauto.
  }
  rewrite ?fmap_insert //=.
Qed.

(* XXX: need to have some ghost resource that enforces that
   the pairing between locs at spec and impl level that's done for arrayT
   and structRefT is one to one, to ensure that pointer equality tests at
   spec/impl level behave correctly *)
Lemma comparableTy_val_eq t vs1 v1 vs2 v2:
  is_comparableTy t = true →
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
  val_interp (hS := hS) t vs1 v1 -∗
  val_interp (hS := hS) t vs2 v2 -∗
  ⌜ v1 = v2 ↔ vs1 = vs2 ⌝.
Proof.
  revert vs1 v1 vs2 v2.
  induction t => vs1 v1 vs2 v2; try (inversion 1; fail).
  - intros. destruct t; iPureIntro; naive_solver.
  - intros (?&?)%andb_prop.
    intros.
    iDestruct 1 as (?? ?? (->&->)) "(H1&H2)".
    iDestruct 1 as (?? ?? (->&->)) "(H1'&H2')".
    rewrite -/val_interp.
    iPoseProof (IHt1 with "H1 H1'") as "%"; eauto.
    iPoseProof (IHt2 with "H2 H2'") as "%"; eauto.
    iPureIntro. naive_solver.
  - intros.
    iDestruct 1 as "[H1|Hnull1]";
    iDestruct 1 as "[H2|Hnull2]";
    rewrite -/val_interp.
    * iDestruct "H1" as (??? (?&?)) "H1".
      iDestruct "H2" as (??? (?&?)) "H2".
      subst.
      admit.
    * admit.
    * admit.
    * admit.
  - admit.
Admitted.

Scheme expr_typing_ind := Induction for expr_transTy Sort Prop with
    val_typing_ind := Induction for val_transTy Sort Prop.

Lemma sty_fundamental_lemma:
  sty_rules_obligation →
  ∀ Γ es e τ, expr_transTy _ _ _ spec_trans Γ es e τ →
  forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
    ⊢ ctx_has_semTy (hS := hS) Γ es e τ.
Proof using spec_trans.
  iIntros (Hrules ???? Htyping).
  induction Htyping using @expr_typing_ind with
      (spec_trans := spec_trans)
      (P := (λ Γ es e τ
             (HTYPE: expr_transTy _ _ _ spec_trans Γ es e τ),
             forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
               ⊢ ctx_has_semTy (hS := hS) Γ es e τ))
      (P0 := (λ Γ vs v τ
             (HTYPE: val_transTy _ _ _ spec_trans Γ vs v τ),
             forall Σ `(hG: !heapG Σ) `(hC: !crashG Σ) `(hRG: !refinement_heapG Σ) (hG': heapG Σ) (hS: styG Σ),
               ⊢ ctx_has_semTy (hS := hS) Γ vs v τ));
    intros ??????; iIntros (Γsubst HPROJ) "#Hinv #Hspec #Htrace #Hctx".
  (* Variables *)
  - subst.
    rewrite lookup_fmap in e.
    apply fmap_Some_1 in e as (t'&?&?). subst.
    iDestruct (big_sepM_lookup with "Hctx") as "H"; first eauto.
    rewrite /= ?lookup_fmap H //=.
    iIntros (j K Hctx) "Hj". iApply wpc_value; iSplit.
    * iModIntro. iExists _; iFrame "H"; iFrame.
    * iModIntro. iApply fupd_mask_weaken; first by set_solver+. eauto.
  (* Function app. *)
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) x2).
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [AppRCtx (subst_map _ f1)] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    wpc_bind (subst_map _ f2).
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [AppLCtx (vs2)] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[Hv2] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    simpl. iDestruct "Hv1" as (?????? (Heq1&Heq2)) "#Hinterp".
    iApply ("Hinterp" with "[$]").
    { iFrame. }
  - iApply (IHHtyping with "[//] [$] [$] [$] [$]").
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
      (* TODO: make spec_ctx auto frame source_ctx *)
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. econstructor; eauto.
      { simpl. econstructor; eauto. }
      { econstructor; eauto. }
    }
    wpc_pures; eauto.
    iExists _; iFrame.
    iExists _, _, _, _, _, _; iSplit; first eauto.
    iLöb as "IH".
    iAlways. iIntros (v vs) "Hval".
    clear j K Hctx.
    iIntros (j K Hctx) "Hj".
    wpc_pures; first auto.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
      (* TODO: make spec_ctx auto frame source_ctx *)
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. econstructor; eauto.
    }
    iPoseProof (ctx_has_semTy_subst with "[] []") as "H1".
    { iApply IHHtyping. }
    { simpl. iExists _, _, _, _, _, _. iFrame "IH"; eauto. }
    iPoseProof (ctx_has_semTy_subst with "[] Hval") as "H2".
    { iApply "H1". }
    iSpecialize ("H2" with "[//] [$] [$] [$] [$] [//] [Hj]").
    { do 2 (rewrite -subst_map_binder_insert' subst_map_binder_insert).
      iEval (rewrite (binder_delete_commute f x)). iFrame. }
    { do 2 (rewrite -subst_map_binder_insert' subst_map_binder_insert).
      iEval (rewrite {2}binder_delete_commute). iFrame. }
  (* Fork *)
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. econstructor; eauto.
    }
    iEval (simpl; rewrite right_id) in "Hchild".
    iDestruct "Hchild" as (j') "Hj'".
    iApply (wpc_fork with "[Hj']").
    { iNext. iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
      iSpecialize ("H" $! j' (λ x, x) with "[] [$]"); first by (iPureIntro; apply language_ctx_id).
      iApply (wpc_mono with "H"); eauto.
    }
    iSplit; first eauto. iNext. iExists _; iFrame; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) cond').
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [IfCtx _ _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.

    iIntros (vcond) "H". iDestruct "H" as (vscond) "(Hj&Hvcond)".
    (* split on the value of the bool *)
    iDestruct "Hvcond" as %(b&->&->).
    destruct b.
    * wpc_pures; first done. simpl.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. econstructor; eauto.
      }
      iApply (IHHtyping2 with "[//] [$] [$] [$] [$]"). eauto.
    * wpc_pures; first done. simpl.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. econstructor; eauto.
      }
      iApply (IHHtyping3 with "[//] [$] [$] [$] [$]"). eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iMod (ghost_step_stuck_det with "Hj []") as %[]; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros; eapply stuck_Panic. }
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iApply wp_wpc.
    iApply wp_fupd.
    iApply wp_ArbitraryInt; auto.
    iNext.
    iIntros. iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. repeat econstructor; eauto.
    }
    iModIntro. iExists _. iFrame. iExists _. iPureIntro; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [UnOpCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u64), ⌜ un_op_eval ToUInt64Op v1 = Some #vres ∧
                            un_op_eval ToUInt64Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wpc_pures; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [UnOpCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u32), ⌜ un_op_eval ToUInt32Op v1 = Some #vres ∧
                            un_op_eval ToUInt32Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wpc_pures; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [UnOpCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u8), ⌜ un_op_eval ToUInt8Op v1 = Some #vres ∧
                            un_op_eval ToUInt8Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wpc_pures; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [UnOpCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: string), ⌜ un_op_eval ToStringOp v1 = Some #(LitString vres) ∧
                            un_op_eval ToStringOp vs1 = Some #(LitString vres) ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply head_prim_step. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wpc_pures; eauto.
  - destruct op; try inversion e; subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [UnOpCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iDestruct "Hv1" as (?) "(%&%)"; subst.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. repeat econstructor; eauto.
    }
    wpc_pures; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [BinOpLCtx EqOp _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply: ectx_lang_ctx; eauto. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    wpc_bind (subst_map _ e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [BinOpRCtx EqOp (vs1)] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[Hv1] [] H"); last done.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply head_prim_step. repeat econstructor; eauto.
    }

    wpc_pures; auto.
    iExists _. iFrame. iExists (bool_decide (vs1 = vs2)); eauto.
    iDestruct (comparableTy_val_eq with "Hv1 Hv2") as %Heq; auto.
    iPureIntro. split; first auto. do 2 f_equal.
    by apply bool_decide_iff.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) _).
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [AppRCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last done.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iPoseProof (Hrules with "[$] [$] [$] [] Hj") as "H"; eauto.
  (* Values *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field
         spec_ffi_interp_adequacy_field.

Section pre_assumptions.

Context `{Hhpre: @heapPreG ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.
Context `{Hcrashpre: crashPreG Σ}.
Context `{Hstypre: !sty_preG Σ}.

Definition sty_derived_crash_condition :=
    (λ (hG: heapG Σ) (hC: crashG Σ) (hRG: refinement_heapG Σ), ∃ hS,
      ▷ ∀ (hG': heapG Σ), |={⊤}=>
      ∀ (hC': crashG Σ) σs,
      (∃ σ0 σ1, ffi_restart (heapG_ffiG) σ1.(world) ∗
      ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ0.(world) (heapG_ffiG (hG := hG')) σ1.(world)) -∗
      ffi_ctx (refinement_spec_ffiG) σs.(world) -∗
      ∃ (σs': sstate) (HCRASH: crash_prim_step (spec_crash_lang) σs σs'),
      ffi_ctx (refinement_spec_ffiG) σs.(world) ∗
      ∀ (hRG': refinement_heapG Σ),
      ffi_crash_rel Σ (refinement_spec_ffiG (hRG := hRG)) σs.(world)
                      (refinement_spec_ffiG (hRG := hRG')) σs'.(world) -∗
      ffi_restart (refinement_spec_ffiG) σs'.(world) -∗
      |={styN}=> ∃ (new: sty_names), sty_init (sty_update Σ hS new))%I.

Lemma sty_inv_to_wpc hG hC hRG hS es e τ j:
  expr_transTy _ _ _ spec_trans ∅ es e τ →
  sty_crash_inv_obligation →
  sty_crash_obligation →
  sty_rules_obligation →
  spec_ctx -∗
  trace_ctx -∗
  sty_init hS -∗
  j ⤇ es -∗
  WPC e @ LVL_INIT; ⊤;⊤ ∖ ↑sN {{ _, True }}{{sty_derived_crash_condition hG hC hRG}}.
Proof.
  iIntros (Htype Hsty_crash_inv Hsty_crash Hsty_rules) "#Hspec #Htrace Hinit Hj".
    rewrite /sty_crash_obligation in Hsty_crash.
  iAssert (|={⊤}=> sty_inv hS ∗ WPC e @ LVL_INIT; ⊤;⊤ ∖ ↑sN ∖ styN {{ _, True }}{{sty_crash_cond hS}})%I with "[-]" as ">(#Hinv&H)".
  {
    rewrite /sty_crash_inv_obligation in Hsty_crash_inv.
    iApply (Hsty_crash_inv with "[$] [$] [Hj]").
    { iIntros "#Hinv'".
      iPoseProof (sty_fundamental_lemma Hsty_rules ∅ _ _ _ Htype) as "H"; eauto.
      iSpecialize ("H" $! ∅ with "[] [$] [$] [$] []").
      { iPureIntro. apply: fmap_empty. }
      { by rewrite big_sepM_empty. }
      rewrite /has_semTy.
      iSpecialize ("H" $! j id with "[] [Hj]").
      { iPureIntro. apply _. }
      { simpl. by rewrite fmap_empty subst_map_empty. }
      rewrite fmap_empty subst_map_empty.
      iApply (wpc_strong_mono _ _ _ _ _ _ _ _ _ _ (λ _, True%I) with "[$]"); eauto.
      iSplit.
      - eauto.
      - eauto. rewrite difference_diag_L.
        simpl. replace (LVL_OPS - LVL_OPS)%nat with O by lia. eauto.
    }
  }
  iApply (wpc_strong_mono with "[$]"); eauto.
  { solve_ndisj. }
  iSplit.
  - eauto.
  - iIntros.
    simpl. replace (LVL_INIT - LVL_INIT)%nat with O by lia. simpl.
    replace (⊤ ∖ ↑sN ∖ (⊤ ∖ ↑sN ∖ styN)) with (styN); last first.
    {
      rewrite difference_difference_remainder_L; auto.
      clear. generalize (styN_disjoint). solve_ndisj.
    }
    iMod (Hsty_crash with "[$] [$]").
    iModIntro. iModIntro. iExists _. iFrame.
Qed.
End pre_assumptions.

Existing Instances subG_cfgG subG_refinement_heapPreG subG_crashG.
Definition logical_relnΣ := #[styΣ; heapΣ; @cfgΣ spec_lang; refinement_heapΣ; crashΣ].

Lemma sty_adequacy es σs e σ τ initP:
  sty_init_obligation1 initP →
  sty_init_obligation2 initP →
  sty_crash_inv_obligation →
  sty_crash_obligation →
  sty_rules_obligation →
  expr_transTy _ _ _ spec_trans ∅ es e τ →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  initP σ σs →
  trace_refines e e σ es es σs.
Proof.
  intros Hsty_init1 Hsty_init2 Hsty_crash_inv Hsty_crash Hsty_rules Htype Htrace Horacle Hinit.
  eapply @heap_wpc_refinement_adequacy with (spec_ext := spec_ext) (Σ := logical_relnΣ)
           (Φ := λ _ _ _ _, True%I) (Φc := sty_derived_crash_condition)
           (k := LVL_INIT) (initP := initP); eauto.
  { apply _. }
  { apply _. }
  { apply _. }
  { apply _. }
  { clear dependent σ σs. rewrite /wpc_init. iIntros (hG hC hRG σ σs Hinit) "Hffi Hffi_spec".
    rewrite /sty_init_obligation1 in Hsty_init1.
    rewrite /wpc_obligation.
    iIntros "Hj #Hspec #Htrace".
    iApply fupd_wpc.
    iPoseProof (Hsty_init1 _ _ _ _  with "[$] [$]") as "H"; first auto.
    iApply (fupd_mask_mono styN); first by set_solver+.
    iMod "H" as (names) "Hinit".
    iModIntro.
    iApply (sty_inv_to_wpc with "[$] [$] [$]"); eauto.
  }
  { clear dependent σ σs.
    rewrite /wpc_post_crash.
    iIntros (???) "H". iDestruct "H" as (hS') "H". iNext.
    iIntros (hG'). iMod ("H" $! hG') as "H". iModIntro.
    iIntros. iSpecialize ("H" with "[$] [$]").
    iDestruct "H" as (σs' Hcrash) "(Hctx&Hrest)".
    iExists σs', Hcrash. iFrame. iIntros (hRG') "Hcrash_rel Hrestart".
    iSpecialize ("Hrest" $! hRG' with "[$] [$]").
    rewrite /wpc_obligation.
    iIntros "Hj #Hspec #Htrace".
    iApply fupd_wpc.
    iApply (fupd_mask_mono styN); first by set_solver+.
    iMod "Hrest" as (names) "Hinv".
    iModIntro.
    iApply (sty_inv_to_wpc _ _ _ (sty_update logical_relnΣ hS' names) with "[$] [$] [$]"); eauto.
  }
  Grab Existential Variables.
  apply subG_styPreG, _.
Qed.


End reln_adeq.

End reln.
