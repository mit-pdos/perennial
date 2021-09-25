From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth frac agree gmap excl csum.
From Perennial.base_logic.lib Require Import proph_map frac_coPset.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation crash_borrow.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy spec_assert.
From Perennial.goose_lang Require Import typing adequacy refinement.
From Perennial.goose_lang Require Export recovery_adequacy spec_assert.

Set Default Proof Using "Type".

Class spec_ffi_interp_adequacy `{spec_ffi: @spec_ffi_interp ffi} `{EXT: !spec_ext_semantics ext ffi} :=
  { spec_ffi_interp_adequacy_field : @ffi_interp_adequacy _ (spec_ffi_interp_field)
                                                          (spec_ffi_op_field)
                                                          (spec_ext_semantics_field) }.

Class refinement_heapPreG `{ext: spec_ffi_op} `{@spec_ffi_interp_adequacy ffi spec_ffi ext EXT} Σ := HeapGpreS {
  refinement_heap_preG_heap :> na_heapGpreS loc (@val spec_ffi_op_field) Σ;
  refinement_heap_preG_ffi : @ffiGpreS (@spec_ffi_model_field ffi)
                                       (@spec_ffi_interp_field _ spec_ffi)
                                       _ _ (spec_ffi_interp_adequacy_field) Σ;
  refinement_heap_preG_trace :> trace_preG Σ;
  refinement_heap_preG_frac :> frac_countG Σ;
  refinement_heap_resv :> inG Σ (frac_coPsetR);
}.

Existing Instances spec_ffi_op_field spec_ext_semantics_field spec_ffi_model_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.
Definition refinement_heapΣ `{ext: spec_ffi_op} `{@spec_ffi_interp_adequacy ffi spec_ffi ext EXT} : gFunctors := #[GFunctor (frac_coPsetR); invΣ; na_heapΣ loc val; ffiΣ; proph_mapΣ proph_id (val * val); traceΣ; frac_countΣ].
Instance subG_refinement_heapPreG `{ext: spec_ffi_op} `{@spec_ffi_interp_adequacy ffi spec_ffi ext EXT} {Σ} :
  subG refinement_heapΣ Σ → refinement_heapPreG Σ.
Proof.
  assert (subG (GFunctor (frac_coPsetR)) Σ → inG Σ frac_coPsetR).
  { solve_inG. }
  solve_inG_deep.
Qed.

Section refinement.
Context {ext: ffi_syntax}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ffi_semantics ext ffi}.
Context `{interp: !ffi_interp ffi}.
Context `{interp_adeq: !ffi_interp_adequacy}.

Context {spec_ext: spec_ffi_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{spec_interp: @spec_ffi_interp spec_ffi}.
Context `{spec_adeq: !spec_ffi_interp_adequacy}.

Context `{Hhpre: @gooseGpreS ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.

Existing Instances spec_ffi_model_field spec_ffi_op_field spec_ext_semantics_field spec_ffi_interp_field
         spec_ffi_interp_adequacy_field.

Lemma goose_spec_init1 {hG: heapGS Σ} r tp0 σ0 g0 tp σ g s tr or P:
  ffi_initgP g →
  ffi_initP σ.(world) g →
  null_non_alloc σ.(heap) →
  neg_non_alloc σ.(heap) →
  σ.(trace) = tr →
  σ.(oracle) = or →
  erased_rsteps (CS := spec_crash_lang) r (tp0, (σ0,g0)) (tp, (σ, g)) s →
  crash_safe (CS := spec_crash_lang) r (tp0, (σ0,g0)) →
  ⊢ trace_frag tr -∗ oracle_frag or -∗
   |={⊤}=> ∃ hR : refinement_heapG Σ, spec_ctx' r (tp0, (σ0,g0)) ∗ source_pool_map (tpool_to_map tp)
                                      ∗ ffi_global_start (refinement_spec_ffiGlobalGS) g
                                      ∗ ffi_local_start (refinement_spec_ffiLocalGS) σ.(world)
                                      ∗ trace_ctx
                                      ∗ spec_crash_ctx' r (tp0, (σ0,g0)) (P hR)
                                      ∗ (|C={⊤}=> trace_inv).
Proof using Hrpre Hcpre.
  iIntros (??? Hnonneg ?? Hsteps Hsafe) "Htr Hor".
  iMod (own_alloc (Cinl 1%Qp)) as (γ) "H".
  { rewrite //=. }
  iMod (source_cfg_init_names1 r tp0 σ0 g0 tp σ g (own γ (Cinl 1%Qp))) as (Hcfg_γ) "(Hsource_ctx&Hpool&Hstate&Hcfupd)"; eauto.
  iMod (na_heap_init tls σ.(heap)) as (Hrheap) "Hrh".
  iMod (ffi_global_init _ (refinement_heap_preG_ffi) g) as (ffi_namesg) "(Hgw&Hgs)"; first by auto.
  iMod (ffi_local_init _ (refinement_heap_preG_ffi) σ.(world))
    as (HffiG) "(Hrw&Hrs)"; first by auto.
  iMod (trace_init σ.(trace) σ.(oracle)) as (HtraceG) "(?&Htr'&?&Hor')".
  set (D := (list_to_set (Z.to_pos <$> (loc_car <$> ((map_to_list σ.(heap)).*1))) : gset positive)).
  iMod (ownfCP_init_fresh_name_finite D) as (γsrv) "Hresv".
  set (HrhG := (refinement_HeapG _ HffiG ffi_namesg HtraceG
                                  {| cfg_name := Hcfg_γ |} Hrheap) _ γ γsrv _).
  iExists HrhG.
  iFrame "Hsource_ctx Hpool Hrs Hcfupd Hgs".
  iMod (ncinv_cinv_alloc (spec_stateN) ⊤ (↑spec_stateN)
                         (∃ (σ0 : language.state goose_lang) g0, (source_state σ0 g0 ∗ spec_assert.spec_interp σ0 g0))
                         (P HrhG ∨ (∃ (σ0 : language.state goose_lang) g0, (source_state σ0 g0 ∗ spec_assert.spec_interp σ0 g0)))%I
                         True%I
            with "[] [-Htr' Hor' Htr Hor]") as "(#Hinv&_&#Hcfupd2)".
  { set_solver. }
  { iModIntro. iIntros "H _". iModIntro; eauto. }
  { iNext. iExists _, _. iFrame. iSplit; first iPureIntro; eauto.
    iExists _; iFrame. iPureIntro.
    intros l Hdom. split.
    * apply Hnonneg. apply elem_of_dom. auto.
    * rewrite /D. rewrite elem_of_gset_to_coPset elem_of_list_to_set elem_of_list_fmap.
      eexists; split; eauto.
      apply elem_of_list_fmap.
      eexists; split; eauto.
      apply elem_of_list_fmap.
      apply elem_of_dom in Hdom as (v&?).
      exists (l, v); split; eauto.
      apply elem_of_map_to_list'; eauto.
  }
  rewrite /trace_ctx.
  iMod (ncinv_alloc (spec_traceN) _ trace_inv with "[-Hcfupd2]") as "($&Hcfupd3)".
  { iNext. subst. rewrite /trace_inv. iExists _, _, _, _. iFrame; eauto. }
  iModIntro. iFrame "Hinv Hcfupd2".
  { iMod (own_disc_fupd_elim with "Hcfupd3") as "Hcfupd3".
    iMod (cfupd_weaken_mask with "Hcfupd3") as "H"; auto.
    iDestruct "H" as ">$".
    eauto. }
Qed.

Lemma goose_spec_init2 {hG: heapGS Σ} r tp σ g tr or P:
  ffi_initgP g →
  ffi_initP σ.(world) g →
  null_non_alloc σ.(heap) →
  neg_non_alloc σ.(heap) →
  σ.(trace) = tr →
  σ.(oracle) = or →
  crash_safe (CS := spec_crash_lang) r (tp, (σ,g)) →
  ⊢ trace_frag tr -∗ oracle_frag or -∗
   |={⊤}=> ∃ hR : refinement_heapG Σ, spec_ctx' r (tp, (σ,g)) ∗ source_pool_map (tpool_to_map tp)
                                     ∗ ffi_global_start (refinement_spec_ffiGlobalGS) g
                                     ∗ ffi_local_start (refinement_spec_ffiLocalGS) σ.(world)
                                     ∗ trace_ctx
                                     ∗ spec_crash_ctx' r (tp, (σ,g)) (P hR)
                                     ∗ (|C={⊤}=> trace_inv).
Proof using Hrpre Hcpre.
  intros; eapply goose_spec_init1; eauto.
  { do 2 econstructor. }
Qed.

Lemma goose_spec_crash_init {hG: gooseGlobalGS Σ} {hL: gooseLocalGS Σ} {hRG: refinement_heapG Σ} r tp0 σ0 g0 tp σ g σ_post_crash s tr or P:
  σ_post_crash.(trace) = tr →
  σ_post_crash.(oracle) = or →
  erased_rsteps (CS := spec_crash_lang) r (tp0, (σ0,g0)) (tp, (σ,g)) s →
  crash_safe (CS := spec_crash_lang) r (tp0, (σ0,g0)) →
  crash_prim_step spec_crash_lang σ σ_post_crash →
  ⊢ trace_frag tr -∗
    oracle_frag or -∗
    ffi_local_ctx refinement_spec_ffiLocalGS (world σ) -∗
    ffi_global_ctx refinement_spec_ffiGlobalGS g -∗
   |={⊤}=> ∃ hRG' : refinement_heapG Σ, spec_ctx' r (tp0, (σ0,g0)) ∗ source_pool_map (tpool_to_map [r])
             ∗ ffi_crash_rel Σ (@refinement_spec_ffiLocalGS _ _ _ _ _ hRG) (world σ)
                               (refinement_spec_ffiLocalGS) (world σ_post_crash)
             ∗ ffi_restart (refinement_spec_ffiLocalGS) (world σ_post_crash)
             ∗ trace_ctx
             ∗ spec_crash_ctx' r (tp0, (σ0,g0)) (P hRG')
             ∗ (|C={⊤}=> trace_inv).
Proof using Hrpre Hcpre.
  iIntros (?? Hsteps Hsafe Hcrash) "Htr Hor Hffi Hffig".
  iMod (own_alloc (Cinl 1%Qp)) as (γ) "H".
  { rewrite //=. }
  iMod (source_cfg_init_names1 r tp0 σ0 g0 [r] σ_post_crash g (own γ (Cinl 1%Qp))) as (Hcfg_γ) "(Hsource_ctx&Hpool&Hstate&Hcfupd)"; eauto.
  { eapply erased_rsteps_r; eauto. econstructor. }
  iMod (na_heap_init tls σ_post_crash.(heap)) as (Hrheap) "Hrh".
  iMod (ffi_crash _ σ.(world) σ_post_crash.(world) with "Hffi")
    as (ffi_names) "(Hrw&Hcrash_rel&Hrs)".
  { inversion Hcrash. subst. eauto. }
  iMod (trace_init σ_post_crash.(trace) σ_post_crash.(oracle)) as (HtraceG) "(?&Htr'&?&Hor')".
  iMod (ownfCP_init_fresh_name_finite ∅) as (γsrv) "Hresv".
  set (HrhG := (refinement_HeapG _ ffi_names refinement_spec_ffiGlobalGS HtraceG
                                 {| cfg_name := Hcfg_γ |} Hrheap) _ γ γsrv _).
  iExists HrhG.
  rewrite /spec_ctx'.  iFrame "Hsource_ctx Hpool Hrs Hcfupd Hcrash_rel".
  iMod (ncinv_cinv_alloc (spec_stateN) ⊤ (↑spec_stateN)
                         (∃ (σ0 : language.state goose_lang) g0, (source_state σ0 g0 ∗ spec_assert.spec_interp σ0 g0))
                         (P HrhG ∨ (∃ (σ0 : language.state goose_lang) g0, (source_state σ0 g0 ∗ spec_assert.spec_interp σ0 g0)))%I
                         True%I
            with "[] [-Htr' Hor' Htr Hor]") as "(#Hinv&_&#Hcfupd2)".
  { set_solver. }
  { iModIntro. iIntros "H _". iModIntro; eauto. }
  { iNext. iExists _, _. iFrame.
    inversion Hcrash. subst.
    simpl. iSplit.
    { iPureIntro => ?. rewrite lookup_empty //. }
    { iExists ∅; iFrame. iPureIntro => ?. rewrite dom_empty_L; inversion 1. }
  }
  rewrite /trace_ctx.
  iMod (ncinv_alloc (spec_traceN) _ trace_inv with "[-Hcfupd2]") as "($&Hcfupd3)".
  { iNext. subst. rewrite /trace_inv. iExists _, _, _, _. iFrame; eauto. }
  iModIntro. iFrame "Hinv Hcfupd2".
  { iMod (own_disc_fupd_elim with "Hcfupd3") as "H".
    iMod (cfupd_weaken_mask with "[$]") as "H"; auto.
    iDestruct "H" as ">$".
    eauto. }
Qed.

Lemma trace_inv_open {hG: gooseGlobalGS Σ} {hL: gooseLocalGS Σ} {hrG: refinement_heapG Σ}  rs es σgs σ:
  spec_ctx' rs ([es], σgs) -∗
  trace_ctx -∗
  trace_auth (trace σ) -∗
  oracle_auth (oracle σ) -∗
  |NC={⊤}=> ⌜∃ (t2s : list expr) (σ2s : state) (g2s : global_state) (stats : status),
            erased_rsteps (CS := spec_crash_lang) rs ([es], σgs) (t2s, (σ2s, g2s)) stats ∧ trace σ2s = trace σ⌝.
Proof.
  iIntros "Hspec Htrace Htrace_auth Horacle_auth".
  rewrite /spec_ctx'.
  iDestruct "Hspec" as "(Hsource&Hspec_state)".
  iInv "Hsource" as "Hsource_open" "Hc1".
  iInv "Hspec_state" as "Hspec_state_open" "Hc2".
  iInv "Htrace" as ">Htrace_open" "Hc3".
  rewrite /source_inv.
  iDestruct "Hsource_open" as (????) "(>Hsource_auth&>(%&%))".
  iDestruct "Hspec_state_open" as (??) "(>Hsource_state&Hspec_interp)".
  iDestruct "Hspec_interp" as "(H1&H2&H3&>Hspec_trace_auth&>Hspec_oracle_auth&Hnull)".
  rewrite /trace_inv.
  iDestruct "Htrace_open" as (???? ??) "(Htrace_frag&Hspec_trace_frag&Horacle_frag&Htspec_oracle_frag)".
  iDestruct (source_state_reconcile with "[$] [$]") as %[Heq0 Heq0'].
  iDestruct (trace_agree with "Htrace_auth [$]") as %Heq1.
  iDestruct (trace_agree with "Hspec_trace_auth [$]") as %Heq2.
  iDestruct (oracle_agree with "Horacle_auth [$]") as %Heq3.
  iDestruct (oracle_agree with "Hspec_oracle_auth [$]") as %Heq4.
  iMod ("Hc3" with "[Htrace_frag Hspec_trace_frag Horacle_frag Htspec_oracle_frag]").
  { iExists _, _, _, _. iFrame. eauto. }
  iMod ("Hc2" with "[Hsource_state H1 H2 H3 Hspec_trace_auth Hspec_oracle_auth Hnull]").
  { iExists _, _. iFrame. }
  iMod ("Hc1" with "[Hsource_auth]").
  { iExists _, _, _. iFrame. eauto. }
  destruct σgs.
  iExists _, _, _, _; iPureIntro; split.
  { eauto. }
  { subst. congruence. }
Qed.

Theorem goose_recv_refinement_adequacy es e rs r σs gs σ g φ φr (Φinv: heapGS Σ → iProp Σ) P n :
  null_non_alloc σs.(heap) →
  neg_non_alloc σs.(heap) →
  ffi_initgP g →
  ffi_initP σ.(world) g →
  ffi_initgP gs →
  ffi_initP σs.(world) gs →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  (∀ `{Hheap : !heapGS Σ} {Href: refinement_heapG Σ},
     ⊢ |={⊤}=>
       (spec_ctx' rs ([es], (σs,gs)) -∗
        trace_ctx -∗
        spec_crash_ctx' rs ([es], (σs,gs)) (P Hheap Href) -∗
        (|C={⊤}=> trace_inv) -∗
       □ (∀ hL, Φinv (HeapGS _ goose_globalGS hL) -∗
                       ∃ Href', spec_ctx' (hR := Href') rs ([es], (σs,gs)) ∗ trace_ctx (hR := Href')) ∗
        (ffi_local_start (goose_ffiLocalGS) σ.(world) -∗ ffi_local_start (refinement_spec_ffiLocalGS) σs.(world) -∗
         pre_borrowN n -∗
         O ⤇ es -∗ wpr NotStuck ⊤ e r (λ v, ⌜φ v⌝) (Φinv) (λ _ v, ⌜φr v⌝)))) →
  trace_refines e r σ g es rs σs gs.
Proof using Hrpre Hhpre Hcpre.
  intros ???????? Hwp Hsafe.
  cut (recv_adequate (CS := goose_crash_lang) NotStuck e r σ g (λ v _ _, φ v) (λ v _ _, φr v)
                     (λ σ2 g2,
                      ∃ t2s σ2s g2s stats,
                        erased_rsteps (CS:= spec_crash_lang) rs ([es], (σs,gs)) (t2s, (σ2s,g2s)) stats ∧
                        σ2s.(trace) = σ2.(trace))); eauto.
  { intros Hrecv.
    split.
    - intros ?????. eapply recv_adequate_not_stuck; eauto.
    - intros tr Hobs. destruct Hobs as (?&?&?&?&Hexec&Htr).
      eapply (recv_adequate_inv _ _ _ _ _ _ _ _ Hrecv) in Hexec.
      subst. destruct Hexec as (t2s&σ2s&g2s&?&Hexecs&Htrs).
      do 3 eexists; eauto.
  }
  eapply (goose_recv_adequacy _ _ _ _ _ _ _ _ _ Φinv); auto.
  iIntros (hG) "???? Hpre".
  iMod (goose_spec_init2 _ _ _ _ _ _ (P _) with "[$] [$]") as
      (HrG) "(#Hspec&Hpool&Hgs&Hrs&#Htrace&Hcfupd1&Hcfupd3)"; try (by symmetry); eauto.
  iMod (Hwp hG HrG with "[$] [$] [$] [$]") as "(#H1&Hwp)".
  iDestruct (source_pool_singleton with "Hpool") as "Hpool".
  iSpecialize ("Hwp" with "[$] [$] [$] [$]").
  iModIntro. iFrame "Hwp". iSplit.
  - iModIntro. iIntros (??) "(Hheap_ctx&Hffi_ctx&Htrace_auth&Horacle_auth)".
    iMod (trace_inv_open with "[$] [$] [$] [$]").
    iApply ncfupd_mask_weaken; eauto.
  - iModIntro. iIntros (hL) "H".
    iDestruct ("H1" $! hL with "H") as (?) "(#Hspec_ctx&#Htrace_ctx)".
    iClear "H1". iModIntro.
    iIntros (??) "(Hheap_ctx&Hffi_ctx&Htrace_auth&Horacle_auth)".
    iMod (@trace_inv_open _ hL with "[$] Htrace_ctx Htrace_auth [$]").
    iApply ncfupd_mask_weaken; eauto.
Qed.

End refinement.

Section refinement_wpc.
Context {ext: ffi_syntax}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ffi_semantics ext ffi}.
Context `{interp: !ffi_interp ffi}.
Context `{interp_adeq: !ffi_interp_adequacy}.

Context {spec_ext: spec_ffi_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{spec_interp: @spec_ffi_interp spec_ffi}.
Context `{spec_adeq: !spec_ffi_interp_adequacy}.

Context `{Hhpre: @gooseGpreS ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.

Existing Instances spec_ffi_model_field spec_ffi_op_field spec_ext_semantics_field spec_ffi_interp_field
         spec_ffi_interp_adequacy_field.


(* This is the core triple that must be proved. There are then two scenarios
   where it has to be shown to hold: from an initial state, and from post-crash
   (assuming Φc on the previous generation) *)

Definition wpc_obligation E e es Φ Φc (hG: gooseGlobalGS Σ) (hL:gooseLocalGS Σ) (hRG: refinement_heapG Σ) P : iProp Σ :=
     (O ⤇ es -∗ spec_ctx -∗ spec_crash_ctx P  -∗ trace_ctx -∗ WPC e @ E {{ Φ hL hRG }} {{ Φc hL hRG }})%I.

Implicit Types initP: @state ext ffi → @state (spec_ffi_op_field) (spec_ffi_model_field) → Prop.

Definition wpc_init E e es Φ Φc initP (P : gooseGlobalGS Σ → gooseLocalGS Σ → refinement_heapG Σ → iProp Σ) n : iProp Σ :=
  (∀ (hG: gooseGlobalGS Σ) (hL:gooseLocalGS Σ) (hRG: refinement_heapG Σ) σ σs,
      ⌜ initP σ σs ⌝ →
      ffi_local_start (goose_ffiLocalGS) σ.(world) -∗
      ffi_local_start (refinement_spec_ffiLocalGS) σs.(world) -∗
      pre_borrowN n -∗
      wpc_obligation E e es Φ (λ hL hRG, Φc hG hL hRG ∗ P hG hL hRG) hG hL hRG (P hG hL hRG))%I.

(* XXX: ffi_restart seems unnecessary, given ffi_crash_rel *)
(* This is very complicated to allow the choice of simulated spec crash step
   to be able to depend on what state the impl crashed to. If spec crah steps
   or impl crash steps are deterministic, there is probably a much simpler defn. *)
Definition wpc_post_crash E e es
    (Φ : gooseLocalGS Σ → refinement_heapG Σ → val → iProp Σ)
    (Φc : gooseGlobalGS Σ → gooseLocalGS Σ → refinement_heapG Σ → iProp Σ)
    (P : gooseGlobalGS Σ → gooseLocalGS Σ → refinement_heapG Σ → iProp Σ)
    (n : nat)
  : iProp Σ
  :=
  (∀ (hG: gooseGlobalGS Σ) (hL:gooseLocalGS Σ) (hRG: refinement_heapG Σ),
      Φc hG hL hRG -∗ ▷ ∀ (hL': gooseLocalGS Σ), |={⊤}=>
      ∀ σs,
      (∃ σ0 σ1, ffi_restart (goose_ffiLocalGS) σ1.(world) ∗
      ffi_crash_rel Σ (goose_ffiLocalGS (hL := hL)) σ0.(world) (goose_ffiLocalGS (hL := hL')) σ1.(world)) -∗
      ffi_local_ctx (refinement_spec_ffiLocalGS) σs.(world) -∗
      ∃ σs' (HCRASH: crash_prim_step (spec_crash_lang) σs σs'),
      ffi_local_ctx (refinement_spec_ffiLocalGS) σs.(world) ∗
      ∀ (hRG': refinement_heapG Σ),
      ffi_crash_rel Σ
                      (refinement_spec_ffiLocalGS (hRG := hRG)) σs.(world)
                      (refinement_spec_ffiLocalGS (hRG := hRG')) σs'.(world) -∗
      ffi_restart (refinement_spec_ffiLocalGS) σs'.(world) -∗
      pre_borrowN n -∗
      wpc_obligation E e es Φ (λ hL hRG, Φc hG hL hRG ∗ P hG hL hRG) hG hL' hRG' (P hG hL' hRG'))%I.

Lemma difference_difference_remainder_L (E1 E2: coPset) :
  E1 ⊆ E2 → (E2 ∖ (E2 ∖ E1)) = E1.
Proof.
  intros Hsub. rewrite (union_difference_L E1 E2 Hsub). set_solver.
Qed.

Lemma wpc_trace_inv_open es σs gs e (hG: gooseGlobalGS Σ) (hL:gooseLocalGS Σ) Href Φ Φc
      `{!Timeless P}:
  □ (P -∗ P -∗ False) -∗
  spec_ctx' es ([es], (σs,gs)) -∗
  trace_ctx -∗
  spec_crash_ctx' es ([es], (σs,gs)) (P) -∗
  (|C={⊤}=> trace_inv) -∗
  WPC e @ ⊤ {{ v, Φ v }}{{Φc Href ∗ P}} -∗
  WPC e @ ⊤ {{ _, True }}{{∃ (hRef : refinement_heapG Σ)
                        (es' : list expr) (σs' : state) (gs' : global_state) (stat : status),
                        ⌜erased_rsteps (CS := spec_crash_lang) es ([es], (σs,gs)) (es', (σs',gs')) stat⌝
                        ∗ ⌜crash_safe (CS := spec_crash_lang) es ([es], (σs,gs))⌝
                        ∗ ▷ ffi_local_ctx refinement_spec_ffiLocalGS (world σs')
                        ∗ ▷ ffi_global_ctx refinement_spec_ffiGlobalGS (gs')
                        ∗ trace_frag (trace σs')
                        ∗ oracle_frag (oracle σs')
                        ∗ Φc hRef}}.
(* FIXME(RJ) this lemma no longer exactly matches what we need below, but we now use some
local mono reasoning -- that seems less fragile than precisely aligning the
statement of this lemma and wpr_idempotence. Can we simplify this lemma further now?
For example, does Φc really need that parameter? *)
Proof.
  iIntros "#Hexcl #Hspec #Htrace #Hcfupd1 Hcfupd2 H".
  iApply (@wpc_strong_mono with "H"); eauto.
  iSplit; first eauto.
  iIntros "(HΦc&HP)".
  iMod ("Hcfupd2") as "Htrace_open".
  iDestruct "Hcfupd1" as "(#Hcinv1&#Hcinv2)".
  rewrite /source_crash_ctx'.
  iMod (cfupd_weaken_mask with "Hcinv1") as "#Hcinv1'"; [ set_solver+ |].
  iMod (cfupd_weaken_mask with "Hcinv2") as "#Hcinv2'"; [ set_solver+ |].
  iInv "Hcinv1'" as ">Hc1" "Hclo1".
  iInv "Hcinv2'" as "Hc2" "Hclo2".
  iDestruct "Hc2" as "[>Hbad|Hc2]".
  { iDestruct ("Hexcl" with "[$] [$]") as %[]. }
  iDestruct "Hc2" as (σs'' gs'') "(>Hspec_state_frag&Hspec_interp)".
  rewrite /spec_assert.spec_interp.
  iDestruct "Hspec_interp" as "(?&?&?&>Hspec_trace_auth&>Hspec_oracle_auth&?&>Hrefinement_ctok&Hresv)".

  iDestruct "Hc1" as "[Hbad|Hc1]".
  { by iDestruct (own_valid_2 with "Hbad Hrefinement_ctok") as %?. }
  iIntros "HC".
  iMod ("Hclo2" with "[HP]") as "_"; eauto.
  iMod ("Hclo1" with "[Hrefinement_ctok]") as "_"; eauto.
  iDestruct "Hc1" as (? es' σs' gs') "(H1&H2)".
  iDestruct "H2" as %(Hexec&Hsafe).
  iDestruct "Htrace_open" as (???? ??) "(Htrace_frag&Hspec_trace_frag&Horacle_frag&Htspec_oracle_frag)".
  iDestruct (source_state_reconcile with "[$] [$]") as %[Heq0' Heq0''].
  iDestruct (trace_agree with "Hspec_trace_auth [$]") as %Heq1'.
  iDestruct (oracle_agree with "Hspec_oracle_auth [$]") as %Heq2'.
  simpl in Hsafe.
  subst. iIntros.
  rewrite /trace_inv.
  iExists _, _, _, _, _.
  iModIntro.
  simpl in Hexec.
  iSplitR; first by eauto.
  iSplitR; first by eauto.
  iFrame.
Qed.

Lemma trace_equiv_preserve_crash σ σ' σs σs':
  trace σs = trace σ →
  crash_prim_step goose_crash_lang σ σ' →
  crash_prim_step spec_crash_lang σs σs' →
  trace σs' = trace σ'.
Proof.
  intros Heq1 Hcrash Hcrash_spec.
  inversion Hcrash; subst.
  inversion Hcrash_spec; subst.
  rewrite //= /add_crash Heq1 //=.
Qed.

Lemma oracle_equiv_preserve_crash σ σ' σs σs':
  oracle σs = oracle σ →
  crash_prim_step goose_crash_lang σ σ' →
  crash_prim_step spec_crash_lang σs σs' →
  oracle σs' = oracle σ'.
Proof.
  intros Heq1 Hcrash Hcrash_spec.
  inversion Hcrash; subst.
  inversion Hcrash_spec; subst.
  rewrite //= Heq1 //=.
Qed.

Definition initP_wf initP :=
  ∀ (σ: @state ext ffi) (g: @global_state ffi)
    (σs: @state (@spec_ffi_op_field spec_ext) (@spec_ffi_model_field spec_ffi))
    (gs: @global_state (@spec_ffi_model_field spec_ffi)),
    initP σ σs → null_non_alloc σs.(heap) ∧ neg_non_alloc σs.(heap) ∧
                 ffi_initP σ.(world) g ∧ ffi_initP σs.(world) gs ∧
                 ffi_initgP g ∧ ffi_initgP gs.

Definition excl_crash_token (P : gooseGlobalGS Σ → gooseLocalGS Σ → refinement_heapG Σ → iProp Σ) :=
  ∀ hG hL Href, (⊢ ((P hG hL Href -∗ P hG hL Href -∗ False))).

Theorem goose_wpc_refinement_adequacy `{crashGpreS Σ} es e
        σs gs σ g Φ Φc initP P n `{∀ hG (hL:gooseLocalGS Σ) hRG, Timeless (P hG hL hRG)} :
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  initP σ σs →
  initP_wf initP →
  excl_crash_token P →
  (⊢ wpc_init ⊤ e es Φ Φc initP P n) →
  (⊢ wpc_post_crash ⊤ e es Φ Φc P n) →
  trace_refines e e σ g es es σs gs.
Proof using Hrpre Hhpre Hcpre.
  intros Heq1 Heq2 Hinit Hinit_wf Hexcl Hwp_init Hwp_crash.
  eapply goose_recv_refinement_adequacy with
      (φ := λ _, True) (φr := λ _, True)
      (n0 := (n + n)%nat)
      (Φinv := λ hG,
               (
                         ∃ Href' : refinement_heapG Σ, spec_ctx' es ([es], (σs,gs))
                                                                 ∗ trace_ctx)%I); eauto.
  { eapply Hinit_wf; eauto. }
  { eapply Hinit_wf; eauto. }
  { eapply Hinit_wf; eauto. }
  { eapply Hinit_wf; eauto. }
  { eapply Hinit_wf; eauto. }
  { eapply Hinit_wf; eauto. }
  iIntros (Hheap Href).
  iModIntro. iIntros "#Hspec #Htrace #Hcfupd1 Hcfupd3".
  iSplit.
  { iModIntro. iIntros (?) "H". iApply "H". }
  iIntros "Hstart Hstart_spec Hpre Hj".

  (* Create an invariant that will store pre_borrowN n. This is a silly trick
     to let us argue after the crash that the global step count must be at least n,
     which is how we can justify re-generating pre_borrowN n again. *)
  iDestruct (pre_borrowN_split with "Hpre") as "(Hpre&Hpre_inv)".
  iApply fupd_wpr.
  iMod (inv_alloc (nroot.@"pre") with "Hpre_inv") as "#Hpre_inv".
  iModIntro.


  iApply (recovery_weakestpre.idempotence_wpr _ _ ⊤ _ _ (λ _, _) _ _ (λ hGen,
   ∃ hL hRef, ∃ es' σs' gs' stat, 
         ⌜ hGen = goose_generationGS (L:=hL) ⌝ ∗
         ⌜ erased_rsteps es ([es], (σs,gs)) (es', (σs',gs')) stat ⌝ ∗
         ⌜ crash_safe es ([es], (σs,gs)) ⌝ ∗
         ▷ ffi_local_ctx (refinement_spec_ffiLocalGS) σs'.(world) ∗
         ▷ ffi_global_ctx (refinement_spec_ffiGlobalGS) gs' ∗
         trace_frag (trace σs') ∗ oracle_frag (oracle σs')
                (* spec_ctx' es ([es], σs) ∗ trace_ctx *) ∗  Φc _ hL hRef)%I with "[-]")%I.
  - rewrite /wpc_init/wpc_obligation in Hwp_init.
    iPoseProof (Hwp_init with "[//] [$] [$] [$] [$] [] [] [$]") as "H".
    { rewrite /spec_ctx/spec_ctx'.
      iDestruct "Hspec" as "(H1&$)".
      iExists _, _. iFrame "H1".
    }
    { rewrite /spec_crash_ctx/spec_crash_ctx'/source_crash_ctx.
      iSplitL.
      { iExists _, _. iDestruct "Hcfupd1" as "($&_)". }
      iDestruct "Hcfupd1" as "(_&$)".
    }
    iApply (wpc_crash_mono).
    2:{ iApply (wpc_trace_inv_open with "[] Hspec Htrace Hcfupd1 Hcfupd3 H").
        iApply Hexcl. }
    iIntros "H". iDestruct "H" as (?????) "H".
    iExists _, _, _, _, _, _. iSplit; first done. iExact "H".
  - iModIntro. iClear "Hspec Htrace".
    iIntros (? σ_pre_crash g_pre_crash σ_post_crash Hcrash ns κs ?).
    iIntros (κs' ?).
    iIntros "H". iDestruct "H" as (?? es' σs' gs' stat -> Hexec Hsafe)
                                    "(Hspec_ffi&Hspec_gffi&Htrace_frag&Horacle_frag&HΦc)".
    iIntros "(_&Hffi_old&Htrace_auth&Horacle_auth) Hg".
    iDestruct (trace_agree with "Htrace_auth [$]") as %Heq1'.
    iDestruct (oracle_agree with "Horacle_auth Horacle_frag") as %Heq2'.
    iInv "Hpre_inv" as ">H" "Hclo".
    iDestruct (pre_borrowN_global_interp_le _ _ _ _ _ κs' with "[$] [Hg]") as %Hle.
    { rewrite //=. }
    iMod ("Hclo" with "[$]") as "_".
    iModIntro.
    iPoseProof (@Hwp_crash $! _ _ with "HΦc") as "H".
    iNext. iIntros.
    iMod (na_heap.na_heap_reinit _ tls σ_post_crash.(heap)) as (name_na_heap) "Hh".
    iDestruct "Hg" as "(Hffig&Hg)".
    iMod (ffi_crash _ σ_pre_crash.(world) σ_post_crash.(world) with "Hffi_old") as (ffi_names) "(Hw&Hcrel&Hc)".
    { inversion Hcrash; subst; eauto. }
    iMod (trace_reinit _ σ_post_crash.(trace) σ_post_crash.(oracle)) as (name_trace) "(Htr&Htrfrag&Hor&Hofrag)".
    set (hL' := GooseLocalGS _ Hc ffi_names (na_heapGS_update _ name_na_heap) (traceGS_update Σ _ name_trace)).
    iSpecialize ("H" $! hL').
    iExists (goose_generationGS (L:=hL')).
    iSplitR; first done.
    iMod "H".
    iSpecialize ("H" with "[Hc Hcrel] [$]").
    {  simpl. iExists _, _. iFrame. }
    iDestruct "H" as (σs_post_crash Hspec_crash) "(Hspec_ffi&Hwpc)".
    iClear "Htrace_auth Horacle_auth Htrace_frag Horacle_frag".
    iMod (goose_spec_crash_init (hL:=hL') _ _ σs gs _ σs' gs' σs_post_crash _ (trace σ_post_crash) (oracle σ_post_crash)
            with "[$] [$] Hspec_ffi Hspec_gffi") as (HrG) "(#Hspec&Hpool&Hcrash_rel&Hrs&#Htrace&#Hcfupd1'&Hcfupd3)";
      eauto.
    { eapply trace_equiv_preserve_crash; eauto. }
    { eapply oracle_equiv_preserve_crash; eauto. }
    iDestruct "Hg" as "(Hb_ginv&Hc&Hp)".
    iMod (cred_interp_incr_k _ (9 * ns + 10) with "Hc") as "(Hc&Hfrag)".
    assert (∃ n0 : nat, 9 * ns + 10 = n * 4 + n0)%nat as (n0'&Heqn0').
    { exists (9 * ns + 10 - 4 * n)%nat. lia. }
    iEval (rewrite Heqn0') in "Hfrag".
    iDestruct (cred_frag_split with "Hfrag") as "(Hfrag&_)".
    iDestruct (cred_frag_to_pre_borrowN with "Hfrag") as "Hpre".
    iModIntro.
    rewrite /state_interp//=.
    iFrame.
    iSplitL "Hc".
    { iExactEq "Hc". f_equal. lia. }
    iSplit.
    + iClear "∗". eauto.
    + iDestruct (source_pool_singleton with "Hpool") as "Hpool".
      iDestruct ("Hwpc" with "[$] [$] [$] [$] [] [] [$]") as "H".
      { rewrite /spec_ctx/spec_ctx'.
        iDestruct "Hspec" as "(H1&$)".
        iExists _, _. iFrame "H1".
      }
      { rewrite /spec_crash_ctx/spec_crash_ctx'/source_crash_ctx.
        iSplitL.
        { iExists _, _. iDestruct "Hcfupd1'" as "($&_)". }
        iDestruct "Hcfupd1'" as "(_&$)".
      }
      iPoseProof (wpc_trace_inv_open _ _ _ e _ hL' _ (Φ hL' _) (Φc _ hL') with "[] Hspec Htrace Hcfupd1' Hcfupd3 H") as "H".
      { iApply Hexcl. }
      iApply (wpc_mono with "H").
      * naive_solver.
      * iIntros "H". iDestruct "H" as (?????) "H".
        iExists _, _, _, _, _, _. iSplit; first done. iExact "H".
Qed.

End refinement_wpc.
