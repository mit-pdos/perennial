From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth frac agree gmap excl csum.
From Perennial.base_logic.lib Require Import proph_map.
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
  refinement_heap_preG_heap :> na_heapPreG loc (@val spec_ffi_op_field) Σ;
  refinement_heap_preG_ffi : @ffi_preG (@spec_ffi_model_field ffi)
                                       (@spec_ffi_interp_field _ spec_ffi)
                                       _ _ (spec_ffi_interp_adequacy_field) Σ;
  refinement_heap_preG_trace :> trace_preG Σ;
  refinement_heap_preG_frac :> frac_countG Σ;
}.

Existing Instances spec_ffi_op_field spec_ext_semantics_field spec_ffi_model_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.
Definition refinement_heapΣ `{ext: spec_ffi_op} `{@spec_ffi_interp_adequacy ffi spec_ffi ext EXT} : gFunctors := #[invΣ; na_heapΣ loc val; ffiΣ; proph_mapΣ proph_id (val * val); traceΣ; frac_countΣ].
Instance subG_refinement_heapPreG `{ext: spec_ffi_op} `{@spec_ffi_interp_adequacy ffi spec_ffi ext EXT} {Σ} :
  subG refinement_heapΣ Σ → refinement_heapPreG Σ.
Proof. solve_inG_deep. Qed.

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

Context `{Hhpre: @heapGpreS ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.

Existing Instances spec_ffi_model_field spec_ffi_op_field spec_ext_semantics_field spec_ffi_interp_field
         spec_ffi_interp_adequacy_field.

Lemma goose_spec_init1 {hG: heapGS Σ} r tp0 σ0 g0 tp σ g s tr or P:
  ffi_initgP g →
  ffi_initP σ.(world) g →
  null_non_alloc σ.(heap) →
  σ.(trace) = tr →
  σ.(oracle) = or →
  erased_rsteps (CS := spec_crash_lang) r (tp0, (σ0,g0)) (tp, (σ, g)) s →
  crash_safe (CS := spec_crash_lang) r (tp0, (σ0,g0)) →
  ⊢ trace_frag tr -∗ oracle_frag or -∗
   |={⊤}=> ∃ hR : refinement_heapG Σ, spec_ctx' r (tp0, (σ0,g0)) ∗ source_pool_map (tpool_to_map tp)
                                      ∗ ffi_local_start (refinement_spec_ffiG) σ.(world) g
                                      ∗ trace_ctx
                                      ∗ spec_crash_ctx' r (tp0, (σ0,g0)) (P hR)
                                      ∗ <disc> (|C={⊤}_0=> trace_inv).
Proof using Hrpre Hcpre.
  iIntros (????? Hsteps Hsafe) "Htr Hor".
  iMod (own_alloc (Cinl 1%Qp)) as (γ) "H".
  { rewrite //=. }
  iMod (source_cfg_init_names1 r tp0 σ0 g0 tp σ g (own γ (Cinl 1%Qp))) as (Hcfg_γ) "(Hsource_ctx&Hpool&Hstate&Hcfupd)"; eauto.
  iMod (na_heap_init tls σ.(heap)) as (Hrheap) "Hrh".
  iMod (ffi_name_global_init _ (refinement_heap_preG_ffi) g) as (ffi_namesg) "(Hgw&_)"; first auto.
  iMod (ffi_name_init _ (refinement_heap_preG_ffi) σ.(world) g with "Hgw")
    as (HffiG) "(Hrw&Hrg&Hrs)"; first auto.
  iMod (trace_init σ.(trace) σ.(oracle)) as (HtraceG) "(?&Htr'&?&Hor')".
  set (HrhG := (refinement_HeapG _ (ffi_update_pre _ (refinement_heap_preG_ffi) HffiG ffi_namesg) HtraceG
                                  {| cfg_name := Hcfg_γ |} Hrheap) _ γ).
  iExists HrhG.
  iFrame "Hsource_ctx Hpool Hrs Hcfupd".
  iMod (ncinv_cinv_alloc (spec_stateN) 0 ⊤ (↑spec_stateN)
                         (∃ (σ0 : language.state goose_lang) g0, (source_state σ0 g0 ∗ spec_assert.spec_interp σ0 g0))
                         (P HrhG ∨ (∃ (σ0 : language.state goose_lang) g0, (source_state σ0 g0 ∗ spec_assert.spec_interp σ0 g0)))%I
                         True%I
            with "[] [-Htr' Hor' Htr Hor]") as "(#Hinv&_&#Hcfupd2)".
  { set_solver. }
  { iModIntro. iIntros "H _". iModIntro; eauto. }
  { iNext. iExists _, _. iFrame. iPureIntro; eauto. }
  rewrite /trace_ctx.
  iMod (ncinv_alloc (spec_traceN) _ trace_inv with "[-Hcfupd2]") as "($&Hcfupd3)".
  { iNext. subst. rewrite /trace_inv. iExists _, _, _, _. iFrame; eauto. }
  iModIntro. iFrame "Hinv Hcfupd2".
  { iModIntro. iMod (cfupd_weaken_all with "[$]") as "H"; auto. iDestruct "H" as ">$". eauto. }
  Unshelve. exact O.
Qed.

Lemma goose_spec_init2 {hG: heapGS Σ} r tp σ g tr or P:
  ffi_initgP g →
  ffi_initP σ.(world) g →
  null_non_alloc σ.(heap) →
  σ.(trace) = tr →
  σ.(oracle) = or →
  crash_safe (CS := spec_crash_lang) r (tp, (σ,g)) →
  ⊢ trace_frag tr -∗ oracle_frag or -∗
   |={⊤}=> ∃ hR : refinement_heapG Σ, spec_ctx' r (tp, (σ,g)) ∗ source_pool_map (tpool_to_map tp)
                                     ∗ ffi_local_start (refinement_spec_ffiG) σ.(world) g
                                     ∗ trace_ctx
                                     ∗ spec_crash_ctx' r (tp, (σ,g)) (P hR)
                                     ∗ <disc> (|C={⊤}_0=> trace_inv).
Proof using Hrpre Hcpre.
  intros; eapply goose_spec_init1; eauto.
  { do 2 econstructor. }
Qed.

Lemma goose_spec_crash_init {hG: heapGS Σ} {hRG: refinement_heapG Σ} r tp0 σ0 g0 tp σ g σ_post_crash s tr or P:
  σ_post_crash.(trace) = tr →
  σ_post_crash.(oracle) = or →
  erased_rsteps (CS := spec_crash_lang) r (tp0, (σ0,g0)) (tp, (σ,g)) s →
  crash_safe (CS := spec_crash_lang) r (tp0, (σ0,g0)) →
  crash_prim_step spec_crash_lang σ σ_post_crash →
  ⊢ trace_frag tr -∗
    oracle_frag or -∗
    ffi_ctx refinement_spec_ffiG (world σ) -∗
    ffi_global_ctx refinement_spec_ffiG g -∗
   |={⊤}=> ∃ hRG' : refinement_heapG Σ, spec_ctx' r (tp0, (σ0,g0)) ∗ source_pool_map (tpool_to_map [r])
             ∗ ffi_crash_rel Σ (@refinement_spec_ffiG _ _ _ _ _ hRG) (world σ)
                               (refinement_spec_ffiG) (world σ_post_crash)
             ∗ ffi_restart (refinement_spec_ffiG) (world σ_post_crash)
             ∗ trace_ctx
             ∗ spec_crash_ctx' r (tp0, (σ0,g0)) (P hRG')
             ∗ <disc> (|C={⊤}_0=> trace_inv).
Proof using Hrpre Hcpre.
  iIntros (?? Hsteps Hsafe Hcrash) "Htr Hor Hffi Hffig".
  iMod (own_alloc (Cinl 1%Qp)) as (γ) "H".
  { rewrite //=. }
  iMod (source_cfg_init_names1 r tp0 σ0 g0 [r] σ_post_crash g (own γ (Cinl 1%Qp))) as (Hcfg_γ) "(Hsource_ctx&Hpool&Hstate&Hcfupd)"; eauto.
  { eapply erased_rsteps_r; eauto. econstructor. }
  iMod (na_heap_init tls σ_post_crash.(heap)) as (Hrheap) "Hrh".
  iMod (ffi_crash _ σ.(world) σ_post_crash.(world) with "Hffi Hffig")
    as (ffi_names) "(Hrw&Hrg&Hcrash_rel&Hrs)".
  { inversion Hcrash. subst. eauto. }
  iMod (trace_init σ_post_crash.(trace) σ_post_crash.(oracle)) as (HtraceG) "(?&Htr'&?&Hor')".
  set (HrhG := (refinement_HeapG _ (ffi_update_local Σ (refinement_spec_ffiG) ffi_names) HtraceG
                                 {| cfg_name := Hcfg_γ |} Hrheap) _ γ).
  iExists HrhG.
  rewrite /spec_ctx'.  iFrame "Hsource_ctx Hpool Hrs Hcfupd Hcrash_rel".
  iMod (ncinv_cinv_alloc (spec_stateN) 0 ⊤ (↑spec_stateN)
                         (∃ (σ0 : language.state goose_lang) g0, (source_state σ0 g0 ∗ spec_assert.spec_interp σ0 g0))
                         (P HrhG ∨ (∃ (σ0 : language.state goose_lang) g0, (source_state σ0 g0 ∗ spec_assert.spec_interp σ0 g0)))%I
                         True%I
            with "[] [-Htr' Hor' Htr Hor]") as "(#Hinv&_&#Hcfupd2)".
  { set_solver. }
  { iModIntro. iIntros "H _". iModIntro; eauto. }
  { iNext. iExists _, _. iFrame.
    inversion Hcrash. subst. simpl. iPureIntro => ?. rewrite lookup_empty //. }
  rewrite /trace_ctx.
  iMod (ncinv_alloc (spec_traceN) _ trace_inv with "[-Hcfupd2]") as "($&Hcfupd3)".
  { iNext. subst. rewrite /trace_inv. iExists _, _, _, _. iFrame; eauto. }
  iModIntro. iFrame "Hinv Hcfupd2".
  { iModIntro. iMod (cfupd_weaken_all with "[$]") as "H"; auto. iDestruct "H" as ">$". eauto. }
  Unshelve. exact O.
Qed.

Lemma trace_inv_open {hG: heapGS Σ} {hrG: refinement_heapG Σ}  rs es σgs σ:
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

Theorem heap_recv_refinement_adequacy k es e rs r σs gs σ g φ φr (Φinv: heapGS Σ → iProp Σ) P n :
  null_non_alloc σs.(heap) →
  ffi_initgP g →
  ffi_initP σ.(world) g →
  ffi_initgP gs →
  ffi_initP σs.(world) gs →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  (∀ `{Hheap : !heapGS Σ} {Href: refinement_heapG Σ}
    (* (HPF: ∃ Hi' Ht', Hheap = heap_update_pre _ _ Hi' (@pbundleT _ Σ Ht') *),
     ⊢ |={⊤}=>
       (spec_ctx' rs ([es], (σs,gs)) -∗
        trace_ctx -∗
        spec_crash_ctx' rs ([es], (σs,gs)) (P Hheap Href) -∗
        <disc> (|C={⊤}_0=> trace_inv) -∗
       □ (∀ hG, Φinv hG -∗
                       ∃ Href', spec_ctx' (hR := Href') rs ([es], (σs,gs)) ∗ trace_ctx (hR := Href')) ∗
        (ffi_local_start (heapG_ffiG) σ.(world) g -∗ ffi_local_start (refinement_spec_ffiG) σs.(world) gs -∗
         pre_borrowN n -∗
         O ⤇ es -∗ wpr NotStuck k ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ v, ⌜φr v⌝)))) →
  trace_refines e r σ g es rs σs gs.
Proof using Hrpre Hhpre Hcpre.
  intros ??????? Hwp Hsafe.
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
  eapply (heap_recv_adequacy _ _ _ _ _ _ _ _ _ _ Φinv); auto.
  iIntros (hG) "??? Hpre".
  iMod (goose_spec_init2 _ _ _ _ _ _ (P _) with "[$] [$]") as
      (HrG) "(#Hspec&Hpool&Hrs&#Htrace&Hcfupd1&Hcfupd3)"; try (by symmetry); eauto.
  iMod (Hwp hG HrG with "[$] [$] [$] [$]") as "(#H1&Hwp)".
  iDestruct (source_pool_singleton with "Hpool") as "Hpool".
  iSpecialize ("Hwp" with "[$] [$] [$] [$]").
  iModIntro. iFrame "Hwp". iSplit.
  - iModIntro. iIntros (??) "(Hheap_ctx&Hffi_ctx&Htrace_auth&Horacle_auth)".
    iMod (trace_inv_open with "[$] [$] [$] [$]").
    iApply ncfupd_mask_weaken; eauto.
  - iModIntro. iIntros (??) "H".
    iDestruct ("H1" with "H") as (?) "(#Hspec_ctx&#Htrace_ctx)".
    iClear "H1". iModIntro.
    iIntros (??) "(Hheap_ctx&Hffi_ctx&Htrace_auth&Horacle_auth)".
    iMod (@trace_inv_open with "[$] [$] [$] [$]").
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

Context `{Hhpre: @heapGpreS ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.

Existing Instances spec_ffi_model_field spec_ffi_op_field spec_ext_semantics_field spec_ffi_interp_field
         spec_ffi_interp_adequacy_field.


(* This is the core triple that must be proved. There are then two scenarios
   where it has to be shown to hold: from an initial state, and from post-crash
   (assuming Φc on the previous generation) *)

Definition wpc_obligation k E e es Φ Φc (hG: heapGS Σ) (hRG: refinement_heapG Σ) P : iProp Σ :=
     (O ⤇ es -∗ spec_ctx -∗ spec_crash_ctx P  -∗ trace_ctx -∗ WPC e @ NotStuck; k; E {{ Φ hG hRG }} {{ Φc hG hRG }})%I.

Implicit Types initP: @state ext ffi → @state (spec_ffi_op_field) (spec_ffi_model_field) → Prop.

Definition wpc_init k E e es Φ Φc initP P n : iProp Σ :=
  (∀ (hG: heapGS Σ) (hRG: refinement_heapG Σ) σ g σs gs,
      ⌜ initP σ σs ⌝ →
      ffi_local_start (heapG_ffiG) σ.(world) g -∗
      ffi_local_start (refinement_spec_ffiG) σs.(world) gs -∗
      pre_borrowN n -∗
      wpc_obligation k E e es Φ (λ hG hRG, Φc hG hRG ∗ P hG hRG) hG hRG (P hG hRG))%I.

(* XXX: ffi_restart seems unnecessary, given ffi_crash_rel *)
(* This is very complicated to allow the choice of simulated spec crash step
   to be able to depend on what state the impl crashed to. If spec crah steps
   or impl crash steps are deterministic, there is probably a much simpler defn. *)
Definition wpc_post_crash k E e es Φ Φc P n : iProp Σ :=
  (∀ (hG: heapGS Σ) (hRG: refinement_heapG Σ),
      Φc hG hRG -∗ ▷ ∀ (hG': heapGS Σ), |={⊤}=>
      ∀ σs,
      (∃ σ0 σ1, ffi_restart (heapG_ffiG) σ1.(world) ∗
      ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ0.(world) (heapG_ffiG (hG := hG')) σ1.(world)) -∗
      ffi_ctx (refinement_spec_ffiG) σs.(world) -∗
      ∃ σs' (HCRASH: crash_prim_step (spec_crash_lang) σs σs'),
      ffi_ctx (refinement_spec_ffiG) σs.(world) ∗
      ∀ (hRG': refinement_heapG Σ),
      ffi_crash_rel Σ
                      (refinement_spec_ffiG (hRG := hRG)) σs.(world)
                      (refinement_spec_ffiG (hRG := hRG')) σs'.(world) -∗
      ffi_restart (refinement_spec_ffiG) σs'.(world) -∗
      pre_borrowN n -∗
      wpc_obligation k E e es Φ (λ hG hRG, Φc hG hRG ∗ P hG hRG) hG' hRG' (P hG' hRG'))%I.

Lemma difference_difference_remainder_L (E1 E2: coPset) :
  E1 ⊆ E2 → (E2 ∖ (E2 ∖ E1)) = E1.
Proof.
  intros Hsub. rewrite (union_difference_L E1 E2 Hsub). set_solver.
Qed.

Lemma wpc_trace_inv_open k es σs gs e Hheap Href Φ Φc
      `{∀ hG hRG, Timeless (P hG hRG)}:
  □ (P Hheap Href -∗ P Hheap Href -∗ False) -∗
  spec_ctx' es ([es], (σs,gs)) -∗
  trace_ctx -∗
  spec_crash_ctx' es ([es], (σs,gs)) (P Hheap Href) -∗
  (|C={⊤}_0=> trace_inv) -∗
  WPC e @ k; ⊤ {{ v, Φ Hheap Href v }}{{Φc Hheap Href ∗ P Hheap Href}} -∗
  WPC e @ k; ⊤ {{ _, True }}{{∃ (hC : crashG Σ) (hRef : refinement_heapG Σ)
                        (es' : list expr) (σs' : state) (gs' : global_state) (stat : status),
                        ⌜erased_rsteps (CS := spec_crash_lang) es ([es], (σs,gs)) (es', (σs',gs')) stat⌝
                        ∗ ⌜crash_safe (CS := spec_crash_lang) es ([es], (σs,gs))⌝
                        ∗ ▷ ffi_ctx refinement_spec_ffiG (world σs')
                        ∗ ▷ ffi_global_ctx refinement_spec_ffiG (gs')
                        ∗ trace_frag (trace σs')
                        ∗ oracle_frag (oracle σs')
                        ∗ Φc (heap_update_local Σ Hheap _ hC (heap_get_local_names Σ Hheap)) hRef}}.
Proof.
  iIntros "#Hexcl #Hspec #Htrace #Hcfupd1 Hcfupd2 H".
  iApply (@wpc_strong_mono with "H"); eauto.
  iSplit; first eauto.
  iIntros "(HΦc&HP)".
  iMod ("Hcfupd2") as "Htrace_open"; first lia.
  iDestruct "Hcfupd1" as "(#Hcinv1&#Hcinv2)".
  rewrite /source_crash_ctx'.
  iMod (cfupd_weaken_all with "Hcinv1") as "#Hcinv1'"; [ lia | set_solver+ |].
  iMod (cfupd_weaken_all with "Hcinv2") as "#Hcinv2'"; [ lia | set_solver+ |].
  iInv "Hcinv1'" as ">Hc1" "Hclo1".
  iInv "Hcinv2'" as "Hc2" "Hclo2".
  iDestruct "Hc2" as "[>Hbad|Hc2]".
  { iDestruct ("Hexcl" with "[$] [$]") as %[]. }
  iDestruct "Hc2" as (σs'' gs'') "(>Hspec_state_frag&Hspec_interp)".
  rewrite /spec_assert.spec_interp.
  iDestruct "Hspec_interp" as "(?&?&?&>Hspec_trace_auth&>Hspec_oracle_auth&?&>Hrefinement_ctok)".

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
  iExists _, _, _, _, _, _.
  iModIntro.
  simpl in Hexec.
  iSplitR; first by eauto.
  iSplitR; first by eauto.
  rewrite heap_get_update'.
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
    initP σ σs → null_non_alloc σs.(heap) ∧ ffi_initP σ.(world) g ∧ ffi_initP σs.(world) gs ∧
                 ffi_initgP g ∧ ffi_initgP gs.

Definition excl_crash_token (P : heapGS Σ → refinement_heapG Σ → iProp Σ) :=
  ∀ Hheap Href, (⊢ ((P Hheap Href -∗ P Hheap Href -∗ False))).

Theorem heap_wpc_refinement_adequacy `{crashPreG Σ} k es e
        σs gs σ g Φ Φc initP P n `{∀ hG hRG, Timeless (P hG hRG)} :
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  initP σ σs →
  initP_wf initP →
  excl_crash_token P →
  (⊢ wpc_init k ⊤ e es Φ Φc initP P n) →
  (⊢ wpc_post_crash k ⊤ e es Φ Φc P n) →
  trace_refines e e σ g es es σs gs.
Proof using Hrpre Hhpre Hcpre.
  intros Heq1 Heq2 Hinit Hinit_wf Hexcl Hwp_init Hwp_crash.
  eapply heap_recv_refinement_adequacy with
      (k0 := k)
      (φ := λ _, True) (φr := λ _, True)
      (n0 := (n + n)%nat)
      (Φinv := λ hG,
               (* (∀  Hheap  (HPF: ∃ Hi' Ht', Hheap = heap_update_pre _ _ Hi' (@pbundleT _ _ Ht') ) *)
               (
                         ∃ Href' : refinement_heapG Σ, spec_ctx' es ([es], (σs,gs))
                                                                 ∗ trace_ctx)%I); eauto.
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


  iApply (recovery_weakestpre.idempotence_wpr _ _ ⊤ _ _ (λ _ _, _) _ _ (λ Hc0 t,
   ∃ hC hRef, let hG := heap_update_local Σ Hheap _ hC pbundleT in
                 ∃ es' σs' gs' stat, ⌜ erased_rsteps es ([es], (σs,gs)) (es', (σs',gs')) stat ⌝ ∗
                                 ⌜ crash_safe es ([es], (σs,gs)) ⌝ ∗
                                ▷ ffi_ctx (refinement_spec_ffiG) σs'.(world) ∗
                                ▷ ffi_global_ctx (refinement_spec_ffiG) gs' ∗
                                trace_frag (trace σs') ∗ oracle_frag (oracle σs')
                (* spec_ctx' es ([es], σs) ∗ trace_ctx *) ∗  Φc hG hRef)%I with "[-]")%I.
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
    rewrite /perennial_irisG. simpl.
    rewrite heap_get_update'.
    iMod (own_disc_fupd_elim with "Hcfupd3") as "Hcfupd3".
    iApply (wpc_trace_inv_open with "[] Hspec Htrace Hcfupd1 Hcfupd3 H").
    { iApply Hexcl. }
  - iModIntro. iClear "Hspec Htrace".
    iIntros (?? σ_pre_crash g_pre_crash σ_post_crash Hcrash ns κs ?).
    iIntros (κs' ?).
    iIntros "H". iDestruct "H" as (?? es' σs' gs' stat Hexec Hsafe)
                                    "(Hspec_ffi&Hspec_gffi&Htrace_frag&Horacle_frag&HΦc)".
    iIntros "(_&Hffi_old&Htrace_auth&Horacle_auth) Hg".
    iDestruct (trace_agree with "Htrace_auth [$]") as %Heq1'.
    iDestruct (oracle_agree with "Horacle_auth Horacle_frag") as %Heq2'.
    iInv "Hpre_inv" as ">H" "Hclo".
    iDestruct (pre_borrowN_global_interp_le _ _ _ _ _ κs' with "[$] [Hg]") as %Hle.
    { rewrite //=. rewrite ffi_global_ctx_nolocal. iFrame. }
    iMod ("Hclo" with "[$]") as "_".
    iModIntro.
    iPoseProof (@Hwp_crash $! _ _ with "HΦc") as "H".
    iNext. iIntros.
    iMod (na_heap.na_heap_reinit _ tls σ_post_crash.(heap)) as (name_na_heap) "Hh".
    iDestruct "Hg" as "(Hffig&Hg)".
    iMod (ffi_crash _ σ_pre_crash.(world) σ_post_crash.(world) g_pre_crash with "Hffi_old Hffig") as (ffi_names) "(Hw&Hffig&Hcrel&Hc)".
    { inversion Hcrash; subst; eauto. }
    iMod (trace_reinit _ σ_post_crash.(trace) σ_post_crash.(oracle)) as (name_trace) "(Htr&Htrfrag&Hor&Hofrag)".
    set (hnames := {| heap_local_heap_names := name_na_heap;
                      heap_local_ffi_local_names := ffi_names;
                      heap_local_trace_names := name_trace |}).
    set (hG := (heap_update_local _ _ _ _ hnames)).
    iSpecialize ("H" $! hG).
    simpl.
    rewrite /hG.
    rewrite heap_update_invG.
    rewrite heap_update_invG.
    iApply fupd_idemp.
    (* XXX: This is horrible, but iMod does not work here for some reason, so we have to manually do it *)
    iApply (@fupd_wand_l _ (@uPred_bi_fupd Σ
         (@iris_invG (@goose_lang ext ffi ffi_semantics) Σ (@heapG_irisG ext ffi ffi_semantics interp Σ Hheap))) with "[-]").
    iSplitR "H"; last first.
    { iExact "H". }
    iIntros "H".
    iSpecialize ("H" with "[Hc Hcrel] [$]").
    {  simpl. iExists _, _. rewrite ffi_update_update. iFrame. }
    iDestruct "H" as (σs_post_crash Hspec_crash) "(Hspec_ffi&Hwpc)".
    iClear "Htrace_auth Horacle_auth Htrace_frag Horacle_frag".
    iExists ({| pbundleT := hnames |}).
    unshelve (iExists _).
    { rewrite //=. rewrite ?ffi_global_ctx_nolocal //=. }
    unshelve (iExists _).
    { rewrite //=. }
    iMod (goose_spec_crash_init _ _ σs gs _ σs' gs' σs_post_crash _ (trace σ_post_crash) (oracle σ_post_crash)
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
    rewrite ffi_update_update. iFrame.
    iSplitL "Hc".
    { iExactEq "Hc". f_equal. lia. }
    iSplit.
    * iClear "∗". eauto.
    * iDestruct (source_pool_singleton with "Hpool") as "Hpool".
      iDestruct ("Hwpc" with "[$] [$] [$] [$] [] [] [$]") as "H".
      { rewrite /spec_ctx/spec_ctx'.
        iDestruct "Hspec" as "(H1&$)".
        iExists _, _. iFrame "H1".
      }
      { rewrite /spec_crash_ctx/spec_crash_ctx'/source_crash_ctx.
        iSplitL.
        {
          rewrite /heap_update_local/heap_get_names//=.
          iExists _, _. iDestruct "Hcfupd1'" as "($&_)". }
        iDestruct "Hcfupd1'" as "(_&$)".
      }
      iMod (own_disc_fupd_elim with "Hcfupd3") as "Hcfupd3".
      iPoseProof (wpc_trace_inv_open k _ _ _ e _ _ Φ Φc with "[] Hspec Htrace Hcfupd1' Hcfupd3 H") as "H".
      { iApply Hexcl. }
      rewrite /hG//=.
      rewrite /heap_update_local/heap_get_names//= ffi_update_update.
      rewrite /traceG_update//=.
      rewrite /gen_heap_names.gen_heapG_update//=.
      rewrite ffi_update_get_local //=.
Qed.

End refinement_wpc.
