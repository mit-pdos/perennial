From iris.algebra Require Import auth gmap frac agree.
Require Import Helpers.RelationTheorems.
Require Import ExMach.Adequacy.
Import ExMach.
Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Spec.Layer.

Section refinement.
  Context OpT (Λa: Layer OpT).
  Context (impl: LayerImpl ExMach.Op OpT).
  Notation compile_op := impl.(compile_op).
  Notation compile_rec := impl.(compile_rec).
  Notation compile_seq := impl.(compile_seq).
  Notation compile := impl.(compile).
  Notation recover := impl.(recover).
  Notation compile_proc_seq := impl.(compile_proc_seq).
  Context `{exmachPreG Σ}.
  Context `{cfgPreG OpT Λa Σ}.
  Context (crash_inner: forall {_ : @cfgG OpT Λa Σ} {_: exmachG Σ}, iProp Σ).
  Context (exec_inner: forall {_ : @cfgG OpT Λa Σ} {_ : exmachG Σ}, iProp Σ).
  Context (crash_param: forall (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ), Type).
  Context (crash_inv: forall {H1 : @cfgG OpT Λa Σ} {H2 : exmachG Σ}, @crash_param _ _ → iProp Σ).
  Context (crash_starter: forall {H1 : @cfgG OpT Λa Σ} {H2 : exmachG Σ}, @crash_param _ _ → iProp Σ).
  Context (exec_inv: forall {_ : @cfgG OpT Λa Σ} {_ : exmachG Σ}, iProp Σ).

  Context (einv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : exmachG Σ}, Persistent (exec_inv H1 H2)).
  Context (cinv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : exmachG Σ}
            {P: crash_param _ _}, Persistent (crash_inv H1 H2 P)).

  Context (E: coPset).
  Context (nameIncl: nclose sourceN ⊆ E).
  (* TODO: we should get rid of rec_seq if we're not exploiting vertical comp anymore *)
  Context (recv: proc ExMach.Op unit).
  Context (recsingle: recover = rec_singleton recv).

  Context (refinement_op_triples:
             forall {H1 H2 T1 T2} j K `{LanguageCtx OpT T1 T2 Λa K} (op: OpT T1),
               j ⤇ K (Call op) ∗ (@exec_inv H1 H2) ⊢
                 WP compile (Call op) {{ v, j ⤇ K (Ret v) }}).

  Context (exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ ∃ ρ, source_ctx ρ).

  Lemma refinement_triples:
             forall {H1 H2 T1 T2} j K `{LanguageCtx OpT T1 T2 Λa K} (e: proc OpT T1),
               j ⤇ K e ∗ (@exec_inv H1 H2) ⊢
                 WP compile e {{ v, j ⤇ K (Ret v) }}.
  Proof.
    intros ???? j K Hctx e.
    iIntros "(Hj&#Hinv)".
    iAssert (⌜∃ ea: Λa.(State), True⌝)%I as %[? _].
    {
      iDestruct (exec_inv_source_ctx with "Hinv") as ((?&?)) "#Hctx".
      eauto.
    }
    assert (Inhabited Λa.(State)).
    { eexists. eauto. }
    iInduction e as [] "IH" forall (j T2 K Hctx).
    - iApply refinement_op_triples; iFrame; eauto.
    - wp_ret. eauto.
    - wp_bind.
      iApply wp_wand_l. iSplitL ""; last first.
      * iApply ("IH1" $! _ _ (fun x => K (Bind x p2)) with "[] Hj"); try iFrame.
        { iPureIntro. apply comp_ctx; auto. apply _. }
      * iIntros (?) "Hj".
        iDestruct (exec_inv_source_ctx with "Hinv") as (?) "#Hctx".
        iMod (ghost_step_bind_ret with "Hj []") as "Hj".
        { set_solver+. }
        { eauto. }
        iApply "IH"; auto.
    - iLöb as "IHloop" forall (init).
      iDestruct (exec_inv_source_ctx with "Hinv") as (?) "#Hctx".
      iMod (ghost_step_loop with "Hj []") as "Hj".
      { set_solver+. }
      { eauto. }
      wp_loop.
      iApply wp_wand_l.
      iSplitL ""; last first.
      * rewrite /loop1. simpl.
        iApply ("IH" $! _ _ _ (fun x => K (Bind x
                               (fun out => match out with
                               | ContinueOutcome x => Loop body x
                               | DoneWithOutcome r => Ret r
                               end))) with "[] Hj")%proc.
        { iPureIntro. apply comp_ctx; auto. apply _. }
      * iIntros (out) "Hj".
        destruct out.
        ** iNext.
           iMod (ghost_step_bind_ret with "Hj []") as "Hj".
           { set_solver+. }
           { eauto. }
             by iApply "IHloop".
        ** iNext.
           iMod (ghost_step_bind_ret with "Hj []") as "Hj".
           { set_solver+. }
           { eauto. }
           by wp_ret.
   - iDestruct (exec_inv_source_ctx with "Hinv") as (?) "#Hctx".
     iMod (ghost_step_spawn with "Hj []") as "(Hj&Hj')".
     { set_solver+. }
     { eauto. }
     iDestruct "Hj'" as (j') "Hj'".
     iApply (wp_spawn with "[Hj'] [Hj]").
     { iNext. iApply wp_wand_l; iSplitL ""; last first.
       { iApply ("IH" $! _ _ (fun x => x)); first (iPureIntro; apply _).
         iFrame. }
       eauto. }
     eauto.
  Qed.

  Context (recv_triple:
             forall {H1 H2} param,
               (@crash_inv H1 H2 param) ∗ (@crash_starter H1 H2 param) ⊢
                    WP recv @ NotStuck; ⊤ {{ v, |={⊤,E}=> ∃ σ2a σ2a', source_state σ2a
                    ∗ ⌜Λa.(crash_step) σ2a (Val σ2a' tt)⌝ ∗
                    ∀ `{Hcfg': cfgG OpT Λa Σ} (Hinv': invG Σ) ρ,
                      source_ctx (ρ, σ2a') ∗ source_state σ2a'  ={⊤}=∗
                      exec_inner Hcfg' (ExMachG Σ Hinv' exm_mem_inG exm_disk_inG)
                                               }}).

  Context (init_absr: Λa.(State) → ExMach.State → Prop).
  Context (init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → state_wf σ1c).

  Context (init_exec_inner: ∀ σ1a σ1c ρ, init_absr σ1a σ1c →
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          (([∗ map] i ↦ v ∈ mem_state σ1c, i m↦ v) ∗
           ([∗ map] i ↦ v ∈ disk_state σ1c, i d↦ v) ∗
           source_ctx (ρ, σ1a) ∗ source_state σ1a) ={⊤}=∗ exec_inner _ _)).

  Context (exec_inv_preserve_crash:
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          exec_inv Hcfg Hex ={⊤, E}=∗ ∀ Hmem',
          (let Hex := ExMachG Σ (exm_invG) Hmem' (exm_disk_inG) in
              ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={E}=∗ crash_inner Hcfg Hex))).

  Context (crash_inv_preserve_crash:
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ} param,
          crash_inv Hcfg Hex param ={⊤, E}=∗ ∀ Hmem',
          (let Hex := ExMachG Σ (exm_invG) Hmem' (exm_disk_inG) in
              ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={E}=∗ crash_inner Hcfg Hex))).

  (* TODO: Much of this business is just to capture the fact that exec_inner/crash_inner
     should not really mention invariants, because those old invariants are 'dead' *)
  Context (crash_inner_inv :
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ} cfg,
          (∃ Hinv, crash_inner Hcfg (ExMachG Σ Hinv (exm_mem_inG) (exm_disk_inG))) ∗
          source_ctx cfg
          ={⊤}=∗ ∃ param, crash_inv Hcfg Hex param ∗ crash_starter Hcfg Hex param)).

  Context (exec_inner_inv :
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ} cfg,
          (∃ Hinv, exec_inner Hcfg (ExMachG Σ Hinv (exm_mem_inG) (exm_disk_inG))) ∗
          source_ctx cfg
          ={⊤}=∗ exec_inv Hcfg Hex)).

  Context (inv_implies_source:
             ∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
             exec_inv Hcfg Hex ={⊤, E}=∗ ∃ σ2a : Λa.(State), source_state σ2a).

  (* TODO: should we model explicit effects of finishing programs? *)
  Context (exec_inv_preserve_finish:
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          exec_inv Hcfg Hex ={⊤, E}=∗ ∃ σ2a : Λa.(State), source_state σ2a ∗
          ∀ `{Hcfg': cfgG OpT Λa Σ} (Hinv': invG Σ) ρ,
            source_ctx (ρ, σ2a) ∗ source_state σ2a  ={⊤}=∗
             exec_inner Hcfg' (ExMachG Σ Hinv' exm_mem_inG exm_disk_inG))).


  Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq OpT T) :
    init_absr σ1a σ1c →
    ¬ proc_exec_seq Λa es (rec_singleton (Ret ())) σ1a Err →
    ∀ σ2c res, ExMach.l.(proc_exec_seq) (compile_proc_seq es) (rec_singleton recv) σ1c (Val σ2c res) →
    ∃ σ2a, Λa.(proc_exec_seq) es (rec_singleton (Ret tt)) σ1a (Val σ2a res).
  Proof.
    rewrite /compile_proc_seq. intros Hinit Hno_err.
    unshelve (eapply wp_proc_seq_refinement_adequacy with
                  (φ := fun _ _ _ => True%I)
                  (φrec := fun _ _ => True%I)
                  (E0 := E); eauto).
    clear Hno_err.
  iAssert (∀ invG H1 ρ, |={⊤}=>
       ∃ hM hD
            (Hmpf_eq : hM.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
          H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ nat_eq_dec nat_countable))
            (Hdpf_eq : hD.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
          H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ nat_eq_dec nat_countable)),
         (@ex_mach_interp _ hM hD σ1c) ∗
         (source_ctx (ρ, σ1a) -∗ source_state σ1a ={⊤}=∗
       exec_inner H1 (ExMachG Σ invG hM hD)))%I as "Hpre".
  {
  iIntros.
  iMod (gen_heap_strong_init (mem_state σ1c)) as (hM Hmpf_eq) "(Hmc&Hm)".
  iMod (gen_heap_strong_init (disk_state σ1c)) as (hD Hdpf_eq) "(Hdc&Hd)".
  iModIntro. iExists hM, hD, Hmpf_eq, Hdpf_eq. iSplitL "Hmc Hdc".
  { iExists _, _. iFrame. iPureIntro.
    edestruct (init_wf) as (Hwf1&Hwf2); eauto.
    split_and!; eauto; intros i.
    * destruct (Hwf1 i); intuition.
    * destruct (Hwf2 i); intuition.
  }
  iIntros.
  iPoseProof (init_exec_inner σ1a σ1c ρ Hinit (ExMachG Σ _ hM hD) _) as "H".
  iMod ("H" with "[-]") as "$".
  { iFrame.  iSplitL "Hm"; [| iSplitL "Hd"].
    { rewrite -Hmpf_eq. iApply mem_init_to_bigOp; auto. }
    { rewrite -Hdpf_eq. iApply disk_init_to_bigOp; auto. }
    eauto.
  }
  eauto.
  }

  clear Hinit.
  iInduction es as [|es] "IH" forall (σ1a σ1c) "Hpre".
  - iSplit; first by eauto.
  iExists (fun cfgG s => ∃ (_ : exmachG Σ),
                     state_interp s ∗
                       (∃ (hM: gen_heapG addr nat Σ)
                            (Hmpf_eq : hM.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
                                       H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ
                                                              nat_eq_dec nat_countable)) ,
            gen_heap_ctx init_zero ∗ crash_inner cfgG (ExMachG Σ _ hM (exm_disk_inG))))%I; auto.
  iIntros (invG0 Hcfg0).
  iMod ("Hpre" $! invG0 _ _) as (hM hD ??) "(Hstate0&H)".
  iExists (@ex_mach_interp _ hM hD).
  iIntros "!> (#Hsrc&Hpt0&Hstate)".
  iMod ("H" with "Hsrc Hstate") as "Hinv".
  iMod (exec_inner_inv (ExMachG Σ _ hM hD) _ with "[Hinv]") as "#Hinv".
  { iFrame. iFrame "Hsrc". iExists _. iFrame. }
  simpl.
  iModIntro.
  iFrame "Hstate0".
  iSplitL "Hpt0".
  {  iPoseProof (@wp_mono with "[Hpt0]") as "H"; swap 1 2.
     { iApply refinement_triples. iFrame. iFrame "Hinv". }
     { reflexivity. }
     iApply (wp_wand with "H [Hinv]").
     iIntros (v) "Hpt0". iFrame.
     iIntros (σ2c) "Hmach".
     iMod (inv_implies_source with "Hinv") as (σ2a) "H".
     iModIntro. iExists _; iFrame; auto.
  }
  iSplit.
  { iIntros (σ2c) "Hmach".
    iMod (exec_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod (gen_heap_strong_init (init_zero)) as (hM' Hmpf_eq') "(Hmc&Hm)".
    iMod ("Hinv_post" with "[Hm]") as "Hinv'".
    { rewrite -Hmpf_eq'. iApply @mem_init_to_bigOp; auto. }
    iIntros. iModIntro.
    iExists (ExMachG Σ _ hM hD). iFrame "Hmach".
    iExists hM', Hmpf_eq'. iFrame.
  }

  iClear "Hsrc".
  iModIntro. iIntros (invG Hcfg' ?? Hcrash) "(Hinv0&#Hsrc)".
  iDestruct "Hinv0" as (HexmachG') "(Hinterp&Hinv0)".
  iDestruct "Hinv0" as (hM' Hmpf_eq') "(Hmc'&Hcrash_inner)".
  iClear "Hinv".
  iMod (crash_inner_inv (ExMachG Σ invG hM' (exm_disk_inG)) Hcfg' with "[Hcrash_inner]") as
      (param) "(#Hinv&Hstarter)".
  { iIntros. simpl. iFrame "Hsrc". iExists ( exmachG_irisG.(@iris_invG Op ExMach.State Σ)).
    iFrame. }
  iModIntro.
  iExists (@ex_mach_interp Σ hM' (exm_disk_inG)).
  iSplitL "Hinterp Hmc'".
  { (* shows ex_mach_interp is holds after crash for next gen *)
    rewrite /ex_mach_interp.
    iDestruct "Hinterp" as (mems disks) "(Hdisks&?&%&Hp)".
    iDestruct "Hp" as %(Hdisks&Hwf1'&Hwf2').
    inversion Hcrash; subst.
    iExists init_zero, _.
    iFrame.
    iPureIntro. split_and!.
    * rewrite /crash_fun//=.
    * rewrite /crash_fun//=.
    * rewrite /crash_fun/=. intros i Hsome.
      apply not_le; intros Hge.
      rewrite init_zero_lookup_ge_None in Hsome; last by lia.
      apply is_Some_None in Hsome; auto.
    * rewrite /crash_fun; auto.
  }
  iSplitL "Hinv Hstarter".
  {
    iPoseProof (@wp_mono with "[Hinv Hstarter]") as "H"; swap 1 2.
    { iApply recv_triple. iFrame. iApply "Hinv". }
    { reflexivity. }
    iApply (@wp_mono with "H").
    iIntros (_) "H". iIntros (σ2c) "Hinterp".
    iMod "H". iModIntro.
    iDestruct "H" as (σ2a σ2a') "(Hsource&Hinner&Hp)".
    iExists _, _. iFrame.
  }
  {
    iIntros (σ2c) "Hmach".
    iMod (crash_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod (gen_heap_strong_init (init_zero)) as (hM'' Hmpf_eq'') "(Hmc&Hm)".
    iMod ("Hinv_post" with "[Hm]") as "Hinv'".
    { rewrite -Hmpf_eq''. iApply @mem_init_to_bigOp; auto. }
    iIntros. iModIntro.

    iExists {| exm_invG := invG;
               exm_mem_inG := hM';
               exm_disk_inG := HexmachG'.(@exm_disk_inG Σ) |}.
    iFrame. iExists hM'', Hmpf_eq''. iFrame.
  }
  -
    iSplit; first by eauto.
  iExists (fun cfgG s => ∃ (Hex : exmachG Σ), state_interp s ∗
            (∃ (hM: gen_heapG addr nat Σ)
               (Hmpf_eq : hM.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
                          H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ
                                                                   nat_eq_dec nat_countable))
               (Hdpf_eq : (@exm_disk_inG Σ Hex).(@gen_heap_inG addr nat Σ
                                                               nat_eq_dec nat_countable)=
                          H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ
                                                                   nat_eq_dec nat_countable)) ,
            gen_heap_ctx init_zero ∗ crash_inner cfgG (ExMachG Σ _ hM (exm_disk_inG))))%I; auto.
  iIntros (invG0 Hcfg0).
  iMod ("Hpre" $! invG0 _ _) as (hM hD ??) "(Hstate0&H)".
  iExists (@ex_mach_interp _ hM hD).
  iIntros "!> (#Hsrc&Hpt0&Hstate)".
  iMod ("H" with "Hsrc Hstate") as "Hinv".
  iMod (exec_inner_inv (ExMachG Σ _ hM hD) _ with "[Hinv]") as "#Hinv".
  { iFrame "Hsrc".  iFrame. iExists _. iFrame. }
  simpl.
  iModIntro.
  iFrame "Hstate0".
  iSplitL "Hpt0".
  {  iPoseProof (@wp_mono with "[Hpt0]") as "H"; swap 1 2.
     { iApply refinement_triples. iFrame. iFrame "Hinv". }
     { reflexivity. }
     iApply (wp_wand with "H [Hinv]").
     iIntros (v) "Hpt0". iFrame.
     iIntros (σ2c) "Hmach".
     iMod (exec_inv_preserve_finish with "Hinv") as (σ2a) "(H&Hfinish)".
     iModIntro. iExists _; iFrame; auto.
     simpl.
     rewrite -/wp_proc_seq_refinement.
     iApply "IH".
     { iIntros. iModIntro.
       iExists hM. iExists hD. unshelve (iExists _, _); try eauto.
       iFrame. iIntros. iMod ("Hfinish" with "[-]"). iFrame. eauto.
       iModIntro. eauto.
     }
  }
  iSplit.
  { iIntros (σ2c) "Hmach".
    iMod (exec_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod (gen_heap_strong_init (init_zero)) as (hM' Hmpf_eq') "(Hmc&Hm)".
    iMod ("Hinv_post" with "[Hm]") as "Hinv'".
    { rewrite -Hmpf_eq'. iApply @mem_init_to_bigOp; auto. }
    iIntros. iModIntro.
    iExists (ExMachG Σ _ hM hD). iFrame "Hmach".
    iExists hM', Hmpf_eq', H2. iFrame.
  }
  iClear "Hsrc".
  iModIntro. iIntros (invG Hcfg' ?? Hcrash) "(Hinv0&#Hsrc)".
  iDestruct "Hinv0" as (HexmachG') "(Hinterp&Hinv0)".
  iDestruct "Hinv0" as (hM' Hmpf_eq' Hmdpf_eq') "(Hmc'&Hcrash_inner)".
  iClear "Hinv".
  iMod (crash_inner_inv (ExMachG Σ _
                                 hM' (exm_disk_inG)) Hcfg'
                         with "[Hcrash_inner]") as (param) "(#Hinv&Hstarter)".
  { iIntros. simpl. iFrame "Hsrc". iExists ( exmachG_irisG.(@iris_invG Op ExMach.State Σ)).
    iFrame. }
  iModIntro.
  iExists (@ex_mach_interp Σ hM' (exm_disk_inG)).
  iSplitL "Hinterp Hmc'".
  { (* shows ex_mach_interp is holds after crash for next gen *)
    rewrite /ex_mach_interp.
    iDestruct "Hinterp" as (mems disks) "(Hdisks&?&%&Hp)".
    iDestruct "Hp" as %(Hdisks&Hwf1&Hwf2).
    inversion Hcrash; subst.
    iExists init_zero, _.
    iFrame.
    iPureIntro. split_and!.
    * rewrite /crash_fun//=.
    * rewrite /crash_fun//=.
    * rewrite /crash_fun/=. intros i Hsome.
      apply not_le; intros Hge.
      rewrite init_zero_lookup_ge_None in Hsome; last by lia.
      apply is_Some_None in Hsome; auto.
    * rewrite /crash_fun; auto.
  }
  iSplitL "Hinv Hstarter".
  {
    iPoseProof (@wp_mono with "[Hinv Hstarter IH]") as "H"; swap 1 2.
    { iApply recv_triple. iFrame "Hstarter". iApply "Hinv". }
    { reflexivity. }
    iApply (@wp_wand with "H [IH]").
    iIntros (_) "H". iIntros (σ2c) "Hinterp".
    iMod "H". iModIntro.
    iDestruct "H" as (σ2a σ2a') "(Hsource&Hinner&Hfinish)".
    iExists _, _. iFrame.
     rewrite -/wp_proc_seq_refinement.
     iApply "IH".
     { iIntros. iModIntro.
       iExists hM'. iExists (HexmachG'.(@exm_disk_inG Σ)). unshelve (iExists _; iExists _); eauto.
       iFrame "Hinterp".
       iIntros.
       iMod ("Hfinish" with "[-]"). iFrame. eauto.
       iModIntro. eauto.
     }
  }
  {
    iIntros (σ2c) "Hmach".
    iMod (crash_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod (gen_heap_strong_init (init_zero)) as (hM'' Hmpf_eq'') "(Hmc&Hm)".
    iMod ("Hinv_post" with "[Hm]") as "Hinv'".
    { rewrite -Hmpf_eq''. iApply @mem_init_to_bigOp; auto. }
    iIntros. iModIntro.

    iExists {| exm_invG := invG;
               exm_mem_inG := hM';
               exm_disk_inG := HexmachG'.(@exm_disk_inG Σ) |}.
    iFrame. unshelve (iExists hM'', Hmpf_eq'', _); eauto. iFrame.
  }
  Qed.

End refinement.