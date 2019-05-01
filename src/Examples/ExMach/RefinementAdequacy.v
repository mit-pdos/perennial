From iris.algebra Require Import auth gmap frac agree.
Require Import ExMach.Adequacy.
Import ExMach.
Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Layer.

Module Type exmach_refinement_type.
  Context (OpT: Type → Type).
  Context (Λa: Layer OpT).
  Context (impl: LayerImpl ExMach.Op OpT).
  Context (Σ: gFunctors).
  Notation compile_op := (compile_op impl).
  Notation compile_rec := (compile_rec impl).
  Notation compile_seq := (compile_seq impl).
  Notation compile := (compile impl).
  Notation recover := (recover impl).
  Notation compile_proc_seq := (compile_proc_seq impl).
  Context `{CFG: cfgPreG OpT Λa Σ} `{exmachPreG Σ}.
  Context (crash_inner: forall {_ : @cfgG OpT Λa Σ} {_: exmachG Σ}, iProp Σ).
  Context (exec_inner: forall {_ : @cfgG OpT Λa Σ} {_: exmachG Σ}, iProp Σ).
  Context (crash_param: forall (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ), Type).
  Context (crash_inv: forall {H1 : @cfgG OpT Λa Σ} {H2 : exmachG Σ},
              @crash_param _ H2 → iProp Σ).
  Context (crash_starter: forall {H1 : @cfgG OpT Λa Σ} {H2 : exmachG Σ},
              @crash_param _ H2 → iProp Σ).
  Context (exec_inv: forall {_ : @cfgG OpT Λa Σ} {_ : exmachG Σ}, iProp Σ).
  Context (einv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _},
              Persistent (exec_inv H1 H2)).
  Context (cinv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _}
            {P: crash_param _ _}, Persistent (crash_inv H1 H2 P)).

  Context (E: coPset).
  Context (nameIncl: nclose sourceN ⊆ E).
  (* TODO: we should get rid of rec_seq if we're not exploiting vertical comp anymore *)
  Context (recv: proc ExMach.Op unit).
  Context (recsingle: recover = rec_singleton recv).

  Context (refinement_op_triples:
             forall {H1 H2 T1 T2} j K `{LanguageCtx OpT T1 T2 Λa K} (op: OpT T1),
               j ⤇ K (Call op) ∗ Registered ∗ (@exec_inv H1 H2) ⊢
                 WP compile (Call op) {{ v, j ⤇ K (Ret v) ∗ Registered  }}).

  Context (exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx).
End exmach_refinement_type.

Module exmach_refinement (eRT: exmach_refinement_type).

  Import eRT.
  Module RT : refinement_type.
    Definition OpC := ExMach.Op.
    Definition Λc := ExMach.l.
    Definition OpT := OpT.
    Definition Λa := Λa.
    Definition impl := impl.
    Definition exmachG := exmachG.
    Definition Σ := Σ.
    Definition CFG := CFG.
    Definition Hinstance := @exmachG_irisG.
    Definition Hinstance_reg := @exm_treg_inG.
    Definition crash_inner := crash_inner.
    Definition exec_inner := exec_inner.
    Definition crash_inv := crash_inv.
    Definition crash_param := crash_param.
    Definition crash_starter := crash_starter.
    Definition exec_inv := exec_inv.
    Definition einv_persist := einv_persist.
    Definition cinv_persist := cinv_persist.
    Definition E := E.
    Definition nameIncl := nameIncl.
    Definition recv := recv.
    Definition recsingle := recsingle.
    Definition refinement_op_triples := refinement_op_triples.
    Definition exec_inv_source_ctx := exec_inv_source_ctx.
  End RT.

  Module R := refinement RT.
  Export R.
End exmach_refinement.


Section refinement.
  Context OpT (Λa: Layer OpT).
  Context (impl: LayerImpl ExMach.Op OpT).
  Notation compile_op := (compile_op impl).
  Notation compile_rec := (compile_rec impl).
  Notation compile_seq := (compile_seq impl).
  Notation compile := (compile impl).
  Notation recover := (recover impl).
  Notation compile_proc_seq := (compile_proc_seq impl).
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
               j ⤇ K (Call op) ∗ Registered ∗ (@exec_inv H1 H2) ⊢
                 WP compile (Call op) {{ v, j ⤇ K (Ret v) ∗ Registered }}).

  Context (exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx).

  Lemma refinement_triples:
             forall {H1 H2 T1 T2} j K `{LanguageCtx OpT T1 T2 Λa K} (e: proc OpT T1),
               wf_client e →
               j ⤇ K e ∗ Registered ∗ (@exec_inv H1 H2) ⊢
                 WP compile e {{ v, j ⤇ K (Ret v) ∗ Registered }}.
  Proof.
    intros.
    epose (@refinement_triples _ _ _ _ _ exmachG).
    rewrite /RefinementIdempotence.exmachG in b.
    simpl.
    eapply @refinement_triples with (exmachG' := exmachG).


    . (exmachG := exmachG Σ)). with (exmachG := exmachG Σ)).



    intros ???? j K Hctx e Hwf.
    iIntros "(Hj&Hreg&#Hinv)".
    iAssert (⌜∃ ea: State Λa, True⌝)%I as %[? _].
    {
      iDestruct (exec_inv_source_ctx with "Hinv") as ((?&?)) "#Hctx".
      eauto.
    }
    assert (Inhabited (State Λa)).
    { eexists. eauto. }
    assert (Inhabited Λa.(OpState)).
    { eexists. destruct x; eauto. }
    iInduction e as [] "IH" forall (j T2 K Hctx).
    - iApply refinement_op_triples; iFrame; eauto.
    - wp_ret. iFrame.
    - wp_bind.
      iApply wp_wand_l. iSplitL ""; last first.
      * unshelve (iApply ("IH1" $! _ _ _ (fun x => K (Bind x p2)) with "[] Hj"); try iFrame).
        { eapply Hwf. }
        { iPureIntro. apply comp_ctx; auto. apply _. }
      * iIntros (?) "(Hj&Hreg)".
        iDestruct (exec_inv_source_ctx with "Hinv") as "#Hctx".
        iMod (ghost_step_bind_ret with "Hj []") as "Hj".
        { set_solver+. }
        { eauto. }
        iApply ("IH" with "[] [] Hj Hreg"); auto.
        { iPureIntro. eapply Hwf. }
    - iLöb as "IHloop" forall (init Hwf).
      iDestruct (exec_inv_source_ctx with "Hinv") as "#Hctx".
      iMod (ghost_step_loop with "Hj []") as "Hj".
      { set_solver+. }
      { eauto. }
      wp_loop.
      iApply wp_wand_l.
      iSplitL ""; last first.
      * rewrite /loop1. simpl.
        unshelve (iApply ("IH" $! _ _ _ _ (fun x => K (Bind x
                               (fun out => match out with
                               | ContinueOutcome x => Loop body x
                               | DoneWithOutcome r => Ret r
                               end))) with "[] Hj Hreg")%proc).
        { eauto. }
        { iPureIntro. apply comp_ctx; auto. apply _. }
      * iIntros (out) "(Hj&Hreg)".
        destruct out.
        ** iNext.
           iMod (ghost_step_bind_ret with "Hj []") as "Hj".
           { set_solver+. }
           { eauto. }
           iApply ("IHloop" with "[] Hj Hreg").
           { eauto. }
        ** iNext.
           iMod (ghost_step_bind_ret with "Hj []") as "Hj".
           { set_solver+. }
           { eauto. }
           wp_ret. iFrame.
   - inversion Hwf.
   - inversion Hwf.
   - iDestruct (exec_inv_source_ctx with "Hinv") as "#Hctx".
     iMod (ghost_step_spawn with "Hj []") as "(Hj&Hj')".
     { set_solver+. }
     { eauto. }
     iDestruct "Hj'" as (j') "Hj'".
     iApply (wp_spawn with "Hreg [Hj'] [Hj]").
     { iNext. iIntros "Hreg'". 
       { wp_bind.
         iApply (wp_wand with "[Hj' Hreg'] []").
         { unshelve (iApply ("IH" $! _ _ _ (fun x => Bind x (fun _ => Unregister))
                               with "[] Hj' Hreg'")).
           { eauto. }
           { iPureIntro. apply _. }
         }
         { iIntros (?) "(?&?)". iApply (wp_unregister with "[$]"). iIntros "!> ?". eauto. }
       }
     }
     iIntros "!> ?". iFrame.
  Qed.

  Context (recv_triple:
             forall {H1 H2} param,
               (@crash_inv H1 H2 param) ∗ Registered ∗ (@crash_starter H1 H2 param) ⊢
                    WP recv @ NotStuck; ⊤ {{ v, |={⊤,E}=> ∃ σ2a σ2a', source_state σ2a
                    ∗ ⌜Λa.(crash_step) σ2a (Val σ2a' tt)⌝ ∗
                    ∀ `{Hcfg': cfgG OpT Λa Σ} (Hinv': invG Σ) tr',
                      source_ctx ∗ source_state σ2a'  ={⊤}=∗
                      exec_inner Hcfg' (ExMachG Σ Hinv' exm_mem_inG exm_disk_inG tr')
                                               }}).

  Context (init_absr: Λa.(OpState) → ExMach.State → Prop).
  Context (init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → state_wf σ1c).

  Context (init_exec_inner: ∀ σ1a σ1c, init_absr σ1a σ1c →
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          (([∗ map] i ↦ v ∈ mem_state σ1c, i m↦ v) ∗
           ([∗ map] i ↦ v ∈ disk_state σ1c, i d↦ v) ∗
           source_ctx ∗ source_state σ1a) ={⊤}=∗ exec_inner _ _)).

  Context (exec_inv_preserve_crash:
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          exec_inv Hcfg Hex ={⊤, E}=∗ ∀ Hmem' Hreg',
          (let Hex := ExMachG Σ (exm_invG) Hmem' (exm_disk_inG) Hreg' in
              ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={E}=∗ crash_inner Hcfg Hex))).

  Context (crash_inv_preserve_crash:
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ} param,
          crash_inv Hcfg Hex param ={⊤, E}=∗ ∀ Hmem' Hreg',
          (let Hex := ExMachG Σ (exm_invG) Hmem' (exm_disk_inG) Hreg' in
              ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={E}=∗ crash_inner Hcfg Hex))).

  (* TODO: Much of this business is just to capture the fact that exec_inner/crash_inner
     should not really mention invariants, because those old invariants are 'dead' *)
  Context (crash_inner_inv :
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          (∃ Hinv, crash_inner Hcfg (ExMachG Σ Hinv (exm_mem_inG) (exm_disk_inG) (exm_treg_inG))) ∗
          source_ctx ={⊤}=∗ ∃ param, crash_inv Hcfg Hex param ∗ crash_starter Hcfg Hex param)).

  Context (exec_inner_inv :
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          (∃ Hinv, exec_inner Hcfg (ExMachG Σ Hinv (exm_mem_inG) (exm_disk_inG) (exm_treg_inG))) ∗
          source_ctx ={⊤}=∗ exec_inv Hcfg Hex)).

  Context (exec_inv_preserve_finish:
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          AllDone -∗ exec_inv Hcfg Hex ={⊤, E}=∗ ∃ (σ2a σ2a' : Λa.(OpState)), source_state σ2a
          ∗ ⌜Λa.(finish_step) σ2a (Val σ2a' tt)⌝ ∗
          ∀ `{Hcfg': cfgG OpT Λa Σ} (Hinv': invG Σ) Hmem' Hreg',
            (let Hex := ExMachG Σ Hinv' Hmem' (exm_disk_inG) Hreg' in
            source_ctx∗ source_state σ2a' ∗ ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={⊤}=∗
               exec_inner Hcfg' Hex))%I).


  Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq OpT T) :
    init_absr σ1a σ1c →
    wf_client_seq es →
    ¬ proc_exec_seq Λa es (rec_singleton (Ret ())) (1, σ1a) Err →
    ∀ σ2c res, proc_exec_seq ExMach.l (compile_proc_seq es)
                                        (rec_singleton recv) (1, σ1c) (Val σ2c res) →
    ∃ σ2a, proc_exec_seq Λa es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
  Proof.
    rewrite /compile_proc_seq. intros Hinit Hwf_seq Hno_err σ2c0 ?.
    unshelve (eapply wp_proc_seq_refinement_adequacy with
                  (Λc := l)
                  (φ := fun va vc _ _ => ⌜ va = vc ⌝%I)
                  (E0 := E); eauto).
    clear Hno_err.
  iAssert (∀ invG H1 ρ, |={⊤}=>
       ∃ hM hD tR
            (Hmpf_eq : hM.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
          H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ nat_eq_dec nat_countable))
            (Hdpf_eq : hD.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
          H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ nat_eq_dec nat_countable)),
         (@ex_mach_interp _ hM hD {| treg_name := tR; treg_counter_inG := _ |} (1, σ1c)) ∗
         (source_ctx' (ρ, σ1a) -∗ source_state σ1a ={⊤}=∗
         own tR (Cinl (Count (-1))) ∗ 
          exec_inner H1 (ExMachG Σ invG hM hD {| treg_name := tR; treg_counter_inG := _ |})))%I
      as "Hpre".
  {
  iIntros.
  iMod (gen_heap_strong_init (mem_state σ1c)) as (hM Hmpf_eq) "(Hmc&Hm)".
  iMod (gen_heap_strong_init (disk_state σ1c)) as (hD Hdpf_eq) "(Hdc&Hd)".
  iMod (own_alloc (Cinl (Count 0))) as (tR) "Ht".
  { constructor. }
  set (tR' := {| treg_name := tR; treg_counter_inG := _ |}).
  iAssert (own tR (Cinl (Count 1)) ∗ own tR (Cinl (Count (-1))))%I with "[Ht]" as "(Ht&Hreg)".
  { rewrite /Registered -own_op Cinl_op counting_op' //=. }
  iModIntro. iExists hM, hD, tR, Hmpf_eq, Hdpf_eq. iSplitL "Hmc Hdc Ht".
  { iFrame. iExists _, _. iFrame. iPureIntro.
    edestruct (init_wf) as (Hwf1&Hwf2); eauto.
    split_and!; eauto; intros i.
    * destruct (Hwf1 i); intuition.
    * destruct (Hwf2 i); intuition.
  }
  iIntros.
  iPoseProof (init_exec_inner σ1a σ1c Hinit (ExMachG Σ _ hM hD tR') _) as "H".
  iMod ("H" with "[-Hreg]") as "$".
  { iFrame.  iSplitL "Hm"; [| iSplitL "Hd"].
    { rewrite -Hmpf_eq. iApply mem_init_to_bigOp; auto. }
    { rewrite -Hdpf_eq. iApply disk_init_to_bigOp; auto. }
    iExists _; eauto.
  }
  iFrame; eauto.
  }

  clear Hinit.
  iInduction es as [|es] "IH" forall (σ1a σ1c) "Hpre"; first by eauto.
  - iSplit; first by eauto.
  iExists (fun cfgG s => ∃ (Hex : exmachG Σ), state_interp s ∗
            (∃ (hM: gen_heapG addr nat Σ) tr
               (Hmpf_eq : hM.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
                          H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ
                                                                   nat_eq_dec nat_countable))
               (Hdpf_eq : (@exm_disk_inG Σ Hex).(@gen_heap_inG addr nat Σ
                                                               nat_eq_dec nat_countable)=
                          H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ
                                                                   nat_eq_dec nat_countable)) ,
            gen_heap_ctx init_zero ∗ own tr (Cinl (Count 0)) ∗ crash_inner cfgG (ExMachG Σ _ hM (exm_disk_inG) {| treg_name := tr; treg_counter_inG := _ |})))%I; auto.
  iIntros (invG0 Hcfg0).
  iMod ("Hpre" $! invG0 _ _) as (hM hD tr ??) "(Hstate0&H)".
  set (tR' := {| treg_name := tr; treg_counter_inG := _ |}).
  iExists (@ex_mach_interp _ hM hD tR').
  iIntros "!> (#Hsrc&Hpt0&Hstate)".
  iMod ("H" with "Hsrc Hstate") as "(Hreg&Hinv)".
  iMod (exec_inner_inv (ExMachG Σ _ hM hD tR') _ with "[Hinv]") as "#Hinv".
  { iSplitR ""; last by (iExists _; iFrame). iExists _. iFrame. }
  simpl.
  iModIntro.
  iFrame "Hstate0".
  iSplitL "Hpt0 Hreg".
  {  iPoseProof (@wp_mono with "[Hpt0 Hreg]") as "H"; swap 1 2.
     { iApply @refinement_triples. destruct (Hwf_seq) as (?&?). eauto. iFrame. iFrame "Hinv".
       iFrame "Hreg".
     }
     { reflexivity. }
     simpl. rewrite /compile_whole.
     wp_bind.
     iApply (wp_wand with "H [Hinv]").
     iIntros (v) "(Hpt0&Hreg)". iFrame.
     wp_bind.
     iApply (@wp_wait Σ {| exm_invG := invG0;
             exm_mem_inG := hM;
             exm_disk_inG := hD;
             exm_treg_inG := tR' |}
               with "Hreg").
     iIntros "!> Hdone".
     wp_ret. iFrame. iExists _. iFrame. iIntros (σ2c) "Hmach".
     iMod (exec_inv_preserve_finish with "Hdone Hinv") as (σ2a σ2a') "(H&Hfina&Hfinish)".
     iDestruct "Hfina" as %Hfina.
     iModIntro. iExists _; iFrame; auto.
     simpl.
     rewrite -/wp_proc_seq_refinement.
     iIntros (σ2c'). iIntros.
     unshelve (iExists σ2a', _); [eauto |]; [].
     iApply "IH".
     { iPureIntro. destruct Hwf_seq. eauto. }
     { iIntros.
       iMod (gen_heap_strong_init (init_zero)) as (hM' Hmpf_eq') "(Hmc&Hm)".
       iMod (own_alloc (Cinl (Count 0))) as (tR_fresh') "Ht".
       { constructor. }
       iAssert (own tR_fresh' (Cinl (Count 1))
                    ∗ own tR_fresh' (Cinl (Count (-1))))%I with "[Ht]" as "(Ht&Hreg)".
       { rewrite /Registered -own_op Cinl_op counting_op' //=. }
       set (tR''' := {| treg_name := tR_fresh'; treg_counter_inG := _ |}).
       iModIntro.
       iExists hM'. iExists hD. iExists tR_fresh'. unshelve (iExists _, _); try eauto.
       destruct σ2c as (n&σ2c). iDestruct "Hmach" as "(?&Hmach)".
       iFrame.
       iSplitL ("Hmc Hmach").
       { iClear "IH". iDestruct "Hmach" as (mem0 disk) "(?&?&%&%&%&%)".
         iExists init_zero, disk. iFrame.
         inversion Hfinish. subst. rewrite /crash_fun. simpl.
         iPureIntro. split_and!; [ | | apply init_state_wf |]; auto.
       }
       iIntros "Hctx' Hsrc'". iMod ("Hfinish" $! _ _ hM' with "[-]").
       iSplitL "Hctx'"; first by (iExists _; iFrame). iFrame.
       { rewrite -Hmpf_eq'. iApply (@mem_init_to_bigOp _ (ExMachG Σ _ hM' hD tR') with "Hm"). }
       iFrame; eauto.
     }
  }
  iSplit.
  { iIntros (σ2c) "Hmach".
    iMod (exec_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod (gen_heap_strong_init (init_zero)) as (hM' Hmpf_eq') "(Hmc&Hm)".
    iMod (own_alloc (Cinl (Count 0))) as (tR_fresh') "Ht".
    { constructor. }
    set (tR''' := {| treg_name := tR_fresh'; treg_counter_inG := _ |}).
    iMod ("Hinv_post" with "[Hm]") as "Hinv'".
    { rewrite -Hmpf_eq'. iApply @mem_init_to_bigOp; auto. }
    iIntros. iModIntro.
    iExists (ExMachG Σ _ hM hD tR'). iFrame "Hmach".
    iExists hM', tR_fresh', Hmpf_eq', H2. iFrame.
  }
  iClear "Hsrc".
  iModIntro. iIntros (invG Hcfg' ?? Hcrash) "(Hinv0&#Hsrc)".
  iDestruct "Hinv0" as (HexmachG') "(Hinterp&Hinv0)".
  iDestruct "Hinv0" as (hM' tR_fresh' Hmpf_eq' Hmdpf_eq') "(Hmc'&Hreg&Hcrash_inner)".
  iClear "Hinv".
  set (tR''' := {| treg_name := tR_fresh'; treg_counter_inG := _ |}).
  iMod (crash_inner_inv (ExMachG Σ _
                                 hM' (exm_disk_inG) tR''') Hcfg'
                         with "[Hcrash_inner]") as (param) "(#Hinv&Hstarter)".
  { iIntros. simpl. iSplitR ""; last by (iExists _; iFrame).
    iExists ( exmachG_irisG.(@iris_invG Op _ Σ)).
    iFrame. }
  iModIntro.
  iAssert (own tR_fresh' (Cinl (Count 1)) ∗ own tR_fresh' (Cinl (Count (-1))))%I
    with "[Hreg]" as "(Ht&Hreg)".
  { rewrite /Registered -own_op Cinl_op counting_op' //=. }
  iExists (@ex_mach_interp Σ hM' (exm_disk_inG) tR''').
  iSplitL "Hinterp Ht Hmc'".
  { (* shows ex_mach_interp is holds after crash for next gen *)
    rewrite /ex_mach_interp'.
    rewrite /ex_mach_interp.
    destruct a, a0.
    iDestruct "Hinterp" as "(?&Hinterp)".
    iDestruct "Hinterp" as (mems disks) "(Hdisks&?&%&Hp)".
    iDestruct "Hp" as %(Hdisks&Hwf1'&Hwf2').
    destruct Hcrash as ([]&(?&?)&Hput&Hrest).
    inversion Hput. inversion H4. subst.
    inversion Hrest; subst. inversion H3. subst.
    iSplitL "Ht".
    { iFrame. }
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
  iSplitL "Hinv Hreg Hstarter".
  {
    iPoseProof (@wp_mono with "[Hinv Hreg Hstarter IH]") as "H"; swap 1 2.
    { iApply recv_triple. iFrame "Hstarter". iFrame. iApply "Hinv". }
    { reflexivity. }
    iApply (@wp_wand with "H [IH]").
    iIntros (_) "H". iIntros (σ2c) "Hinterp".
    iMod "H". iModIntro.
    iDestruct "H" as (σ2a σ2a') "(Hsource&Hinner&Hfinish)".
    iExists (1, σ2a), (1, σ2a'). iFrame.
     rewrite -/wp_proc_seq_refinement.
     iDestruct "Hinner" as %?.
     iSplitL "".
     { iPureIntro. exists tt, (1, σ2a); split; eauto. econstructor. split; eauto. eauto.
       econstructor; eauto.
     }
     iApply "IH".
     { destruct Hwf_seq. eauto. }
     { iIntros.
       iMod (own_alloc (Cinl (Count 0))) as (tR_fresh'') "Ht".
       { constructor. }
       iAssert (own tR_fresh'' (Cinl (Count 1))
                    ∗ own tR_fresh'' (Cinl (Count (-1))))%I with "[Ht]" as "(Ht&Hreg)".
       { rewrite /Registered -own_op Cinl_op counting_op' //=. }
       set (tR'''' := {| treg_name := tR_fresh''; treg_counter_inG := _ |}).
       iModIntro.
       iExists hM'. iExists (HexmachG'.(@exm_disk_inG Σ)). iExists tR_fresh''.
       unshelve (iExists _; iExists _); eauto.
       destruct σ2c. iDestruct "Hinterp" as "(?&?)".
       iFrame. iIntros. iMod ("Hfinish" with "[-]"). iSplitL ""; first by (iExists _; iFrame).
       iFrame. eauto.
     }
  }
  {
    iIntros (σ2c) "Hmach".
    iMod (crash_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod (gen_heap_strong_init (init_zero)) as (hM'' Hmpf_eq'') "(Hmc&Hm)".
    iMod (own_alloc (Cinl (Count 0))) as (tR_fresh'') "Ht".
    { constructor. }
    set (tR'''' := {| treg_name := tR_fresh''; treg_counter_inG := _ |}).
    iMod ("Hinv_post" with "[Hm]") as "Hinv'".
    { rewrite -Hmpf_eq''. iApply @mem_init_to_bigOp; auto. }
    iIntros. iModIntro.

    iExists {| exm_invG := invG;
               exm_mem_inG := hM';
               exm_disk_inG := HexmachG'.(@exm_disk_inG Σ);
               exm_treg_inG := tR''' |}.
    iFrame "Hmach".
    iFrame. unshelve (iExists hM'', tR_fresh'', Hmpf_eq'', _); eauto. iFrame.
  }
  Qed.

End refinement.
