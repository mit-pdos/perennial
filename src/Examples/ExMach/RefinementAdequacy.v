From iris.algebra Require Import auth gmap frac agree.
Require Export CSL.WeakestPre CSL.Lifting CSL.Adequacy CSL.RefinementAdequacy.
Require Import Helpers.RelationTheorems.
From iris.algebra Require Export functions.
From iris.base_logic.lib Require Export invariants gen_heap.
From iris.proofmode Require Export tactics.
Require Export ExMach.ExMachAPI ExMach.WeakestPre.

Class exmachPreG Σ := ExMachPreG {
  exm_preG_iris :> invPreG Σ;
  exm_preG_mem :> gen_heapPreG nat nat Σ;
  exm_preG_disk :> gen_heapPreG nat nat Σ
}.

Definition exmachΣ : gFunctors := #[invΣ; gen_heapΣ nat nat; gen_heapΣ nat nat].
Instance subG_exmachPreG {Σ} : subG exmachΣ Σ → exmachPreG Σ.
Proof. solve_inG. Qed.

Import ExMach.

(* We don't need to actually use this directly, because we're interested in showing refinements,
   but worth proving first because it's a bit simpler and helps check that everything makes sense. *)
Definition exmach_recovery_adequacy {T R} Σ `{exmachPreG Σ} s
           (e: proc ExMach.Op T) (rec: proc _ R) σ φ φrec (φinv : forall {_ : exmachG Σ}, iProp Σ) :
  state_wf σ →
  (∀ `{exmachG Σ},
      (([∗ map] i ↦ v ∈ mem_state σ, i m↦ v) -∗
       ([∗ map] i ↦ v ∈ disk_state σ, i d↦ v) ={⊤}=∗
               WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}
               ∗ (|={⊤, ∅}=> φinv)
               ∗ □ (∀ `{hex: exmachG Σ},
                      (∃ Hinv H0', @φinv (@ExMachG Σ Hinv H0' (exm_disk_inG))) -∗
                      ([∗ map] i ↦ v ∈ init_zero, i m↦ v)
                      ={⊤}=∗ WP rec @ s; ⊤ {{ _, ⌜ φrec ⌝ }}
                         ∗ (|={⊤, ∅}=> φinv))
      )%I) →
  s = NotStuck →
  @recv_adequate _ _ _ ExMach.l s e rec σ (λ v _, φ v) (λ _, φrec).
Proof.
  intros Hwf Hwp Hnot_stuck.
  eapply (wp_recovery_adequacy _ _) with (k := 0); eauto.
  iExists (fun s => ∃ _ : exmachG Σ,
                     state_interp s
                       ∗ φinv _
                       ∗ (∃ (hM: gen_heapG addr nat Σ)
                         (Hmpf_eq : hM.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
                                    H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ nat_eq_dec
                                                                             nat_countable)) ,
                             gen_heap_ctx init_zero ∗ own (gen_heap_name hM)
                                                     (◯ to_gen_heap init_zero)))%I; auto.
  iIntros (?) "".
  iMod (gen_heap_strong_init (mem_state σ)) as (hM Hmpf_eq) "(Hmc&Hm)".
  iMod (gen_heap_strong_init (disk_state σ)) as (hD Hdpf_eq) "(Hdc&Hd)".
  iExists (@ex_mach_interp _ hM hD).
  iSplitL "Hmc Hdc".
  { iExists _, _. iFrame. iPureIntro.
    destruct Hwf as (Hwf1&Hwf2).
    split_and!; eauto; intros i.
    * destruct (Hwf1 i); intuition.
    * destruct (Hwf2 i); intuition.
  }
  iPoseProof (Hwp (ExMachG Σ _ hM hD)) as "H".
  iMod ("H" with "[Hm] [Hd]") as "(Hwp&Hinv&#Hrec)"; iClear "H".
  { rewrite -Hmpf_eq. iApply mem_init_to_bigOp; auto. }
  { rewrite -Hdpf_eq. iApply disk_init_to_bigOp; auto. }
  iSplitL "Hwp".
  { iApply wp_wand_l; iFrame. iModIntro. iIntros.
    iApply fupd_mask_weaken; first by set_solver+. auto. }
  iSplitL "Hinv".
  { iModIntro. iIntros (?) "Hinterp". iMod "Hinv".
    iMod (gen_heap_strong_init (init_zero)) as (hM' Hmpf_eq') "(Hmc&Hm)".
    iExists _. iModIntro. iFrame "Hinv". iFrame "Hinterp". iExists hM', Hmpf_eq'; iFrame. }
  iModIntro. iAlways. iIntros (invG ?? Hcrash) "Hinv".
  iDestruct "Hinv" as (HexmachG) "(Hstate&Hinv&Hm')".
  iDestruct "Hm'" as (hM' Hmpf_eq') "(Hmc'&Hm')".
  iSpecialize ("Hrec" $! (ExMachG Σ invG hM' (@exm_disk_inG _ HexmachG)) with "[Hinv]").
  { iExists (exm_invG). iExists (@exm_mem_inG _ HexmachG); eauto.
    destruct HexmachG; auto. }
  iMod ("Hrec" with "[Hm']") as "(Hrec&Hinv)".
  { rewrite -Hmpf_eq'. iApply @mem_init_to_bigOp; auto. }
  iModIntro.
  iExists (@ex_mach_interp Σ hM' (@exm_disk_inG Σ HexmachG)).
  iSplitL "Hstate Hmc'".
  { (* shows ex_mach_interp is holds after crash for next gen *)
    rewrite /ex_mach_interp.
    iDestruct "Hstate" as (mems disks) "(_&?&%&Hp)".
    iDestruct "Hp" as %(Hdisks&Hwf1&Hwf2).
    inversion Hcrash; subst.
    iExists init_zero, _. iFrame.
    iPureIntro. split_and!.
    * rewrite /crash_fun//=.
    * rewrite /crash_fun//=.
    * rewrite /crash_fun/=. intros i Hsome.
      apply not_le; intros Hge.
      rewrite init_zero_lookup_ge_None in Hsome; last by lia.
      apply is_Some_None in Hsome; auto.
    * rewrite /crash_fun; auto.
  }
  iSplitL "Hrec".
  {
    (* TODO: For some reason @wp_wand_l fails here, not sure why *)
    iPoseProof (@wp_mono with "[Hrec]") as "H"; [| eauto |]; last eauto.
    iIntros. iApply fupd_mask_weaken; auto.
  }
  iIntros.
  iMod (gen_heap_strong_init (init_zero)) as (hM'' Hmpf_eq'') "(Hmc&Hm)".
  iMod "Hinv". iModIntro.
  iExists {| exm_invG := invG;
             exm_mem_inG := hM';
             exm_disk_inG := HexmachG.(@exm_disk_inG Σ) |}.
  iFrame. iExists hM'', Hmpf_eq''. iFrame.
Qed.

Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Spec.Layer.
Theorem exmach_crash_refinement {T R} OpTa Σ (Λa: Layer OpTa)
        `{exmachPreG Σ} `{cfgPreG OpTa Λa Σ}
        (ea: proc OpTa T) (ec: proc ExMach.Op T) (rec: proc ExMach.Op R) σ1a σ1c φ φrec E
        (φinv: forall {_ : @cfgG OpTa Λa Σ} {_ : exmachG Σ}, iProp Σ):
  ¬ exec Λa ea σ1a Err →
  state_wf σ1c →
  nclose sourceN ⊆ E →
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpTa Λa Σ},
          (([∗ map] i ↦ v ∈ mem_state σ1c, i m↦ v) -∗
           ([∗ map] i ↦ v ∈ disk_state σ1c, i d↦ v) -∗
             (source_ctx ([existT _ ea], σ1a) ∗ O ⤇ ea ∗ source_state σ1a) ={⊤}=∗
                WP ec @ NotStuck; ⊤ {{ v, O ⤇ of_val v
                    ∗ (∀ σ2c, ex_mach_interp' σ2c ={⊤,E}=∗ ∃ σ2a, source_state σ2a ∗ ⌜ φ v σ2a σ2c ⌝)}}
                    ∗ (|={⊤,E}=> φinv)
                    ∗ □ (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpTa Λa Σ} σ1c σ1c' (Hcrash: ExMach.l.(crash_step) σ1c (Val σ1c' tt)),
                           (∃ Hinv H0', @φinv _ (@ExMachG Σ Hinv H0' (exm_disk_inG))) -∗
                           ([∗ map] i ↦ v ∈ init_zero, i m↦ v)
                           ={⊤}=∗ WP rec @ NotStuck; ⊤ {{ v, (∀ σ2c, ex_mach_interp' σ2c ={⊤,E}=∗ ∃ σ2a σ2a', source_state σ2a ∗ ⌜Λa.(crash_step) σ2a (Val σ2a' tt)⌝ ∗ ⌜ φrec σ2a' σ2c ⌝)}}
                                  ∗ (|={⊤,E}=> φinv))))%I →
 @recv_adequate_internal Σ _ _ _ ExMach.l NotStuck ec rec σ1c
    (λ v σ2c, ∃ σ2a, ⌜ exec Λa ea σ1a (Val σ2a (existT _ v)) ⌝ ∗ ⌜ φ v σ2a σ2c ⌝)%I
    (λ σ2c, ∃ tp2 σ2a σ2a', ⌜ exec_partial Λa ea σ1a (Val σ2a tp2) ∧
                            crash_step Λa σ2a (Val σ2a' tt) ⌝  ∗ ⌜ φrec σ2a' σ2c⌝)%I O.
Proof.
  intros ? Hwf ? Hwp.
  unshelve (iApply wp_recovery_refinement_adequacy_internal; auto).
  { simpl. apply _. }
  { simpl. apply _. }
  { exact E. }

  rewrite /wp_recovery_refinement.
  simpl. iSplit; first by eauto.
  iExists (fun cfgG s => ∃ (_ : exmachG Σ),
                     state_interp s
                       ∗ φinv cfgG _
                       ∗ (∃ (hM: gen_heapG addr nat Σ)
                            (Hmpf_eq : hM.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
            H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ nat_eq_dec nat_countable)) , gen_heap_ctx init_zero ∗ own (gen_heap_name hM) (◯ to_gen_heap init_zero)))%I; auto.
  iIntros (? Hcfg0).
  iMod (gen_heap_strong_init (mem_state σ1c)) as (hM Hmpf_eq) "(Hmc&Hm)".
  iMod (gen_heap_strong_init (disk_state σ1c)) as (hD Hdpf_eq) "(Hdc&Hd)".
  iExists (@ex_mach_interp _ hM hD).
  iIntros "!> (Hsrc&Hpt0)".
  iSplitL "Hmc Hdc".
  { iExists _, _. iFrame. iPureIntro.
    edestruct Hwf as (Hwf1&Hwf2); first eauto.
    split_and!; eauto; intros i.
    * destruct (Hwf1 i); intuition.
    * destruct (Hwf2 i); intuition.
  }
  iPoseProof (Hwp $! (ExMachG Σ _ hM hD) Hcfg0) as "H".
  iMod ("H" with "[Hm] [Hd] [Hsrc Hpt0]") as "(Hwp&Hinv&#Hrec)"; iClear "H".
  { rewrite -Hmpf_eq. iApply mem_init_to_bigOp; auto. }
  { rewrite -Hdpf_eq. iApply disk_init_to_bigOp; auto. }
  { iFrame.  }
  iSplitL "Hwp".
  { iModIntro.
    iPoseProof (@wp_mono with "[Hwp]") as "H"; [| eauto |]; last eauto.
    iIntros (v) "($&H)". auto. }
  iSplitL "Hinv".
  { iModIntro. iIntros (?) "Hinterp". iMod "Hinv".
    iMod (gen_heap_strong_init (init_zero)) as (hM' Hmpf_eq') "(Hmc&Hm)".
    iExists _. iModIntro. iFrame "Hinv". iFrame "Hinterp". iExists hM', Hmpf_eq'; iFrame. }
  iModIntro. iAlways. iIntros (invG Hcfg' ?? Hcrash) "Hinv".
  iDestruct "Hinv" as (HexmachG) "(Hstate&Hinv&Hm')".
  iDestruct "Hm'" as (hM' Hmpf_eq') "(Hmc'&Hm')".
  iSpecialize ("Hrec" $! (ExMachG Σ invG hM' (@exm_disk_inG _ HexmachG)) Hcfg' with "[//] [Hinv]").
  { iExists (exm_invG). iExists (@exm_mem_inG _ HexmachG); eauto.
    destruct HexmachG; auto. }
  iMod ("Hrec" with "[Hm']") as "(Hrec&Hinv)".
  { rewrite -Hmpf_eq'. iApply @mem_init_to_bigOp; auto. }
  iModIntro.
  iExists (@ex_mach_interp Σ hM' (@exm_disk_inG Σ HexmachG)).
  iSplitL "Hstate Hmc'".
  { (* shows ex_mach_interp is holds after crash for next gen *)
    rewrite /ex_mach_interp.
    iDestruct "Hstate" as (mems disks) "(_&?&%&Hp)".
    iDestruct "Hp" as %(Hdisks&Hwf1&Hwf2).
    inversion Hcrash; subst.
    iExists init_zero, _. iFrame.
    iPureIntro. split_and!.
    * rewrite /crash_fun//=.
    * rewrite /crash_fun//=.
    * rewrite /crash_fun/=. intros i Hsome.
      apply not_le; intros Hge.
      rewrite init_zero_lookup_ge_None in Hsome; last by lia.
      apply is_Some_None in Hsome; auto.
    * rewrite /crash_fun; auto.
  }
  iSplitL "Hrec".
  {
    (* TODO: For some reason @wp_wand_l fails here, not sure why *)
    iPoseProof (@wp_mono with "[Hrec]") as "H"; [| eauto |]; last eauto.
    iIntros (?) "H". iIntros. iMod ("H" with "[$]") as (??) "(?&%)". iModIntro.
    iExists _, _. iFrame.
    eauto.
  }
  iIntros.
  iMod (gen_heap_strong_init (init_zero)) as (hM'' Hmpf_eq'') "(Hmc&Hm)".
  iMod "Hinv". iModIntro.
  iExists {| exm_invG := invG;
             exm_mem_inG := hM';
             exm_disk_inG := HexmachG.(@exm_disk_inG Σ) |}.
  iFrame. iExists hM'', Hmpf_eq''. iFrame.
Qed.

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
  Context (crash_inv: forall {_ : @cfgG OpT Λa Σ} {_ : exmachG Σ}, iProp Σ).
  Context (exec_inv: forall {_ : @cfgG OpT Λa Σ} {_ : exmachG Σ}, iProp Σ).

  Context (einv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : exmachG Σ}, Persistent (exec_inv H1 H2)).
  Context (cinv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : exmachG Σ}, Persistent (crash_inv H1 H2)).

  Context (E: coPset).
  Context (nameIncl: nclose sourceN ⊆ E).
  (* TODO: we should get rid of rec_seq if we're not exploiting vertical comp anymore *)
  Context (recv: proc ExMach.Op unit).
  Context (recsingle: recover = rec_singleton recv).

  Context (refinement_triples:
             forall {H1 H2 T1 T2} j K `{LanguageCtx OpT T1 T2 Λa K} (e: proc OpT T1),
               j ⤇ K e ∗ (@exec_inv H1 H2) ⊢
                 WP compile e {{ v, j ⤇ K (Ret v) }}).

  Context (recv_triple:
             forall {H1 H2},
               (@crash_inv H1 H2) ⊢
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

  (*
  Context (inv_preserve_crash:
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          (∃ Hinv H0', @φinv Hcfg (@ExMachG Σ Hinv H0' (exm_disk_inG))) -∗
          ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={⊤}=∗ φinv _ _)).
   *)

  Context (exec_inv_preserve_crash:
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          exec_inv Hcfg Hex ={⊤, E}=∗ ∀ Hmem',
          (let Hex := ExMachG Σ (exm_invG) Hmem' (exm_disk_inG) in
              ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={E}=∗ crash_inner Hcfg Hex))).

  Context (crash_inv_preserve_crash:
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          crash_inv Hcfg Hex ={⊤, E}=∗ ∀ Hmem',
          (let Hex := ExMachG Σ (exm_invG) Hmem' (exm_disk_inG) in
              ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={E}=∗ crash_inner Hcfg Hex))).

  (* TODO: Much of this business is just to capture the fact that exec_inner/crash_inner
     should not really mention invariants, because those old invariants are 'dead' *)
  Context (crash_inner_inv :
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          (∃ Hinv, crash_inner Hcfg (ExMachG Σ Hinv (exm_mem_inG) (exm_disk_inG)))
          ={⊤}=∗ crash_inv Hcfg Hex)).

  Context (exec_inner_inv :
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ} Hinv,
          exec_inner Hcfg (ExMachG Σ Hinv (exm_mem_inG) (exm_disk_inG))
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
    -

      iSplit; first by eauto.
  iExists (fun cfgG s => ∃ (_ : exmachG Σ),
                     state_interp s ∗
                       (∃ (hM: gen_heapG addr nat Σ)
                            (Hmpf_eq : hM.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
                                       H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ nat_eq_dec nat_countable)) ,
            gen_heap_ctx init_zero ∗ crash_inner cfgG (ExMachG Σ _ hM (exm_disk_inG))))%I; auto.
  iIntros (invG0 Hcfg0).
  iMod ("Hpre" $! invG0 _ _) as (hM hD ??) "(Hstate0&H)".
  iExists (@ex_mach_interp _ hM hD).
  iIntros "!> (#Hsrc&Hpt0&Hstate)".
  iMod ("H" with "Hsrc Hstate") as "Hinv".
  iMod (exec_inner_inv (ExMachG Σ _ hM hD) _ with "Hinv") as "#Hinv".
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
  iModIntro. iIntros (invG Hcfg' ?? Hcrash) "Hinv0".
  iDestruct "Hinv0" as (HexmachG') "(Hinterp&Hinv0)".
  iDestruct "Hinv0" as (hM' Hmpf_eq') "(Hmc'&Hcrash_inner)".
  iClear "Hinv".
  iMod (crash_inner_inv (ExMachG Σ _
                                 hM' (exm_disk_inG)) Hcfg'
                         with "[Hcrash_inner]") as "#Hinv".
  { iIntros. simpl. iExists ( exmachG_irisG.(@iris_invG Op ExMach.State Σ)).
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
  iSplitL "Hinv".
  {
    iPoseProof (@wp_mono with "[Hinv]") as "H"; swap 1 2.
    { iApply recv_triple. iApply "Hinv". }
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
  iExists (fun cfgG s => ∃ (Hex : exmachG Σ),
                     state_interp s ∗
                       (∃ (hM: gen_heapG addr nat Σ)
                            (Hmpf_eq : hM.(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable) =
                                       H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ nat_eq_dec nat_countable))

                            (Hdpf_eq : (@exm_disk_inG Σ Hex).(@gen_heap_inG addr nat Σ nat_eq_dec nat_countable)=
                                       H.(@exm_preG_disk Σ).(@gen_heap_preG_inG addr nat Σ nat_eq_dec nat_countable)) ,
            gen_heap_ctx init_zero ∗ crash_inner cfgG (ExMachG Σ _ hM (exm_disk_inG))))%I; auto.
  iIntros (invG0 Hcfg0).
  iMod ("Hpre" $! invG0 _ _) as (hM hD ??) "(Hstate0&H)".
  iExists (@ex_mach_interp _ hM hD).
  iIntros "!> (#Hsrc&Hpt0&Hstate)".
  iMod ("H" with "Hsrc Hstate") as "Hinv".
  iMod (exec_inner_inv (ExMachG Σ _ hM hD) _ with "Hinv") as "#Hinv".
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
  iModIntro. iIntros (invG Hcfg' ?? Hcrash) "Hinv0".
  iDestruct "Hinv0" as (HexmachG') "(Hinterp&Hinv0)".
  iDestruct "Hinv0" as (hM' Hmpf_eq' Hmdpf_eq') "(Hmc'&Hcrash_inner)".
  iClear "Hinv".
  iMod (crash_inner_inv (ExMachG Σ _
                                 hM' (exm_disk_inG)) Hcfg'
                         with "[Hcrash_inner]") as "#Hinv".
  { iIntros. simpl. iExists ( exmachG_irisG.(@iris_invG Op ExMach.State Σ)).
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
  iSplitL "Hinv".
  {
    iPoseProof (@wp_mono with "[Hinv IH]") as "H"; swap 1 2.
    { iApply recv_triple. iApply "Hinv". }
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

Section test.

  Definition test := (_ <- write_mem 0 1; write_disk 0 1)%proc.
  Definition test_rec := (x <- read_mem 0; y <- read_disk 0;
                          assert (andb (Nat.eqb x 0) (negb (Nat.eqb y 2))))%proc.

  Context `{exmachG}.

  Definition EI := (∃ v, ⌜ v < 2 ⌝ ∗ 0 d↦ v )%I.

  Lemma test_spec N: {{{ inv N EI ∗ 0 m↦ 0 }}} test {{{ RET (); True }}}.
  Proof.
    iIntros (Φ) "(Hinv&mem) H". rewrite /test. wp_bind.
    iApply (wp_write_mem with "[$]"). iIntros "!> ?".
    iInv N as ">HEI".
    iDestruct "HEI" as (v ?) "Hd".
    iApply (wp_write_disk with "[$]"). iIntros "!> ? !>".
    iSplitR "H".
    - iExists 1. iNext. eauto.
    - by iApply "H".
  Qed.

  Lemma test_rec_spec N: {{{ inv N EI ∗ 0 m↦ 0 }}} test_rec {{{ RET (); True }}}.
    iIntros (Φ) "(Hinv&Hmem) H". rewrite /test_rec. wp_bind.
    iApply (wp_read_mem with "[$]"); iIntros "!> ?".
    wp_bind.
    iInv N as ">HEI".
    iDestruct "HEI" as (v ?) "Hd".
    iApply (wp_read_disk with "[$]"); iIntros "!> ? !>".
    iSplitR "H".
    - iExists v. iNext. eauto.
    - iApply wp_assert; auto.
      rewrite (Nat.eqb_refl).
      destruct (Nat.eqb_spec v 2); auto. lia.
  Qed.

End test.

Section closed.

  (* TODO: shorten and bundle up the re-usable reasoning here. *)
  Lemma adeq_closed:
    @recv_adequate _ _ _ ExMach.l NotStuck test test_rec init_state (λ v _, True) (λ _, True).
  Proof.
    eapply (exmach_recovery_adequacy exmachΣ) with (φinv := @EI _).
    - apply init_state_wf.
    - iIntros (?). iIntros "Hbig1 Hbig2".
      rewrite (big_opM_delete _ _ 0 0); last first.
      { rewrite /mem_state. apply init_zero_lookup_lt_zero. rewrite /size. lia. }
      rewrite (big_opM_delete _ (init_state.(disk_state)) 0 0); last first.
      { rewrite /mem_state. apply init_zero_lookup_lt_zero. rewrite /size. lia. }
      iDestruct "Hbig1" as "(Hzm&_)".
      iDestruct "Hbig2" as "(Hzd&_)".
      iMod (inv_alloc nroot _ EI with "[Hzd]") as "#H".
      { iExists O. iNext. iFrame. auto. }

      iModIntro.
      iSplitL "Hzm"; last iSplitR "".
      * iApply (test_spec with "[Hzm]"); iFrame; eauto.
      * iMod (@inv_open_timeless with "H") as "(HEI&_)".
        set_solver+. iApply @fupd_mask_weaken; first by set_solver; eauto.
        done.
      * iClear "H". iModIntro.
        iIntros (?) "HEI Hbig".
        rewrite (big_opM_delete _ _ 0 0); last first.
        { rewrite /mem_state. apply init_zero_lookup_lt_zero. rewrite /size. lia. }
        iDestruct "Hbig" as "(H&_)".
        iDestruct "HEI" as (H ?) "HEI".
        rewrite /EI. simpl. clear H.
        iMod (inv_alloc nroot ⊤ EI with "[HEI]") as "#H'".
        { iNext. rewrite /EI. auto. }
        iModIntro. iSplitL "H".
        ** iApply (test_rec_spec with "[H]"); iFrame; eauto.
        ** iMod (@inv_open_timeless with "H'") as "(HEI&_)".
           set_solver+. iApply @fupd_mask_weaken; first by set_solver; eauto.
           done.
    - auto.
  Qed.
End closed.

Print Assumptions adeq_closed.