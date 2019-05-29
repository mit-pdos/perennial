From iris.algebra Require Import auth gmap frac agree.
Require Import ExMach.Adequacy.
Import ExMach.
Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Layer.
    Import WeakestPre.

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
  Context `{CFG: cfgPreG OpT Λa Σ} `{HEX: exmachPreG Σ}.
  Context `{INV: Adequacy.invPreG Σ}.
  Context `{REG: inG Σ (csumR countingR (authR (optionUR (exclR unitC))))}.
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

End exmach_refinement_type.

Module exmach_refinement (eRT: exmach_refinement_type).

  Module RT <: refinement_type.
    Import eRT.
    Definition OpC := ExMach.Op.
    Definition Λc := ExMach.l.
    Definition OpT := OpT.
    Definition Λa := Λa.
    Definition impl := impl.
    Definition exmachG := exmachG.
    Definition Σ := Σ.
    Definition CFG := CFG.
    Definition INV := INV.
    Definition REG := REG.
    Definition Hinstance := @exmachG_irisG.
    Definition Hinstance_reg := @exm_treg_inG.
    Definition set_inv_reg Hex Hinv Hreg :=
      ExMachG Σ Hinv (@exm_mem_inG _ Hex) (@exm_disk_inG _ Hex) Hreg.

    Definition crash_inner := crash_inner. (* : cfgG eRT.Σ → WeakestPre.exmachG eRT.Σ → iProp eRT.Σ
      := (λ H1 H2, ∃ Hinv Hreg, crash_inner H1 (set_inv_reg H2 Hinv Hreg))%I. *)

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
    Definition init_absr := init_absr.


  End RT.

  Module RD := refinement_definitions RT.

  Import RT RD.

  Module RO : refinement_obligations RT.
    Module RD := RD.
    Import WeakestPre.
    Import RT RD.

    Lemma set_inv_reg_spec0:
             ∀ Hex, (set_inv_reg Hex (Hinstance Σ Hex).(@iris_invG OpC (State Λc) Σ)
                                                         (Hinstance_reg Σ Hex) = Hex).
    Proof. destruct Hex; auto. Qed.

    Lemma set_inv_reg_spec1:
      ∀ Hex Hinv Hreg, @iris_invG _ _ _ (Hinstance _ (set_inv_reg Hex Hinv Hreg)) = Hinv.
    Proof. trivial. Qed.

    Lemma set_inv_reg_spec2:
      ∀ Hex Hinv Hreg, Hinstance_reg _ (set_inv_reg Hex Hinv Hreg) = Hreg.
    Proof. trivial. Qed.

    Lemma set_inv_reg_spec3:
      ∀ Hex Hinv Hinv' Hreg Hreg', set_inv_reg (set_inv_reg Hex Hinv' Hreg') Hinv Hreg =
                       (set_inv_reg Hex Hinv Hreg).
    Proof. trivial. Qed.

    Lemma register_spec `{WeakestPre.exmachG Σ}: ∃ (Interp: OpState Λc → iProp Σ),
                (∀ n σ, @state_interp _ _ _ (Hinstance _ _) (n, σ)
                                     -∗ thread_count_interp n ∗ Interp σ) ∧
                ∀ n σ, thread_count_interp n ∗ Interp σ -∗ state_interp (n, σ).
    Proof. eexists. split; eauto using thread_reg1, thread_reg2. Qed.
    Definition refinement_op_triples := refinement_op_triples.

    (* This is just to convert from the old recv_triple style to the new one. *)
    Lemma recv_triple : recv_triple_type.
    Proof.
      rewrite /recv_triple_type.
      iIntros (???) "(#Hinv&Hreg&Hstart)".
      iPoseProof @eRT.recv_triple as "H".
      iSpecialize ("H" with "[$]").
      iApply (wp_wand with "H").
      iIntros (_) "H".
      iMod "H" as (σ2a σ2a') "(?&%&H)".
      iModIntro. iExists _, _. iFrame.
      iSplitR; first by iPureIntro.
      iIntros. rewrite /post_recv.
      iIntros (????) "((_&Hstate)&Hthread)". iModIntro. iExists _. iFrame.
      iIntros. iModIntro. by iMod ("H" with "[$]").
    Qed.

    Existing Instance eRT.HEX.
    Lemma init_exec_inner : init_exec_inner_type.
    Proof.
      rewrite /init_exec_inner_type.
      iIntros (σ1a σ1c Hinit ???).
      iMod (gen_heap_strong_init (mem_state σ1c)) as (hM Hmpf_eq) "(Hmc&Hm)".
      iMod (gen_heap_strong_init (disk_state σ1c)) as (hD Hdpf_eq) "(Hdc&Hd)".
      iPoseProof (eRT.init_exec_inner σ1a σ1c Hinit (ExMachG Σ _ hM hD _) _) as "H".
      iModIntro. iExists (ExMachG Σ _ hM hD _). iIntros "(Hsource1&Hsource2&Hthread)".
      iMod ("H" with "[Hm Hd Hsource1 Hsource2]") as "Hinner".
      { iFrame.  iSplitL "Hm".
        { rewrite -Hmpf_eq. iApply mem_init_to_bigOp; auto. }
        { rewrite -Hdpf_eq. iApply disk_init_to_bigOp; auto. }
      }
      iFrame. simpl.
      iModIntro. iExists _, _. iFrame.
      iPureIntro;
      edestruct (eRT.init_wf) as (Hwf1&Hwf2); eauto.
      split_and!; eauto; intros i.
      * destruct (Hwf1 i); intuition.
      * destruct (Hwf2 i); intuition.
    Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    rewrite /exec_inv_preserve_crash_type.
    iIntros (??) "Hinv".
    iPoseProof (eRT.exec_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod (gen_heap_strong_init (init_zero)) as (hM Hmpf_eq) "(Hmc&Hm)".
    iMod ("Hinv_post") as "Hinv_post".
    iModIntro. iIntros (?).
    iMod ("Hinv_post" with "[Hm]") as "Hinv_post".
    { rewrite -Hmpf_eq. iApply @mem_init_to_bigOp; auto. }
    iModIntro.
    iIntros (n σ σ' Hcrash) "(Hmach&Hthread)".
    iExists (ExMachG Σ (@exm_invG _ Hex) hM (@exm_disk_inG _ Hex)
                     (@exm_treg_inG _ Hex)).
    iModIntro. iFrame. iDestruct "Hmach" as "(?&Hdisk)".
    inversion Hcrash. subst.
    iDestruct "Hdisk" as (??) "(?&?&%&%&%&%)". iFrame.
    iSplitR ""; last done.
    iExists _, _. iFrame.
    iPureIntro; split_and!; [ auto | auto | | assumption ].
    intros ? Hsome. apply not_le; intros Hge.
    rewrite init_zero_lookup_ge_None in Hsome; last by lia.
    apply is_Some_None in Hsome; auto.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    rewrite /crash_inv_preserve_crash_type.
    iIntros (???) "Hinv".
    iPoseProof (eRT.crash_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod (gen_heap_strong_init (init_zero)) as (hM Hmpf_eq) "(Hmc&Hm)".
    iMod ("Hinv_post") as "Hinv_post".
    iModIntro. iIntros (?).
    iMod ("Hinv_post" with "[Hm]") as "Hinv_post".
    { rewrite -Hmpf_eq. iApply @mem_init_to_bigOp; auto. }
    iModIntro.
    iIntros (n σ σ' Hcrash) "(Hmach&Hthread)".
    iExists (ExMachG Σ (@exm_invG _ Hex) hM (@exm_disk_inG _ Hex)
                     (@exm_treg_inG _ Hex)).
    iModIntro. iFrame. iDestruct "Hmach" as "(?&Hdisk)".
    inversion Hcrash. subst.
    iDestruct "Hdisk" as (??) "(?&?&%&%&%&%)". iFrame.
    iSplitR ""; last done.
    iExists _, _. iFrame.
    iPureIntro; split_and!; [ auto | auto | | assumption ].
    intros ? Hsome. apply not_le; intros Hge.
    rewrite init_zero_lookup_ge_None in Hsome; last by lia.
    apply is_Some_None in Hsome; auto.
  Qed.

  Lemma state_interp_no_inv : state_interp_no_inv_type.
  Proof. done. Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    iIntros (??) "Hinner".
    iPoseProof (eRT.crash_inner_inv with "Hinner") as "Hinv".
    eauto.
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    iIntros (??) "Hinner".
    iPoseProof (eRT.exec_inner_inv with "Hinner") as "Hinv".
    eauto.
  Qed.


  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "Hdone Hinv".
    iPoseProof (eRT.exec_inv_preserve_finish) as "H".
    iMod ("H" $! _ _ with "[$] [$]") as (??) "(?&?&Hinv_post)".
    iModIntro. iExists _, _. iFrame. iIntros.
    iIntros (??? Hfinish ??) "((?&Hdisk)&?)".
    inversion Hfinish. subst.
    iMod (gen_heap_strong_init (init_zero)) as (hM Hmpf_eq) "(Hmc&Hm)".
    iDestruct "Hdisk" as (??) "(_&?&%&%&%&%)". iFrame.
    iModIntro.
    iExists (ExMachG Σ (@exm_invG _ Hex) hM (@exm_disk_inG _ Hex)
                     (@exm_treg_inG _ Hex)).
    iSplitR "Hinv_post Hm".
    {
      iFrame.
      iExists init_zero, _. iFrame.
      iPureIntro; split_and!; [ auto | auto | | assumption ].
      intros ? Hsome. apply not_le; intros Hge.
      rewrite init_zero_lookup_ge_None in Hsome; last by lia.
      apply is_Some_None in Hsome; auto.
    }
    iIntros "Hstate". iSpecialize ("Hinv_post" with "[Hstate Hm]").
    { iFrame. iDestruct "Hstate" as "(?&?)". iFrame.
      rewrite -Hmpf_eq. iApply @mem_init_to_bigOp; auto. }
    eauto.
  Qed.
  End RO.

  Module R := refinement RT RO.


  Export RO.

End exmach_refinement.

