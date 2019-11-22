From iris.algebra Require Import auth gmap frac agree.
Require Export CSL.WeakestPre CSL.Lifting CSL.Adequacy CSL.RefinementIdempotenceFunModule CSL.Leased_Heap.
Require Export ReplicatedDisk.TwoDiskAPI ReplicatedDisk.WeakestPre.
Import TwoDisk.
Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Layer.

Class exmachPreG Σ := ExMachPreG {
  exm_preG_iris :> invPreG Σ;
  exm_preG_mem :> gen_heapPreG nat nat Σ;
  exm_preG_disk :> leased_heapPreG nat nat Σ;
  exm_preG_status_inG :> inG Σ (csumR (exclR unitO) (agreeR (diskIdC)));
  exm_preG_treg_inG :> inG Σ (csumR countingR (authR (optionUR (exclR unitO))));
}.

Definition exmachΣ : gFunctors := #[invΣ; gen_heapΣ nat nat; leased_heapΣ nat nat;
                                    GFunctor (csumR (exclR unitO) (agreeR (diskIdC)));
                                    GFunctor (csumR countingR (authR (optionUR (exclR unitO))))].
Instance subG_exmachPreG {Σ} : subG exmachΣ Σ → exmachPreG Σ.
Proof. solve_inG. Qed.

Import TwoDisk.

Module Type twodisk_refinement_type.
  Context (OpT: Type → Type).
  Context (Λa: Layer OpT).
  Context (impl: LayerImpl TwoDisk.Op OpT).
  Context (Σ: gFunctors).
  Notation compile_op := (compile_op impl).
  Notation compile_rec := (compile_rec impl).
  Notation compile_seq := (compile_seq impl).
  Notation compile := (compile impl).
  Notation recover := (recover impl).
  Notation compile_proc_seq := (compile_proc_seq impl).
  Context `{CFG: cfgPreG OpT Λa Σ} `{HEX: exmachPreG Σ}.
  Context `{INV: Adequacy.invPreG Σ}.
  Context `{REG: inG Σ (csumR countingR (authR (optionUR (exclR unitO))))}.
  Context (crash_inner: forall {_ : @cfgG OpT Λa Σ} {_: exmachG Σ}, iProp Σ).
  Context (exec_inner: forall {_ : @cfgG OpT Λa Σ} {_: exmachG Σ}, iProp Σ).
  Context (crash_param: forall (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ), Type).
  Context (crash_inv: forall {H1 : @cfgG OpT Λa Σ} {H2 : exmachG Σ},
              @crash_param _ H2 → iProp Σ).
  Context (crash_starter: forall {H1 : @cfgG OpT Λa Σ} {H2 : exmachG Σ},
              @crash_param _ H2 → iProp Σ).
  Context (exec_inv: forall {_ : @cfgG OpT Λa Σ} {_ : exmachG Σ}, iProp Σ).

  Context (E: coPset).
  Context (recv: proc TwoDisk.Op unit).
  Context (init_absr: Λa.(OpState) → TwoDisk.State → Prop).
End twodisk_refinement_type.

Module twodisk_refinement_definitions (eRT: twodisk_refinement_type).
  Import eRT.

  Definition recv_triple_type :=
             forall H1 H2 param,
               (@crash_inv H1 H2 param) ∗ Registered ∗ (@crash_starter H1 H2 param) ⊢
                    WP recv @ NotStuck; ⊤ {{ v, |={⊤,E}=> ∃ σ2a σ2a', source_state σ2a
                    ∗ ⌜Λa.(crash_step) σ2a (Val σ2a' tt)⌝ ∗
                    ∀ `{Hcfg': cfgG OpT Λa Σ} (Hinv': invG Σ) tr',
                      source_ctx ∗ source_state σ2a'  ={⊤}=∗
                      exec_inner Hcfg' (ExMachG Σ Hinv' exm_mem_inG
                                                        exm_disk0_inG exm_disk1_inG exm_status_inG
                                                        tr')
                                               }}.

  Definition refinement_op_triples_type :=
             forall H1 H2 T1 T2 j K `{LanguageCtx OpT T1 T2 Λa K} (op: OpT T1),
               j ⤇ K (Call op) ∗ Registered ∗ (@exec_inv H1 H2) ⊢
                 WP compile (Call op) {{ v, j ⤇ K (Ret v) ∗ Registered }}.

  Definition init_exec_inner_type :=
    ∀ σ1a σ1c, init_absr σ1a σ1c →
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          (([∗ map] i ↦ v ∈ init_zero, i m↦ v) ∗
           ([∗ map] i ↦ v ∈ init_zero, i d0↦ v ∗ lease0 i v) ∗
           ([∗ map] i ↦ v ∈ init_zero, i d1↦ v ∗ lease1 i v) ∗
           source_ctx ∗ source_state σ1a) ={⊤}=∗ exec_inner _ _).

  Definition exec_inv_preserve_crash_type :=
      (∀ `(Hex: exmachG Σ) `(Hcfg: cfgG OpT Λa Σ),
          exec_inv Hcfg Hex ={⊤, E}=∗ ∀ Hmem' Hreg',
          (let Hex := ExMachG Σ (exm_invG) Hmem'
                              (next_leased_heapG (hG := (exm_disk0_inG)))
                              (next_leased_heapG (hG := (exm_disk1_inG)))
                              (exm_status_inG)
                              Hreg' in
              ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={E}=∗ crash_inner Hcfg Hex)).

  Definition crash_inv_preserve_crash_type :=
      (∀ `(Hex: exmachG Σ) `(Hcfg: cfgG OpT Λa Σ) param,
          crash_inv Hcfg Hex param ={⊤, E}=∗ ∀ Hmem' Hreg',
          (let Hex := ExMachG Σ (exm_invG) Hmem'
                              (next_leased_heapG (hG := (exm_disk0_inG)))
                              (next_leased_heapG (hG := (exm_disk1_inG)))
                              (exm_status_inG)
                              Hreg' in
              ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={E}=∗ crash_inner Hcfg Hex)).

  Definition crash_inner_inv_type :=
      (∀ `(Hex: exmachG Σ) `(Hcfg: cfgG OpT Λa Σ),
          (∃ Hinv, crash_inner Hcfg (ExMachG Σ Hinv (exm_mem_inG)
                                             (exm_disk0_inG) (exm_disk1_inG) (exm_status_inG)
                                             (exm_treg_inG))) ∗
          source_ctx ={⊤}=∗ ∃ param, crash_inv Hcfg Hex param ∗ crash_starter Hcfg Hex param).

  Definition exec_inner_inv_type :=
      (∀ `(Hex: exmachG Σ) `(Hcfg: cfgG OpT Λa Σ),
          (∃ Hinv, exec_inner Hcfg (ExMachG Σ Hinv (exm_mem_inG)
                                             (exm_disk0_inG) (exm_disk1_inG) (exm_status_inG)
                                             (exm_treg_inG))) ∗
          source_ctx ={⊤}=∗ exec_inv Hcfg Hex).

  Definition exec_inv_preserve_finish_type :=
      (∀ `(Hex: exmachG Σ) `(Hcfg: cfgG OpT Λa Σ),
          AllDone -∗ exec_inv Hcfg Hex ={⊤, E}=∗ ∃ (σ2a σ2a' : Λa.(OpState)), source_state σ2a
          ∗ ⌜Λa.(finish_step) σ2a (Val σ2a' tt)⌝ ∗
          ∀ `{Hcfg': cfgG OpT Λa Σ} (Hinv': invG Σ) Hmem' Hreg',
            (let Hex := ExMachG Σ Hinv' Hmem'
                                (next_leased_heapG (hG := (exm_disk0_inG)))
                                (next_leased_heapG (hG := (exm_disk1_inG)))
                                (exm_status_inG)
                                Hreg' in
            source_ctx∗ source_state σ2a' ∗ ([∗ map] i ↦ v ∈ init_zero, i m↦ v) ={⊤}=∗
               exec_inner Hcfg' Hex))%I.

End twodisk_refinement_definitions.


Module Type twodisk_refinement_obligations (eRT: twodisk_refinement_type).

  Module eRD := twodisk_refinement_definitions eRT.
  Import eRT.
  Import eRD.

  Context (recsingle: recover = rec_singleton eRT.recv).

  Context (nameIncl: nclose sourceN ⊆ eRT.E).
  Context (einv_persist: forall {H1 : @cfgG OpT Λa eRT.Σ} {H2 : _},
              Persistent (exec_inv H1 H2)).
  Context (cinv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _}
            {P: crash_param _ _}, Persistent (crash_inv H1 H2 P)).

  Context (exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx).

  Context (recv_triple: recv_triple_type).
  Context (init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → σ1c = TwoDisk.init_state).
  Context (refinement_op_triples: refinement_op_triples_type).
  Context (init_exec_inner: init_exec_inner_type).
  Context (exec_inv_preserve_crash: exec_inv_preserve_crash_type).
  Context (crash_inv_preserve_crash: crash_inv_preserve_crash_type).
  Context (exec_inner_inv: exec_inner_inv_type).
  Context (crash_inner_inv: crash_inner_inv_type).
  Context (exec_inv_preserve_finish : exec_inv_preserve_finish_type).
End twodisk_refinement_obligations.

Module twodisk_refinement (eRT: twodisk_refinement_type) (eRO: twodisk_refinement_obligations eRT).

  Module RT <: refinement_type.
    Import eRT.
    Definition OpC := TwoDisk.Op.
    Definition Λc := TwoDisk.l.
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
      ExMachG Σ Hinv (@exm_mem_inG _ Hex) (@exm_disk0_inG _ Hex) (@exm_disk1_inG _ Hex)
              (exm_status_inG) Hreg.

    Definition crash_inner := crash_inner.
    Definition exec_inner := exec_inner.
    Definition crash_inv := crash_inv.
    Definition crash_param := crash_param.
    Definition crash_starter := crash_starter.
    Definition exec_inv := exec_inv.
    Definition E := E.
    Definition recv := recv.
    Definition init_absr := init_absr.

  End RT.

  Module RD := refinement_definitions RT.

  Import RT RD.

  Module RO : refinement_obligations RT.
    Module RD := RD.
    Import WeakestPre.
    Import RT RD.

    Definition nameIncl := eRO.nameIncl.
    Definition einv_persist := eRO.einv_persist.
    Definition cinv_persist := eRO.cinv_persist.
    Existing Instances einv_persist cinv_persist.
    Definition recsingle := eRO.recsingle.
    Definition refinement_op_triples := eRO.refinement_op_triples.
    Definition exec_inv_source_ctx := eRO.exec_inv_source_ctx.


    Lemma set_inv_reg_spec0:
             ∀ Hex, (set_inv_reg Hex (Hinstance Σ Hex).(@iris_invG OpC (Layer.State Λc) Σ)
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

    (* This is just to convert from the old recv_triple style to the new one. *)
    Lemma recv_triple : recv_triple_type.
    Proof.
      rewrite /recv_triple_type.
      iIntros (???) "(#Hinv&Hreg&Hstart)".
      iPoseProof @eRO.recv_triple as "H".
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
      iMod (leased_heap_strong_init init_zero) as (hD0 Hdpf_eq0) "(Hdc0&Hd0)".
      iMod (leased_heap_strong_init init_zero) as (hD1 Hdpf_eq1) "(Hdc1&Hd1)".
      iMod (own_alloc (Cinl (Excl tt))) as (status_name) "Hstat".
      { constructor. }
      set (hStatus := {| disk_status_name := status_name; disk_status_inG := _ |}).
      iPoseProof (eRO.init_exec_inner σ1a σ1c Hinit (ExMachG Σ _ hM hD0 hD1 hStatus _) _) as "H".
      iModIntro. iExists (ExMachG Σ _ hM hD0 hD1 hStatus _).
      iIntros "(Hsource1&Hsource2&Hthread)".
      iMod ("H" with "[Hm Hd0 Hd1 Hsource1 Hsource2]") as "Hinner".
      { iFrame.
        rewrite !(eRO.init_wf _ _ Hinit).
        iSplitL "Hm"; [| iSplitL "Hd0"].
        { rewrite -Hmpf_eq. iApply (mem_init_to_bigOp with "Hm"); auto. }
        { iApply (big_sepM_mono with "Hd0"). iIntros (???) "(?&?&?)". iFrame. }
        { iApply (big_sepM_mono with "Hd1"). iIntros (???) "(?&?&?)". iFrame. }
      }
      rewrite !(eRO.init_wf _ _ Hinit); auto.
      iFrame. simpl.
      iModIntro. iExists _, _, _. iFrame.
      iPureIntro; repeat split_and! => //=; eauto using wf_init_zero.
    Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    rewrite /exec_inv_preserve_crash_type.
    iIntros (??) "Hinv".
    iPoseProof (eRO.exec_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod (gen_heap_strong_init (init_zero)) as (hM Hmpf_eq) "(Hmc&Hm)".
    iMod ("Hinv_post") as "Hinv_post".
    iModIntro. iIntros (?).
    iMod ("Hinv_post" with "[Hm]") as "Hinv_post".
    { rewrite -Hmpf_eq. iApply (mem_init_to_bigOp with "Hm"); auto. }
    iIntros (n σ) "(Hmach&Hthread)".
    iModIntro.
    iIntros (σ' Hcrash).
    iExists (ExMachG Σ (@exm_invG _ Hex) hM
                     (next_leased_heapG (hG := (@exm_disk0_inG _ Hex)))
                     (next_leased_heapG (hG := (@exm_disk1_inG _ Hex)))
                     (@exm_status_inG _ Hex)
                     (@exm_treg_inG _ Hex)).
    iFrame. iDestruct "Hmach" as "(?&Hdisk)".
    inversion Hcrash. subst.
    iDestruct "Hdisk" as (???) "(?&?&?&?&%&%&%&%)". iFrame.
    iSplitR ""; last done.
    iExists _, _, _. iFrame.
    iPureIntro; split_and!; [ auto | auto |].
    split; [apply wf_init_zero | assumption].
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    rewrite /crash_inv_preserve_crash_type.
    iIntros (???) "Hinv".
    iPoseProof (eRO.crash_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod (gen_heap_strong_init (init_zero)) as (hM Hmpf_eq) "(Hmc&Hm)".
    iMod ("Hinv_post") as "Hinv_post".
    iModIntro. iIntros (?).
    iMod ("Hinv_post" with "[Hm]") as "Hinv_post".
    { rewrite -Hmpf_eq. iApply (mem_init_to_bigOp with "Hm"); auto. }
    iIntros (n σ) "(Hmach&Hthread)".
    iModIntro.
    iIntros (σ' Hcrash).
    iExists (ExMachG Σ (@exm_invG _ Hex) hM
                     (next_leased_heapG (hG := (@exm_disk0_inG _ Hex)))
                     (next_leased_heapG (hG := (@exm_disk1_inG _ Hex)))
                     (@exm_status_inG _ Hex)
                     (@exm_treg_inG _ Hex)).
    iFrame. iDestruct "Hmach" as "(?&Hdisk)".
    inversion Hcrash. subst.
    iDestruct "Hdisk" as (???) "(?&?&?&?&%&%&%&%)". iFrame.
    iSplitR ""; last done.
    iExists _, _, _. iFrame.
    iPureIntro; split_and!; [ auto | auto |].
    split; [apply wf_init_zero | assumption].
  Qed.

  Lemma state_interp_no_inv : state_interp_no_inv_type.
  Proof. done. Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    iIntros (??) "Hinner".
    iPoseProof (eRO.crash_inner_inv with "Hinner") as "Hinv".
    eauto.
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    iIntros (??) "Hinner".
    iPoseProof (eRO.exec_inner_inv with "Hinner") as "Hinv".
    eauto.
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "Hdone Hinv".
    iPoseProof (eRO.exec_inv_preserve_finish) as "H".
    iMod ("H" $! _ _ with "[$] [$]") as (??) "(?&?&Hinv_post)".
    iModIntro. iExists _, _. iFrame. iIntros.
    iIntros (??? Hfinish ??) "((?&Hdisk)&?)".
    inversion Hfinish. subst.
    iMod (gen_heap_strong_init (init_zero)) as (hM Hmpf_eq) "(Hmc&Hm)".
    iDestruct "Hdisk" as (???) "(_&?&?&?&%&%&%&%)". iFrame.
    iModIntro.
    iExists (ExMachG Σ (@exm_invG _ Hex) hM
                     (next_leased_heapG (hG := (@exm_disk0_inG _ Hex)))
                     (next_leased_heapG (hG := (@exm_disk1_inG _ Hex)))
                     (@exm_status_inG _ Hex)
                     (@exm_treg_inG _ Hex)).
    iSplitR "Hinv_post Hm".
    {
      iFrame.
      iExists init_zero, _, _. iFrame.
      iPureIntro; split_and!; [ auto | auto |].
      split; [apply wf_init_zero | assumption].
    }
    iIntros "Hstate". iSpecialize ("Hinv_post" with "[Hstate Hm]").
    { iFrame. iDestruct "Hstate" as "(?&?)". iFrame.
      rewrite -Hmpf_eq. iApply (mem_init_to_bigOp with "Hm"); auto. }
    eauto.
  Qed.
  End RO.

  Module R := refinement RT RO.


  Export R.

End twodisk_refinement.
