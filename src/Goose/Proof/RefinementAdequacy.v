From iris.algebra Require Import auth gmap frac agree.
Require Import Goose.Proof.Interp.
Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Layer.
From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
Require Export CSL.WeakestPre CSL.Lifting CSL.Adequacy CSL.RefinementAdequacy CSL.RefinementIdempotenceModule.
Import Data.
Import Filesys.FS.
Import GoLayer.Go.


Class fsPreG (m: GoModel) {wf: GoModelWf m} Σ :=
  FsPreG {
      go_fs_dlocks_preG :> Count_Heap.gen_heapPreG string unit Σ;
      go_fs_dirs_preG :> gen_heapPreG string (gset string) Σ;
      go_fs_paths_preG :> gen_dirPreG string string (Inode) Σ;
      go_fs_inodes_preG :> gen_heapPreG Inode (List.list byte) Σ;
      go_fs_fds_preG :> gen_heapPreG File (Inode * OpenMode) Σ;
      go_fs_domalg_preG :> ghost_mapG (discreteC (gset string)) Σ;
}.

Definition fsΣ (m: GoModel) {wf: GoModelWf m} : gFunctors :=
  #[gen_heapΣ string (gset string);
    Count_Heap.gen_heapΣ string unit;
    gen_dirΣ string string (Inode);
    gen_heapΣ Inode (List.list byte);
    gen_heapΣ File (Inode * OpenMode);
    ghost_mapΣ (discreteC (gset string))
   ].

Global Instance subG_fsPreG m {wf: GoModelWf m} {Σ} : subG (fsΣ m) Σ → (fsPreG m) Σ.
Proof. solve_inG. Qed.

Class goosePreG (goose_model: GoModel) {wf: GoModelWf goose_model} Σ := GoosePreG {
  goose_preG_iris :> invPreG Σ;
  goose_preG_heap :> Count_Heap.gen_heapPreG (sigT Ptr) (sigT ptrRawModel) Σ;
  goose_preG_fs :> fsPreG goose_model Σ;
  goose_preG_global :> ghost_mapG (discreteC (sliceLockC)) Σ;
  goose_preG_treg_inG :> inG Σ (csumR countingR (authR (optionUR (exclR unitC))));
}.

Definition gooseΣ (m: GoModel) {wf: GoModelWf m} : gFunctors :=
  #[invΣ; fsΣ m; gen_typed_heapΣ Ptr ptrRawModel; ghost_mapΣ (discreteC (sliceLockC));
      GFunctor (csumR countingR (authR (optionUR (exclR unitC))))].
Global Instance subG_goosePreG (m: GoModel) {wf: GoModelWf m} {Σ} : subG (gooseΣ m) Σ → goosePreG m Σ.
Proof. solve_inG. Qed.

Module Type goose_refinement_type.
  Context (OpT: Type → Type).
  Context (Λa: Layer OpT).
  Context (gm: GoModel).
  Context (gmWf: GoModelWf gm).
  Context (impl: LayerImplRel GoLayer.Op OpT).
  Context (Σ: gFunctors).
  Notation compile_rel_base := (compile_rel_base impl).
  Notation compile_rel_proc_seq := (compile_rel_proc_seq impl).
  Notation compile_rel := (compile_rel impl).
  Notation recover := (recover_rel impl).
  Notation compile_proc_seq := (compile_proc_seq impl).
  Context `{CFG: cfgPreG OpT Λa Σ} `{HEX: @goosePreG gm gmWf Σ}.
  Context `{INV: Adequacy.invPreG Σ}.
  Context `{REG: inG Σ (csumR countingR (authR (optionUR (exclR unitC))))}.
  Context (crash_inner: forall {_ : @cfgG OpT Λa Σ} {_: gooseG gm Σ}, iProp Σ).
  Context (exec_inner: forall {_ : @cfgG OpT Λa Σ} {_: gooseG gm Σ}, iProp Σ).
  Context (crash_param: forall (_ : @cfgG OpT Λa Σ) (_ : gooseG gm Σ), Type).
  Context (crash_inv: forall {H1 : @cfgG OpT Λa Σ} {H2 : gooseG gm Σ},
              @crash_param _ H2 → iProp Σ).
  Context (crash_starter: forall {H1 : @cfgG OpT Λa Σ} {H2 : gooseG gm Σ},
              @crash_param _ H2 → iProp Σ).
  Context (exec_inv: forall {_ : @cfgG OpT Λa Σ} {_ : gooseG gm Σ}, iProp Σ).

  Context (E: coPset).
  Context (recv: proc GoLayer.Op unit).
  Context (init_absr: Λa.(OpState) → State → Prop).
End goose_refinement_type.

Module goose_refinement_definitions (eRT: goose_refinement_type).
  Import eRT.
  Existing Instances gm gmWf.

  Definition recv_triple_type :=
             forall H1 H2 param,
               (@crash_inv H1 H2 param) ∗ Registered ∗ (@crash_starter H1 H2 param) ⊢
                    WP recv @ NotStuck; ⊤ {{ v, |={⊤,E}=> ∃ σ2a σ2a', source_state σ2a
                    ∗ ⌜Proc.crash_step Λa σ2a (Val σ2a' tt)⌝ ∗
                    ∀ `{Hcfg': cfgG OpT Λa Σ} (Hinv': invG Σ) tr',
                      source_ctx ∗ source_state σ2a'  ={⊤}=∗
                      exec_inner Hcfg' (GooseG _ _ Σ Hinv' go_heap_inG go_fs_inG go_global_inG tr')
                                               }}.

  Definition refinement_base_triples_type :=
             forall H1 H2 T1 T2 j K `{LanguageCtx OpT T1 T2 Λa K} (p: proc OpT T1) p',
               compile_rel_base p p' →
               j ⤇ K p ∗ Registered ∗ (@exec_inv H1 H2) ⊢
                 WP p' {{ v, j ⤇ K (Ret v) ∗ Registered }}.

  Definition init_wf_type :=
             ∀ σ1a σ1c, init_absr σ1a σ1c →
                        dom (gset string) σ1c.(fs).(dirents) =
                        dom (gset string) σ1c.(fs).(dirlocks) ∧
                        (∀ s l, σ1c.(fs).(dirlocks) !! s = Some l → fst l = Unlocked) ∧
                        σ1c.(maillocks) = None.

  (* Helper to update collection of ghost algebra for file system to use new
     "generation" mapping for fds/dlocks post crash. *)
  Definition crash_fsG {Σ} (curr: @fsG _ _ Σ) newDirLocks newFds : @fsG _ _ Σ :=
    FsG _ _ _ newDirLocks (go_fs_dirs_inG) (go_fs_paths_inG) (go_fs_inodes_inG)
        newFds (go_fs_domalg_inG) (go_fs_dom_name).

  Definition init_exec_inner_type := ∀ σ1a σ1c, init_absr σ1a σ1c →
      (∀ (Hex: @gooseG gm gmWf Σ) `(Hcfg: cfgG OpT Λa Σ),
          (([∗ map] d ↦ ents ∈ σ1c.(fs).(dirents), d ↦ dom (gset string) ents) ∗
          rootdir ↦{-1} dom (gset string) σ1c.(fs).(dirents) ∗
          ([∗ set] dir ∈ dom (gset string) σ1c.(fs).(dirents), dir ↦ Unlocked) ∗
           source_ctx ∗ source_state σ1a ∗ global ↦ None) ={⊤}=∗ exec_inner _ _).

  Definition exec_inv_preserve_crash_type :=
      (∀ (Hex: @gooseG gm gmWf Σ) `(Hcfg: cfgG OpT Λa Σ),
          exec_inv Hcfg Hex ={⊤, E}=∗ ∀ Hmem' Hdlocks' Hfds' Hreg' Hglobal',
            (let Hex := GooseG _ _ Σ (go_invG) Hmem' (crash_fsG _ Hdlocks' Hfds') Hreg' Hglobal' in
           (∃ S, rootdir ↦{-1} S ∗ [∗ set] dir ∈ S, dir ↦ Unlocked) ∗
           global ↦ None ={E}=∗ crash_inner Hcfg Hex)).

  Definition crash_inv_preserve_crash_type :=
      (∀ (Hex: @gooseG gm gmWf Σ) `(Hcfg: cfgG OpT Λa Σ) param,
          crash_inv Hcfg Hex param ={⊤, E}=∗ ∀ Hmem' Hdlocks' Hfds' Hreg' Hglobal',
          (let Hex := GooseG _ _ Σ (go_invG) Hmem' (crash_fsG _ Hdlocks' Hfds') Hreg' Hglobal' in
           (∃ S, rootdir ↦{-1} S ∗ [∗ set] dir ∈ S, dir ↦ Unlocked) ∗
           global ↦ None ={E}=∗ crash_inner Hcfg Hex)).

  Definition crash_inner_inv_type :=
      (∀ (Hex: @gooseG gm gmWf Σ) `(Hcfg: cfgG OpT Λa Σ),
          (∃ Hinv, crash_inner Hcfg (GooseG _ _ Σ Hinv (go_heap_inG) (go_fs_inG)
                                            (go_global_inG) (go_treg_inG))) ∗
          source_ctx ={⊤}=∗ ∃ param, crash_inv Hcfg Hex param ∗ crash_starter Hcfg Hex param).

  Definition exec_inner_inv_type :=
      (∀ (Hex: @gooseG gm gmWf Σ) `(Hcfg: cfgG OpT Λa Σ),
          (∃ Hinv, exec_inner Hcfg (GooseG _ _ Σ Hinv (go_heap_inG) (go_fs_inG)
                                           (go_global_inG) (go_treg_inG))) ∗
          source_ctx ={⊤}=∗ exec_inv Hcfg Hex).

  Definition exec_inv_preserve_finish_type :=
      (∀ (Hex: @gooseG gm gmWf Σ) `(Hcfg: cfgG OpT Λa Σ),
          AllDone -∗ exec_inv Hcfg Hex ={⊤, E}=∗ ∃ (σ2a σ2a' : Λa.(OpState)), source_state σ2a
          ∗ ⌜Λa.(finish_step) σ2a (Val σ2a' tt)⌝ ∗
          ∀ `{Hcfg': cfgG OpT Λa Σ} (Hinv': invG Σ) Hmem' Hdlocks' Hfds' Hreg' Hglobal',
            (let Hex := GooseG _ _ Σ Hinv' Hmem' (crash_fsG _ Hdlocks' Hfds') Hreg' Hglobal' in
             source_ctx ∗ source_state σ2a' ∗
             (∃ S, rootdir ↦{-1} S ∗ [∗ set] dir ∈ S, dir ↦ Unlocked) ∗
             global ↦ None ={⊤}=∗ exec_inner Hcfg' Hex))%I.

End goose_refinement_definitions.



Module Type goose_refinement_obligations (eRT: goose_refinement_type).

  Module eRD := goose_refinement_definitions eRT.
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
  Context (init_wf: init_wf_type).
  Context (refinement_base_triples: refinement_base_triples_type).
  Context (init_exec_inner: init_exec_inner_type).
  Context (exec_inv_preserve_crash: exec_inv_preserve_crash_type).
  Context (crash_inv_preserve_crash: crash_inv_preserve_crash_type).
  Context (exec_inner_inv: exec_inner_inv_type).
  Context (crash_inner_inv: crash_inner_inv_type).
  Context (exec_inv_preserve_finish : exec_inv_preserve_finish_type).
End goose_refinement_obligations.

Module goose_refinement (eRT: goose_refinement_type) (eRO: goose_refinement_obligations eRT).
  Module eRD := goose_refinement_definitions eRT.

  Module RT <: refinement_type.
    Import eRT.
    Definition OpC := GoLayer.Op.
    Definition Λc := GoLayer.Go.l.
    Definition OpT := OpT.
    Definition Λa := Λa.
    Definition impl := impl.
    Definition exmachG := @gooseG gm gmWf.
    Definition Σ := Σ.
    Definition CFG := CFG.
    Definition INV := INV.
    Definition REG := REG.
    Definition Hinstance := @gooseG_irisG _ _.
    Definition Hinstance_reg := @go_treg_inG _ _.
    Definition set_inv_reg Hex Hinv Hreg :=
      GooseG _ _ Σ Hinv (@go_heap_inG _ _ _ Hex) (@go_fs_inG _ _ _ Hex)
             (@go_global_inG _ _ _ Hex) Hreg.

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
    Definition refinement_base_triples := eRO.refinement_base_triples.
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

    Existing Instance Hinstance.
    Lemma register_spec `{@gooseG eRT.gm _ Σ}: ∃ (Interp: OpState Λc → iProp Σ),
                (∀ n σ, @state_interp _ _ _ (Hinstance _ _) (n, σ)
                                     -∗ thread_count_interp n ∗ Interp σ) ∧
                ∀ n σ, thread_count_interp n ∗ Interp σ -∗ state_interp (n, σ).
    Proof. eexists. split; [ eapply Interp.thread_reg1 | eapply Interp.thread_reg2 ]. Qed.

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
      iMod (gen_typed_heap_strong_init (σ1c.(fs).(heap).(allocs)))
        as (hM Hmpf_eq) "(Hmc&Hm)".
      iMod (gen_heap_strong_init (fmap (dom (gset string)) (σ1c.(fs).(dirents))))
        as (hD Hdpf_eq) "(Hdc&Hd)".
      iMod (gen_heap_strong_init (σ1c.(fs).(fds))) as (hFDs HFDpf_eq) "(Hfdc&Hfd)".
      iMod (gen_heap_strong_init (σ1c.(fs).(inodes))) as (hIs HIpf_eq) "(Hidc&Hi)".
      iMod (gen_dir_strong_init (σ1c.(fs).(dirents))) as (hP HPpf_eq) "(Hpc&Hp)".
      iMod (Count_Heap.gen_heap_strong_init (λ s, (σ1c.(fs).(dirlocks)) !! s))
        as (hL HLpf_eq) "(Hlc&Hl)".
      iMod (ghost_var_alloc (A := discreteC (gset string))
                            (dom (gset string) σ1c.(fs).(dirents))) as (hGD) "(HgdA&Hgd)".
      replace 0%Z with (O :Z) by auto.
      iPoseProof (Count_Ghost.read_split (A := discreteC (gset string)) hGD
                    with "Hgd") as "(Hgd&Hgdr)".
      iMod (ghost_var_alloc (A := discreteC sliceLockC)
                            (σ1c.(maillocks))) as (hGL) "(HglA&Hgl)".
      set (hFG := (FsG _ _ Σ hL hD hP hIs hFDs _ hGD)).
      set (hGl := (GlobalG _ _ _ _ hGL)).
      set (hG := (GooseG _ _ Σ _ hM hFG hGl _)).
      iPoseProof (eRO.init_exec_inner σ1a σ1c Hinit hG _) as "H".
      iExists hG. iModIntro. iIntros "(Hsource1&Hsource2&Hthread)".
      iFrame.
      iMod ("H" with "[-Hgd]") as "Hinner".
      { iFrame.
        edestruct (eRO.init_wf) as (?&?&->); eauto. iFrame.
        iSplitL "Hd".
        * iPoseProof (@gen_heap_init_to_bigOp _ _ _ _ _ hD with "[Hd]") as "?".
          { by rewrite Hdpf_eq. }
            by rewrite big_opM_fmap.
        * iPoseProof (@Count_Heap.gen_heap_init_to_bigOp _ _ _ _ hL _ _ (σ1c.(fs).(dirlocks))
                        with "[Hl]") as "Hl".
          { intros s x. eapply eRO.init_wf; eauto. }
          { by rewrite HLpf_eq. }
          edestruct (eRO.init_wf) as (->&_&_); eauto.
          iApply big_sepM_dom. iApply (big_sepM_mono with "Hl").
          intros ? (?&[]); eauto.
      }
      iFrame. iModIntro.
      iSplitL "Hgd".
      - iExists _. iFrame.
      - edestruct (eRO.init_wf) as (?&?); eauto.
    Qed.

  Lemma goose_interp_split_read_dir `{gooseG Σ} σ2c:
    (goose_interp σ2c -∗
      goose_interp σ2c ∗ rootdir ↦{-1} dom (gset string) σ2c.(fs).(dirents)
      ∗ ⌜ dom (gset string) σ2c.(fs).(dirents) = dom (gset string) σ2c.(fs).(dirlocks) ⌝)%I.
  Proof.
    clear.
    iIntros "(?&(?&?&?&?&?&Hroot&%)&?)".
    iDestruct "Hroot" as (n) "Hmapsto".
    iFrame. iFrame "%".
    rewrite Count_Ghost.read_split.
    iDestruct "Hmapsto" as "(?&?)". iFrame.
    iExists (S n). eauto.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    rewrite /exec_inv_preserve_crash_type.
    iIntros (??) "Hinv".
    iPoseProof (eRO.exec_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod ("Hinv_post") as "Hinv_post".
    iModIntro. iIntros (? n σ) "((?&Hmach)&Hthread)".
    iMod (gen_typed_heap_strong_init ∅) as (hM' Hmpf_eq') "(Hmc&Hm)".
    iMod (gen_heap_strong_init (∅: gmap File (Inode * OpenMode)))
      as (hFds' Hfds'_eq') "(Hfdsc&Hfd)".
    iMod (Count_Heap.gen_heap_strong_init
            (λ s, ((λ _ : LockStatus * (), (Unlocked, ())) <$> σ.(fs).(dirlocks)) !! s))
      as (hDlocks' Hdlocks'_eq') "(Hdlocksc&Hlocks)".
    iMod (ghost_var_alloc (A := discreteC sliceLockC)
                             None) as (hGl_name) "(HglA&Hgl)".
    set (hGl := GlobalG _ _ _ _ hGl_name).
    iPoseProof (goose_interp_split_read_dir with "Hmach") as "(Hmach&Hroot&Hdom_eq)".
    iMod ("Hinv_post" with "[Hm Hgl Hlocks Hroot Hdom_eq]") as "Hinv'".
    { iFrame. iExists _. iFrame.
       iPoseProof (@Count_Heap.gen_heap_init_to_bigOp _ _ _ _ _ _ _ _
                     with "[Hlocks]") as "Hl"; swap 1 2.
       { rewrite Hdlocks'_eq'. eauto. }
       { intros s x. rewrite lookup_fmap. by intros (?&?&->)%fmap_Some_1. }
       iDestruct "Hdom_eq" as %->.
       iApply big_sepM_dom. rewrite big_sepM_fmap. eauto.
    }
    iModIntro.
    iIntros (σ' Hcrash).
    iExists ((GooseG _ _ _ (@go_invG _ _ _ Hex) hM'
                     (eRO.eRD.crash_fsG (@go_fs_inG _ _ _ _) hDlocks' hFds') hGl _)).
    destruct Hcrash as ([]&(?&?)&Hput&Hrest).
    (* TODO: need a better tactic for inverting the crash *)
    inversion Hput. subst. inv_step.
    inversion Hrest; subst.
    simpl.
    repeat inv_step.
    inversion H.
    deex. inv_step.
    inv_step. inversion H.
    deex. inv_step.
    unfold RecordSet.set in *. simpl.
    inversion H. subst. simpl in *.
    repeat deex. inv_step. subst.
    iDestruct "Hmach" as "(?&(?&?&?&?&?&?)&?)".
    simpl.
    unfold RecordSet.set in *. simpl.
    iFrame.
    simpl.
    iFrame.
    rewrite dom_fmap_L.
    auto.
    iFrame. eauto.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    rewrite /crash_inv_preserve_crash_type.
    iIntros (???) "Hinv".
    iPoseProof (eRO.crash_inv_preserve_crash with "Hinv") as "Hinv_post".
    iMod ("Hinv_post") as "Hinv_post".
    iModIntro. iIntros (? n σ) "((?&Hmach)&Hthread)".
    iMod (gen_typed_heap_strong_init ∅) as (hM' Hmpf_eq') "(Hmc&Hm)".
    iMod (gen_heap_strong_init (∅: gmap File (Inode * OpenMode)))
      as (hFds' Hfds'_eq') "(Hfdsc&Hfd)".
    iMod (Count_Heap.gen_heap_strong_init
            (λ s, ((λ _ : LockStatus * (), (Unlocked, ())) <$> σ.(fs).(dirlocks)) !! s))
      as (hDlocks' Hdlocks'_eq') "(Hdlocksc&Hlocks)".
    iMod (ghost_var_alloc (A := discreteC sliceLockC)
                             None) as (hGl_name) "(HglA&Hgl)".
    set (hGl := GlobalG _ _ _ _ hGl_name).
    iPoseProof (goose_interp_split_read_dir with "Hmach") as "(Hmach&Hroot&Hdom_eq)".
    iMod ("Hinv_post" with "[Hm Hgl Hlocks Hroot Hdom_eq]") as "Hinv'".
    { iFrame. iExists _. iFrame.
       iPoseProof (@Count_Heap.gen_heap_init_to_bigOp _ _ _ _ _ _ _ _
                     with "[Hlocks]") as "Hl"; swap 1 2.
       { rewrite Hdlocks'_eq'. eauto. }
       { intros s x. rewrite lookup_fmap. by intros (?&?&->)%fmap_Some_1. }
       iDestruct "Hdom_eq" as %->.
       iApply big_sepM_dom. rewrite big_sepM_fmap. eauto.
    }
    iModIntro.
    iIntros (σ' Hcrash).
    iExists ((GooseG _ _ _ (@go_invG _ _ _ Hex) hM'
                     (eRO.eRD.crash_fsG (@go_fs_inG _ _ _ _) hDlocks' hFds') hGl _)).
    destruct Hcrash as ([]&(?&?)&Hput&Hrest).
    (* TODO: need a better tactic for inverting the crash *)
    inversion Hput. subst. inv_step.
    inversion Hrest; subst.
    simpl.
    repeat inv_step.
    inversion H.
    deex. inv_step.
    inv_step. inversion H.
    deex. inv_step.
    unfold RecordSet.set in *. simpl.
    inversion H. subst. simpl in *.
    repeat deex. inv_step. subst.
    iDestruct "Hmach" as "(?&(?&?&?&?&?&?)&?)".
    simpl.
    unfold RecordSet.set in *. simpl.
    iFrame.
    simpl.
    iFrame.
    rewrite dom_fmap_L.
    auto.
    iFrame. eauto.
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
    iIntros (? σ2c σ2c' Hfinish ??) "((?&Hmach)&?)".
    inversion Hfinish. subst.
    iMod (gen_typed_heap_strong_init ∅) as (hM' Hmpf_eq') "(Hmc&Hm)".
    iMod (gen_heap_strong_init (∅: gmap File (Inode * OpenMode)))
      as (hFds' Hfds'_eq') "(Hfdsc&Hfd)".
    iMod (Count_Heap.gen_heap_strong_init
            (λ s, ((λ _ : LockStatus * (), (Unlocked, ())) <$> σ2c.(fs).(dirlocks)) !! s))
      as (hDlocks' Hdlocks'_eq') "(Hdlocksc&Hlocks)".
    iMod (ghost_var_alloc (A := discreteC sliceLockC)
                          None) as (hGl''_name) "(HglA&Hgl)".
    set (hGl'':= GlobalG _ _ _ _ hGl''_name).
    iModIntro.
    iExists ((GooseG _ _ _ (@go_invG _ _ _ Hex) hM'
                     (eRO.eRD.crash_fsG (@go_fs_inG _ _ _ _) hDlocks' hFds') hGl'' _)).
    iFrame.
    simpl.
    iPoseProof (goose_interp_split_read_dir with "Hmach") as "(Hmach&Hroot&Hdom_eq)".
    iSplitL ("Hmc Hmach Hfdsc Hdlocksc HglA").
    {
      iDestruct "Hmach" as "(?&(?&?&?&?&?&?)&?)".
      repeat deex. inv_step.
      inversion _z. inv_step.
      inversion _z0. inv_step.
      inversion H1.
      inv_step.
      deex.
      inv_step.
      unfold RecordSet.set. simpl.
      iFrame. simpl.
      rewrite dom_fmap_L.
      iFrame.
    }
    iIntros "(Hctx'&Hsrc')". iModIntro. iMod ("Hinv_post" $! _ _ hM' with "[-]").
    iFrame.
    iExists _. iFrame.
    iPoseProof (@Count_Heap.gen_heap_init_to_bigOp _ _ _ _ _ _ _ _
                  with "[Hlocks]") as "Hl"; swap 1 2.
    { rewrite Hdlocks'_eq'. eauto. }
    { intros s ?. rewrite lookup_fmap. by intros (?&?&->)%fmap_Some_1. }
    iDestruct "Hdom_eq" as %->.
    iApply big_sepM_dom. rewrite big_sepM_fmap. eauto.
    eauto.
  Qed.
  End RO.

  Module R := refinement RT RO.


  Export R.

End goose_refinement.
