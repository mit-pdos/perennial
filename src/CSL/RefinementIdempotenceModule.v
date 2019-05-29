(* TODO: need a better name. This file is supposed to help bridge the gap from
   the generic RefinementAdequacy.v to the layer specific versions *)

From Transitions Require Import Relations Rewriting.

Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Layer.
Require Export CSL.WeakestPre CSL.Refinement CSL.Adequacy CSL.RefinementAdequacy CSL.ThreadReg.
From iris.algebra Require Import auth frac agree gmap list.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
Unset Implicit Arguments.

Import RelationNotations.
From Transitions Require Import Relations.

Module Type refinement_type.
  Context (OpC OpT: Type → Type).
  Context (Λc: Layer OpC) (Λa: Layer OpT).
  Context (impl: LayerImpl OpC OpT).
  Context (Σ: gFunctors).
  Context (exmachG : gFunctors → Type).
  Existing Class exmachG.
  Notation compile_op := (compile_op impl).
  Notation compile_rec := (compile_rec impl).
  Notation compile_seq := (compile_seq impl).
  Notation compile := (compile impl).
  Notation recover := (recover impl).
  Notation compile_proc_seq := (compile_proc_seq impl).
  Context `{CFG: cfgPreG OpT Λa Σ}.
  Context `{INV: Adequacy.invPreG Σ}.
  Context `{REG: inG Σ (csumR countingR (authR (optionUR (exclR unitC))))}.
  Context {Hinstance: ∀ Σ, exmachG Σ → irisG OpC Λc Σ}.
  Context {Hinstance_reg: ∀ Σ, exmachG Σ → tregG Σ}.
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
  (*
  Context (init_prop: forall {_ : @cfgG OpT Λa Σ} {_: exmachG Σ}, iProp Σ).
   *)

  Context (E: coPset).
  Context (nameIncl: nclose sourceN ⊆ E).
  (* TODO: we should get rid of rec_seq if we're not exploiting vertical comp anymore *)
  Context (recv: proc OpC unit).
  Context (recsingle: recover = rec_singleton recv).

  Context (exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx).

  (* TODO: probably should say that this has to be given using Tej's record setter stuff *)
  Context (set_inv_reg: exmachG Σ → invG Σ → tregG Σ → exmachG Σ).
  Context (init_absr: Λa.(OpState) → Λc.(OpState) → Prop).

End refinement_type.

Module refinement_definitions (RT: refinement_type).

  Import RT.
  Existing Instances Hinstance Hinstance_reg einv_persist cinv_persist.

  Definition set_reg (Hex: exmachG Σ) (tR: tregG Σ) :=
    set_inv_reg Hex _ tR.
  Definition set_inv (Hex: exmachG Σ) (Hinv: invG Σ) :=
    set_inv_reg Hex Hinv _.

  Definition post_crash {Hex: exmachG Σ} (P: ∀ {_: exmachG Σ}, iProp Σ) : iProp Σ :=
    (∀ n σ σ' (Hcrash: Λc.(crash_step) σ (Val σ' tt)) Hreg',
        state_interp (n, σ) ∗ @thread_count_interp _ Hreg' 1 ==∗
                     ∃ Hex', let _ := set_reg Hex' Hreg' in
                             state_interp (1, σ') ∗ P)%I.

  Definition post_finish {Hex: exmachG Σ} (P: ∀ {_: exmachG Σ}, iProp Σ) : iProp Σ :=
    (∀ n σ σ' (Hcrash: Λc.(finish_step) σ (Val σ' tt)) Hinv' Hreg',
        state_interp (n, σ) ∗ @thread_count_interp _ Hreg' 1 ==∗
                     ∃ Hex', let _ := set_inv_reg Hex' Hinv' Hreg' in
                             state_interp (1, σ') ∗ P)%I.

  Definition post_recv {Hex: exmachG Σ} (P: ∀ {_: exmachG Σ}, iProp Σ) : iProp Σ :=
    (∀ n σ Hinv' Hreg',
        state_interp (n, σ) ∗ @thread_count_interp _ Hreg' 1 ==∗
                     ∃ Hex', let _ := set_inv_reg Hex' Hinv' Hreg' in
                             state_interp (1, σ) ∗ P)%I.

  Definition recv_triple_type :=
    ∀ {H1 H2} param,
      (@crash_inv H1 H2 param) ∗ Registered ∗ (@crash_starter H1 H2 param) ⊢
              WP recv @ NotStuck; ⊤
                 {{ v, |={⊤,E}=> ∃ σ2a σ2a', source_state σ2a
                       ∗ ⌜Λa.(crash_step) σ2a (Val σ2a' tt)⌝ ∗
                       ∀ `{Hcfg': cfgG OpT Λa Σ},
                         post_recv (λ H, source_ctx ∗ source_state σ2a' ==∗ |={⊤}=> exec_inner Hcfg' H
                                    )}}.

  Definition init_exec_inner_type :=
    ∀ σ1a σ1c, init_absr σ1a σ1c →
      (∀ `{Hinv: invG Σ} Hreg `{Hcfg: cfgG OpT Λa Σ},
          |={⊤}=> ∃ (Hex': exmachG Σ),
         (source_ctx ∗ source_state σ1a ∗ @thread_count_interp _ Hreg 1)
           ={⊤}=∗ let _ := set_inv_reg Hex' Hinv Hreg in
                  exec_inner Hcfg _ ∗ state_interp (1, σ1c))%I.

  Definition exec_inv_preserve_crash_type :=
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          exec_inv Hcfg Hex ={⊤, E}=∗ post_crash (λ H, |==> crash_inner Hcfg H)).

  Definition crash_inv_preserve_crash_type :=
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ} param,
          crash_inv Hcfg Hex param ={⊤, E}=∗ post_crash (λ H, |==> crash_inner Hcfg H)).

  Definition state_interp_no_inv_type :=
      (∀ `{Hex: exmachG Σ} Hinv σ,
           state_interp σ -∗ let _ := set_inv Hex Hinv in state_interp σ).

End refinement_definitions.

Module Type refinement_obligations (RT: refinement_type).

  Import RT.
  Module RD := refinement_definitions RT.
  Import RD.

  Context (set_inv_reg_spec0:
             ∀ Hex, (set_inv_reg Hex (Hinstance Σ Hex).(@iris_invG OpC (State Λc) Σ)
                                                         (Hinstance_reg Σ Hex) = Hex)).
  Context (set_inv_reg_spec1:
             ∀ Hex Hinv Hreg, @iris_invG _ _ _ (Hinstance _ (set_inv_reg Hex Hinv Hreg)) = Hinv).
  Context (set_inv_reg_spec2:
             ∀ Hex Hinv Hreg, Hinstance_reg _ (set_inv_reg Hex Hinv Hreg) = Hreg).
  Context (set_inv_reg_spec3:
             ∀ Hex Hinv Hinv' Hreg Hreg', set_inv_reg (set_inv_reg Hex Hinv' Hreg') Hinv Hreg =
                              (set_inv_reg Hex Hinv Hreg)).

  Context (register_spec: ∀ {H: exmachG Σ}, ∃ (Interp: OpState Λc → iProp Σ),
                (∀ n σ, @state_interp _ _ _ (Hinstance _ H) (n, σ)
                                     -∗ thread_count_interp n ∗ Interp σ) ∧
                ∀ n σ, thread_count_interp n ∗ Interp σ -∗ state_interp (n, σ)).

  Context (refinement_op_triples:
             forall {H1 H2 T1 T2} j K `{LanguageCtx OpT T1 T2 Λa K} (op: OpT T1),
               j ⤇ K (Call op) ∗ Registered ∗ (@exec_inv H1 H2) ⊢
                 WP compile (Call op) {{ v, j ⤇ K (Ret v) ∗ Registered  }}).

  (* State interpretations should not contain invariants *)

  Context (state_interp_no_inv: state_interp_no_inv_type).

  Context (recv_triple: recv_triple_type).
  Context (init_exec_inner: init_exec_inner_type).
  Context (exec_inv_preserve_crash: exec_inv_preserve_crash_type).
  Context (crash_inv_preserve_crash: crash_inv_preserve_crash_type).

  (* TODO: Much of this business is just to capture the fact that exec_inner/crash_inner
     should not really mention invariants, because those old invariants are 'dead' *)
  Context (crash_inner_inv :
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          (∃ Hinv, crash_inner Hcfg (set_inv Hex Hinv)) ∗ source_ctx ={⊤}=∗
          ∃ param, crash_inv Hcfg Hex param ∗ crash_starter Hcfg Hex param)).

  Context (exec_inner_inv :
      (∀ {Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ} Hinv,
          (∃ Hinv, exec_inner Hcfg (set_inv Hex Hinv))
          ∗ source_ctx ={⊤}=∗ exec_inv Hcfg (set_inv_reg Hex Hinv _))).

  Context (exec_inv_preserve_finish:
      (∀ `{Hex: exmachG Σ} `{Hcfg: cfgG OpT Λa Σ},
          AllDone -∗ exec_inv Hcfg Hex ={⊤, E}=∗ ∃ (σ2a σ2a' : Λa.(OpState)), source_state σ2a
          ∗ ⌜Λa.(finish_step) σ2a (Val σ2a' tt)⌝ ∗
          ∀ `{Hcfg': cfgG OpT Λa Σ},
          post_finish (λ H, source_ctx ∗ source_state σ2a' ==∗ |={⊤}=> exec_inner Hcfg' H))).
End refinement_obligations.


Module refinement (RT: refinement_type) (RO: refinement_obligations RT).
  Import RT RO.
  Existing Instances Hinstance Hinstance_reg einv_persist cinv_persist.

  Import Reg_wp.

  Lemma wp_spawn {H: exmachG Σ} {T} s E (e: proc _ T) Φ :
    ▷ Registered
      -∗ ▷ (Registered -∗ WP (let! _ <- e; Unregister)%proc @ s; ⊤ {{ _, True }})
      -∗ ▷ ( Registered -∗ Φ tt)
      -∗ WP Spawn e @ s; E {{ Φ }}.
  Proof.
    intros. edestruct (register_spec) as (?&?&?). eapply wp_spawn; eauto.
  Qed.

  Lemma wp_unregister {H: exmachG Σ} s E :
    {{{ ▷ Registered }}} Unregister @ s; E {{{ RET tt; True }}}.
  Proof.
    intros. edestruct (register_spec) as (?&?&?). eapply wp_unregister; eauto.
  Qed.

  Lemma wp_wait {H: exmachG Σ} s E :
    {{{ ▷ Registered }}} Wait @ s; E {{{ RET tt; AllDone }}}.
  Proof.
    intros. edestruct (register_spec) as (?&?&?). eapply wp_wait; eauto.
  Qed.

  Lemma refinement_triples:
             forall {H1 H2 T1 T2} j K `{LanguageCtx OpT T1 T2 Λa K} (e: proc OpT T1),
               wf_client e →
               j ⤇ K e ∗ Registered ∗ (@exec_inv H1 H2) ⊢
                 WP compile e {{ v, j ⤇ K (Ret v) ∗ Registered }}.
  Proof.
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

  Existing Instances INV CFG REG.

  Transparent WeakestPre.iris_invG.
  Lemma iris_invG_proj T H Hinv:
      @iris_invG _ T _ (IrisG OpC _ Σ Hinv H) = Hinv.
  Proof. auto. Qed.
  Opaque WeakestPre.iris_invG.

  Lemma Hinstance_eta Hex Hinv Hreg:
      (Hinstance Σ (set_inv_reg Hex Hinv Hreg)) =
      IrisG OpC _ Σ Hinv (@state_interp _ _ _ (Hinstance Σ (set_inv_reg Hex Hinv Hreg))).
  Proof.
    specialize (set_inv_reg_spec1 Hex Hinv Hreg).
    destruct Hinstance => //=. rewrite iris_invG_proj => -> //.
  Qed.

  Lemma Hinstance_eta2 Hex Hinv Hreg:
    IrisG OpC _ Σ Hinv (@state_interp _ _ _ (Hinstance Σ (set_inv_reg Hex Hinv Hreg))) =
    Hinstance Σ (set_inv_reg (set_inv_reg Hex Hinv Hreg) Hinv
                             (Hinstance_reg Σ (set_inv_reg Hex Hinv Hreg))).
  Proof.
    by rewrite -Hinstance_eta set_inv_reg_spec2 set_inv_reg_spec3.
  Qed.

  Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq OpT T) :
    init_absr σ1a σ1c →
    wf_client_seq es →
    ¬ proc_exec_seq Λa es (rec_singleton (Ret ())) (1, σ1a) Err →
    ∀ σ2c res, proc_exec_seq Λc (compile_proc_seq es) (rec_singleton recv) (1, σ1c) (Val σ2c res) →
    ∃ σ2a, proc_exec_seq Λa es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
  Proof.
    rewrite /compile_proc_seq. intros Hinit Hwf_seq Hno_err σ2c0 ?.
    unshelve (eapply wp_proc_seq_refinement_adequacy with
                  (Λc := Λc)
                  (φ := fun va vc _ _ => ⌜ va = vc ⌝%I)
                  (E := E); eauto).
    clear Hno_err.
    iAssert (∀ invG H1 ρ,
               |={⊤}=> ∃ Hex Hreg (HEQ:Hreg.(@treg_counter_inG Σ) = REG),
               source_ctx' (ρ, σ1a) -∗ source_state σ1a ={⊤}=∗
               let _ := set_inv_reg Hex invG Hreg in
                 state_interp (1, σ1c) ∗
                   own (treg_name Hreg) (Cinl (Count (-1))) ∗
                   exec_inner H1 (set_inv_reg Hex invG Hreg))%I
      as "Hpre".
    {
      iIntros (???).
      iMod (own_alloc (Cinl (Count 0))) as (tR) "Ht".
      { constructor. }
      set (Hreg' := {| treg_name := tR; treg_counter_inG := _ |}).
      iAssert (own tR (Cinl (Count 1)) ∗ own tR (Cinl (Count (-1))))%I with "[Ht]" as "(Ht&Hreg)".
      { rewrite /Registered -own_op Cinl_op counting_op' //=. }
      iMod (init_exec_inner $! _ Hreg' _) as (Hex') "H"; eauto.
      iModIntro. unshelve (iExists Hex', Hreg', _); first by eauto.
      iIntros "#Hctx Hstate".
      iMod ("H" with "[Hstate Ht]") as "(Hexec&Hstate)".
      { iFrame. iExists _; eauto. }
      by iFrame.
    }

  clear Hinit.
  iInduction es as [|es] "IH" forall (σ1a σ1c) "Hpre"; first by eauto.
  - iSplit; first by (eauto using nameIncl).
    iExists (fun cfgG (s: State Λc) => ∀ (s': State Λc)
                  (Hcrash: Λc.(crash_step) (snd s) (Val (snd s') tt)),
                 |==> ∃ (Hex : exmachG Σ) (HEQ:(@Hinstance_reg _ Hex).(@treg_counter_inG Σ) = REG),
                 state_interp (1, snd s') ∗
                 own (treg_name _) (Cinl (Count (-1)%Z)) ∗ crash_inner cfgG Hex)%I; auto.
  iIntros (invG0 Hcfg0).
  iMod ("Hpre" $! invG0 _ _) as (hEx Hreg HEQ) "H".
  iExists (@state_interp _ _ _ ((Hinstance Σ (set_inv_reg hEx invG0 Hreg)))). iModIntro.
  iIntros "(#Hsrc&Hpt0&Hstate)".
  iMod ("H" with "Hsrc Hstate") as "(Hinterp&Hreg&Hinv)".
  iMod (@exec_inner_inv (set_inv_reg hEx invG0 Hreg) with "[Hinv]") as "#Hinv".
  { iSplitR ""; last by (iExists _; iFrame). iExists _. iFrame. simpl. 
    rewrite /RD.set_inv. rewrite set_inv_reg_spec2. rewrite set_inv_reg_spec3.
    iFrame.
  }
  iFrame.
  iSplitL "Hpt0 Hreg".
  {  iPoseProof (@wp_mono with "[Hpt0 Hreg]") as "H"; swap 1 2.
     {
       iApply @refinement_triples. destruct (Hwf_seq) as (?&?). eauto. iFrame. iFrame "Hinv".
       rewrite ?set_inv_reg_spec2.
       rewrite /Registered. rewrite HEQ. auto.
     }
     { reflexivity. }
     simpl. rewrite /compile_whole.
     iModIntro.
     iApply @wp_bind_proc_subst_weak.
     rewrite Hinstance_eta2.
     iApply (@wp_wand with "H [Hinv]").
     iIntros (v) "(Hpt0&Hreg)". iFrame.
     iApply @wp_bind_proc_subst_weak.
     iApply (@wp_wand with "[Hreg Hpt0] []"); last first.
     { iIntros (?) "H". iApply "H". }
     iApply (@wp_wait with "[$]").
     iIntros "!> Hdone".
     iApply @wp_ret.
     iFrame. iExists _. iFrame. iIntros (σ2c) "Hmach".
     iPoseProof (exec_inv_preserve_finish with "Hdone Hinv") as "Hpose".
     rewrite -Hinstance_eta2.
     iMod "Hpose" as (σ2a σ2a') "(H&Hfina&Hfinish)".
     iDestruct "Hfina" as %Hfina.
     iModIntro. iExists _; iFrame; auto.
     simpl.
     rewrite -/wp_proc_seq_refinement.
     iIntros (σ2c'). iIntros.
     unshelve (iExists σ2a', _); [eauto |]; [].
     iApply "IH".
     { iPureIntro. destruct Hwf_seq. eauto. }
     { iIntros.
       destruct σ2c as (n&σ2c).
       iMod (own_alloc (Cinl (Count 0))) as (tR_fresh') "Ht".
       { constructor. }
       iAssert (own tR_fresh' (Cinl (Count 1))
                    ∗ own tR_fresh' (Cinl (Count (-1))))%I with "[Ht]" as "(Ht&Hreg)".
       { rewrite /Registered -own_op Cinl_op counting_op' //=. }
       set (tR''' := {| treg_name := tR_fresh'; treg_counter_inG := _ |}).
       iSpecialize ("Hfinish" $! _ _ _ with "[] [Hmach Ht]").
       { eauto. }
       { simpl.
         rewrite set_inv_reg_spec2.
         rewrite set_inv_reg_spec3.
         iFrame.
       }
       iMod "Hfinish" as (Hex') "H".
       iModIntro. iExists _. iExists tR'''. unshelve (iExists _); first by eauto.
       iIntros "#Hctx' Hsrc'".
       iMod (fupd_mask_mono with "H") as "(H&Hfinish)"; first by set_solver.
       iFrame. iMod ("Hfinish" with "[Hsrc']") as "Hfinish".
       {
         iFrame "Hsrc'". iExists _. rewrite set_inv_reg_spec1. iFrame "Hctx'".
       }
       rewrite set_inv_reg_spec1.
       iFrame.
     }
  }
  iModIntro.
  iSplit.
  { iIntros (σ2c) "Hmach".
    iPoseProof (exec_inv_preserve_crash with "Hinv") as "Hinv_post".
    rewrite -Hinstance_eta2.
    iMod "Hinv_post" as "Hinv_post".
    iMod (own_alloc (Cinl (Count 0))) as (tR_fresh') "Ht".
    { constructor. }
    iAssert (own tR_fresh' (Cinl (Count 1))
                 ∗ own tR_fresh' (Cinl (Count (-1))))%I with "[Ht]" as "(Ht&Hreg)".
    { rewrite /Registered -own_op Cinl_op counting_op' //=. }
    set (tR''' := {| treg_name := tR_fresh'; treg_counter_inG := _ |}).
    iModIntro. iIntros.
    destruct σ2c as (?&σ2c).
    iSpecialize ("Hinv_post" $! _ _ _ Hcrash with "[Ht Hmach]").
    { rewrite set_inv_reg_spec2 set_inv_reg_spec3. iFrame. }
    iMod ("Hinv_post") as (?) "H".
     unshelve (iExists (RD.set_reg H tR'''), _).
    { rewrite set_inv_reg_spec2. eauto. }
    rewrite ?set_inv_reg_spec2 ?set_inv_reg_spec1 ?set_inv_reg_spec3.
    iDestruct ("H") as "(H&H')".
    iMod "H'". iFrame. iModIntro.
    eauto.
  }
  iClear "Hsrc".
  iModIntro. iIntros (invG Hcfg' (?&s) (n'&s') Hcrash) "(Hinv0&#Hsrc)".
  destruct Hcrash as ([]&(?&?)&Hputs&Hcrash).
  inversion Hputs.
  subst.
  inversion Hcrash. subst.
  inversion H. subst.
  unshelve (iMod ("Hinv0" $! (1, s') _) as "Hinv0"); [ eauto | ].
  eauto.
  clear HEQ.
  iDestruct "Hinv0" as (HexmachG' HEQ) "H".
  iMod (fupd_mask_mono with "H") as "(H&Hfinish)"; first by set_solver.
  iExists (@state_interp _ _ _ (@Hinstance Σ (set_inv_reg HexmachG' invG (Hinstance_reg Σ HexmachG')))).
  iDestruct "Hfinish" as "(Hreg&Hcrash_inner)".
  iPoseProof (@crash_inner_inv (RD.set_inv HexmachG' invG) _ with "[Hcrash_inner]") as "Hcrash".
  { simpl. iFrame. iSplitL "Hcrash_inner".
    rewrite /RD.set_inv.
    * iExists (@iris_invG _ _ _ (Hinstance Σ HexmachG')).
      rewrite /RD.set_inv. rewrite ?set_inv_reg_spec3 ?set_inv_reg_spec2.
      rewrite set_inv_reg_spec0. eauto.
    * iExists _.  rewrite set_inv_reg_spec1. eauto.
  }
  rewrite set_inv_reg_spec1.
  iClear "Hinv".
  iMod "Hcrash" as (param) "(#Hinv&Hstarter)".
  iModIntro.
  iFrame.
  (*
  iAssert (own ((Hinstance_reg Σ HexmachG').(treg_name)) (Cinl (Count 1)) ∗
           own ((Hinstance_reg Σ HexmachG').(treg_name)) (Cinl (Count (-1))))%I
    with "[Hreg]" as "(Ht&Hreg)".
  { rewrite set_inv_reg_spec2. rewrite /Registered -own_op Cinl_op counting_op' //=. }
   *)
  iSplitL "H".
  {
    iPoseProof (state_interp_no_inv with "H") as "H".
    rewrite /RD.set_inv/RD.set_reg. eauto.
  }
  iSplitL "Hstarter Hinv Hreg".
  {
    iPoseProof (@wp_mono with "[Hinv Hreg Hstarter IH]") as "H"; swap 1 2.
    { iApply recv_triple. iFrame "Hstarter". iFrame. iFrame "Hinv".
      rewrite/ Registered. rewrite set_inv_reg_spec2 HEQ.
      eauto.
    }
    { reflexivity. }
    iApply (@wp_wand with "[H] [IH]").
    { rewrite Hinstance_eta. iApply "H". }
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
       destruct σ2c.
       iMod ("Hfinish" $! H2 _ with "[$]") as (Hex') "(Hinterp&Hfinish)".
       unshelve (iExists _, _, _); first by auto.
       iFrame.
       iModIntro. simpl.
       iClear "Hsrc".
       iIntros "#Hsrc Hstate".
       iMod ("Hfinish" with "[Hstate]") as "Hfinish".
       { iFrame. iExists _. rewrite set_inv_reg_spec1. eauto. }
       rewrite set_inv_reg_spec1.
       iApply "Hfinish".
     }
  }
  {
    iIntros (σ2c) "Hmach".
    iPoseProof (@crash_inv_preserve_crash with "Hinv") as "Hinv_post".
    rewrite set_inv_reg_spec1.
    iMod ("Hinv_post") as "Hinv_post".
    iMod (own_alloc (Cinl (Count 0))) as (tR_fresh'') "Ht'".
    { constructor. }
    iAssert (own tR_fresh'' (Cinl (Count 1))
                 ∗ own tR_fresh'' (Cinl (Count (-1))))%I with "[Ht']" as "(Ht&Hreg)".
    { rewrite /Registered -own_op Cinl_op counting_op' //=. }
    set (tR'''' := {| treg_name := tR_fresh''; treg_counter_inG := _ |}).
    iModIntro. iIntros.
    destruct σ2c as (?&σ2c).
    iSpecialize ("Hinv_post" with "[] [Hmach Ht]").
    { iPureIntro. eauto. }
    { iFrame. }
    iMod ("Hinv_post") as (?) "H".
    unshelve (iExists (RD.set_reg _ tR''''), _).
    { rewrite set_inv_reg_spec2. eauto. }
    rewrite ?set_inv_reg_spec2 ?set_inv_reg_spec1 ?set_inv_reg_spec3.
    iDestruct ("H") as "(H&>H')".
    iFrame.
    eauto.
  }
  Qed.

End refinement.
