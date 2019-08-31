(* We specialize some of the idempotence module construction results to the special
   case when compilation is defined as a per-op translation. *)

From Transitions Require Import Relations Rewriting.

Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Layer.
Require Export CSL.WeakestPre CSL.Refinement CSL.Adequacy  CSL.RefinementAdequacy CSL.ThreadReg.
Require CSL.RefinementIdempotenceModule.
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
  Context `{REG: inG Σ (csumR countingR (authR (optionUR (exclR unitO))))}.
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

  Context (E: coPset).
  (* TODO: we should get rid of rec_seq if we're not exploiting vertical comp anymore *)
  Context (recv: proc OpC unit).

  (* TODO: probably should say that this has to be given using Tej's record setter stuff *)
  Context (set_inv_reg: exmachG Σ → invG Σ → tregG Σ → exmachG Σ).
  Context (init_absr: Λa.(OpState) → Λc.(OpState) → Prop).

End refinement_type.

Module refinement_definitions (RT: refinement_type).

  Import RT.
  Existing Instances Hinstance Hinstance_reg.

  Definition set_reg (Hex: exmachG Σ) (tR: tregG Σ) :=
    set_inv_reg Hex _ tR.
  Definition set_inv (Hex: exmachG Σ) (Hinv: invG Σ) :=
    set_inv_reg Hex Hinv _.

  Definition post_crash {Hex: exmachG Σ} (P: ∀ {_: exmachG Σ}, iProp Σ) : iProp Σ :=
    (∀ Hreg' n σ, state_interp (n, σ) ∗ @thread_count_interp _ Hreg' 1
                   ={E}=∗ ∀ σ' (Hcrash: Λc.(crash_step) σ (Val σ' tt)),
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
    ∀ H1 H2 param,
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
      (∀ `(Hex: exmachG Σ) `(Hcfg: cfgG OpT Λa Σ),
          exec_inv Hcfg Hex ={⊤, E}=∗ post_crash (λ H, |==> crash_inner Hcfg H)).

  Definition crash_inv_preserve_crash_type :=
      (∀ `(Hex: exmachG Σ) `(Hcfg: cfgG OpT Λa Σ) param,
          crash_inv Hcfg Hex param ={⊤, E}=∗ post_crash (λ H, |==> crash_inner Hcfg H)).

  Definition state_interp_no_inv_type :=
      (∀ `(Hex: exmachG Σ) Hinv σ,
           state_interp σ -∗ let _ := set_inv Hex Hinv in state_interp σ).

  Definition crash_inner_inv_type :=
      (∀ `(Hex: exmachG Σ) `(Hcfg: cfgG OpT Λa Σ),
          (∃ Hinv, crash_inner Hcfg (set_inv Hex Hinv)) ∗ source_ctx ={⊤}=∗
          ∃ param, crash_inv Hcfg Hex param ∗ crash_starter Hcfg Hex param).

  Definition exec_inner_inv_type :=
      (∀ (Hex: exmachG Σ) `(Hcfg: cfgG OpT Λa Σ),
          (∃ Hinv, exec_inner Hcfg (set_inv Hex Hinv))
          ∗ source_ctx ={⊤}=∗ exec_inv Hcfg Hex).

  Definition exec_inv_preserve_finish_type :=
      (∀ `(Hex: exmachG Σ) `(Hcfg: cfgG OpT Λa Σ),
          AllDone -∗ exec_inv Hcfg Hex ={⊤, E}=∗ ∃ (σ2a σ2a' : Λa.(OpState)), source_state σ2a
          ∗ ⌜Λa.(finish_step) σ2a (Val σ2a' tt)⌝ ∗
          ∀ `{Hcfg': cfgG OpT Λa Σ},
          post_finish (λ H, source_ctx ∗ source_state σ2a' ==∗ |={⊤}=> exec_inner Hcfg' H)).

End refinement_definitions.

Module Type refinement_obligations (RT: refinement_type).

  Import RT.
  Module RD := refinement_definitions RT.
  Import RD.

  Context (einv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _},
              Persistent (exec_inv H1 H2)).
  Context (cinv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _}
            {P: crash_param _ _}, Persistent (crash_inv H1 H2 P)).
  Context (nameIncl: nclose sourceN ⊆ E).
  Context (recsingle: recover = rec_singleton recv).
  Context (exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx).


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
  Context (exec_inner_inv: exec_inner_inv_type).
  Context (crash_inner_inv: crash_inner_inv_type).
  Context (exec_inv_preserve_finish : exec_inv_preserve_finish_type).
End refinement_obligations.


Module refinement (RT: refinement_type) (RO: refinement_obligations RT).
  Import RT RO.
  Existing Instances Hinstance Hinstance_reg einv_persist cinv_persist.

  Import Reg_wp.

  Module RT' <: RefinementIdempotenceModule.refinement_type.
    Definition OpC := OpC.
    Definition Λc := Λc.
    Definition OpT := OpT.
    Definition Λa := Λa.
    Definition impl := LayerImpl_to_LayerImplRel impl.
    Definition exmachG := exmachG.
    Definition Σ := Σ.
    Definition CFG := CFG.
    Definition INV := INV.
    Definition REG := REG.
    Definition Hinstance := Hinstance.
    Definition Hinstance_reg := Hinstance_reg.
    Definition set_inv_reg := set_inv_reg.

    Definition crash_inner := crash_inner.
    Definition exec_inner := exec_inner.
    Definition crash_inv := crash_inv.
    Definition crash_param := crash_param.
    Definition crash_starter := crash_starter.
    Definition exec_inv := exec_inv.
    Definition E := E.
    Definition recv := recv.
    Definition init_absr := init_absr.
  End RT'.

  Module RD := RefinementIdempotenceModule.refinement_definitions RT'.
  Module RO' <: RefinementIdempotenceModule.refinement_obligations RT'.
    Module RD := RD.
    Definition nameIncl := RO.nameIncl.
    Definition einv_persist := RO.einv_persist.
    Definition cinv_persist := RO.cinv_persist.
    Existing Instances einv_persist cinv_persist.
    Definition recsingle := RO.recsingle.
    Definition refinement_op_triples := RO.refinement_op_triples.
    Definition exec_inv_source_ctx := RO.exec_inv_source_ctx.
    Definition set_inv_reg_spec0 := RO.set_inv_reg_spec0.
    Definition set_inv_reg_spec1 := RO.set_inv_reg_spec1.
    Definition set_inv_reg_spec2 := RO.set_inv_reg_spec2.
    Definition set_inv_reg_spec3 := RO.set_inv_reg_spec3.
    Definition register_spec := RO.register_spec.
    Definition recv_triple := RO.recv_triple.
    Definition init_exec_inner := RO.init_exec_inner.
    Definition exec_inv_preserve_crash := RO.exec_inv_preserve_crash.
    Definition crash_inv_preserve_crash := RO.crash_inv_preserve_crash.
    Definition state_interp_no_inv := RO.state_interp_no_inv.
    Definition crash_inner_inv := RO.crash_inner_inv.
    Definition exec_inner_inv := RO.exec_inner_inv.
    Definition exec_inv_preserve_finish := RO.exec_inv_preserve_finish.

    Lemma refinement_base_triples : RD.refinement_base_triples_type.
      intros ???? j K ? p p' (op&Heq1&Heq2). subst. iApply refinement_op_triples.
    Qed.
  End RO'.

  Module R := RefinementIdempotenceModule.refinement RT' RO'.

  Lemma crash_refinement_seq {T} σ1c σ1a (es: proc_seq OpT T) :
    init_absr σ1a σ1c →
    wf_client_seq es →
    ¬ proc_exec_seq Λa es (rec_singleton (Ret ())) (1, σ1a) Err →
    ∀ σ2c res, proc_exec_seq Λc (compile_proc_seq es) (rec_singleton recv) (1, σ1c) (Val σ2c res) →
    ∃ σ2a, proc_exec_seq Λa es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
  Proof.
    intros. eapply R.crash_refinement_seq; eauto.
    clear.
    induction es; econstructor; eauto.
    clear. econstructor. induction p; eauto; try (repeat econstructor; done).
    * eapply cr_bind; eauto.
    * eapply cr_loop; eauto.
    * eapply cr_spawn; eauto.
  Qed.

End refinement.
