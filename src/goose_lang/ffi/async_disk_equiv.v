From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang.ffi Require async_disk.
From Perennial.goose_lang.ffi Require async_disk_proph.
From Perennial.program_logic Require recovery_adequacy.


Module ADP := async_disk_proph.
Module AD := async_disk.

Section translate.
  Notation pstate := (@state async_disk_syntax.disk_op ADP.disk_model).
  Notation pglobal := (@global_state ADP.disk_model).
  Notation dstate := (@state async_disk_syntax.disk_op AD.disk_model).
  Notation dglobal := (@global_state AD.disk_model).

  Definition stable_disk (dd : @ffi_state AD.disk_model) :=
    (∀ addr ab, dd !! addr = Some ab → log_heap.pending ab = []).

  Definition disk_compat (dd : @ffi_state AD.disk_model) (ad: @ffi_state ADP.disk_model) :=
    dom dd = dom ad ∧
    (∀ addr ab, dd !! addr = Some ab →
     ∃ bd, bd ∈ log_heap.possible ab ∧
           ad !! addr = Some ({| ADP.curr_val := log_heap.latest ab;
                                 ADP.crash_val := bd |})).

  Definition state_compat (dσ : dstate) (pσ : pstate) :=
    heap dσ = heap pσ ∧
    disk_compat (world dσ) (world pσ) ∧
    trace dσ = trace pσ ∧
    oracle dσ = oracle pσ ∧
    globals dσ = globals pσ
  .

  Definition global_compat (dg : dglobal) (pg : pglobal) :=
    used_proph_id dg = used_proph_id pg ∧
    global_world dg = global_world pg.

  Ltac inv_base_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : base_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        | H: relation.denote (unwrap None) _ _ _ |- _ => inversion H; intuition eauto
        end.

  Ltac inv_monad_false :=
    match goal with
    | H: relation.denote (unwrap None) _ _ _ |- _ => inversion H; intuition eauto
    | H: relation.suchThat (λ _ _, False) _ _ _ |- _ => inversion H; intuition eauto
    end.

  Existing Instances AD.disk_semantics ADP.disk_semantics.

  Ltac destruct_head :=
    repeat match goal with
           | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] => destruct e; monad_inv; []
           end.

  Lemma state_compat_write_inv (σ : dstate) (pσ : pstate) bnew ab (n : u64) :
    world σ !! uint.Z n = Some ab →
    state_compat (RecordSet.set world <[uint.Z n:=log_heap.async_put bnew ab]> σ) pσ →
    ∃ cb, world pσ !! uint.Z n = Some cb ∧
          ((cb = {| ADP.curr_val := bnew; ADP.crash_val := bnew |} ∧
            state_compat σ (RecordSet.set world <[uint.Z n:= {| ADP.curr_val := log_heap.latest ab;
                                                               ADP.crash_val := log_heap.latest ab|}]>
                            pσ)) ∨
           (ADP.crash_val cb ≠ bnew ∧
            state_compat σ (RecordSet.set world <[uint.Z n:= {| ADP.curr_val := log_heap.latest ab;
                                                               ADP.crash_val := ADP.crash_val cb |}]>
                            pσ))).
  Proof.
    intros Hlookup Hcompat.
    destruct Hcompat as (Hheap&Hdisk&?&?&?).
    destruct Hdisk as (Hdom&Hvals).
    destruct (world pσ !! uint.Z n) as [cb|] eqn:Heqp; last first.
    { exfalso. revert Heqp. rewrite -not_elem_of_dom.
      move: Hdom. rewrite /RecordSet.set//=. rewrite dom_insert_L. set_solver. }
    exists cb. split; first done.
    assert (ADP.curr_val cb = bnew).
    { edestruct Hvals as (b'&Hposs&Hlookup2); eauto.
      { rewrite /RecordSet.set//=. apply: lookup_insert_eq. }
      rewrite Heqp in Hlookup2. inversion Hlookup2 => //=.
    }
    destruct (decide (ADP.crash_val cb = bnew)) as [Heq|Hneq].
    { left. split.
      { destruct cb => //=; f_equal; rewrite //=. }
      rewrite /RecordSet.set//=. split_and!; eauto.
      rewrite //=. split.
      * move:Hdom.
        rewrite ?dom_insert_L.
        apply (elem_of_dom_2 (D := gset Z) (world pσ)) in Heqp.
        apply (elem_of_dom_2 (D := gset Z) (world σ)) in Hlookup.
        set_solver.
      * intros addr ab' Hlookup'.
        destruct (decide (addr = uint.Z n)).
        { subst. assert (ab' = ab) by congruence; subst.
          exists (log_heap.latest ab); split.
          * rewrite /log_heap.possible. apply elem_of_app; right. econstructor.
          * rewrite lookup_insert_eq //=.
        }
        rewrite lookup_insert_ne //. eapply Hvals. rewrite lookup_insert_ne; eauto.
    }
    {
      right. split; first done.
      rewrite /RecordSet.set//=. split_and!; eauto.
      rewrite //=. split.
      * move:Hdom.
        rewrite ?dom_insert_L.
        apply (elem_of_dom_2 (D := gset Z) (world pσ)) in Heqp.
        apply (elem_of_dom_2 (D := gset Z) (world σ)) in Hlookup.
        set_solver.
      * intros addr ab' Hlookup'.
        destruct (decide (addr = uint.Z n)).
        { subst. assert (ab' = ab) by congruence; subst.
          exists (ADP.crash_val cb); split.
          * edestruct (Hvals) as (b'&Hin&Hlook'); eauto.
            { rewrite /RecordSet.set//=. apply lookup_insert_eq. }
            rewrite Heqp in Hlook'. inversion Hlook' as [Heq'].
            rewrite //=. move:Hin. rewrite /log_heap.possible //= ?elem_of_app.
            intros [Hin1|Hin2]; eauto.
            apply list_elem_of_singleton in Hin2. exfalso. subst.
            clear -Heq' Hneq. destruct cb. simpl in *; congruence.
          * rewrite lookup_insert_eq //=.
        }
        rewrite lookup_insert_ne //. eapply Hvals. rewrite lookup_insert_ne; eauto.
    }
  Qed.

  Lemma state_compat_disk_size σ pσ :
    state_compat σ pσ →
    AD.disk_size (world σ) = ADP.disk_size (world pσ).
  Proof.
    intros (?&(Hdom&Hdisk)&_). rewrite /AD.disk_size/ADP.disk_size Hdom //.
  Qed.

  Lemma state_compat_all_synced_post_flush σ1 (pσ1 : pstate) :
    ADP.all_synced (world pσ1) →
    state_compat σ1 pσ1 →
    state_compat (RecordSet.set world AD.flush_disk σ1) pσ1.
  Proof.
    rewrite /RecordSet.set //=.
    intros Hsynced (Hheap&Hdisk&Htrace&Horacle&Hglobals).
    split_and! => //=.
    destruct Hdisk as (Hdom&Hlook). split.
    { rewrite /AD.flush_disk dom_fmap_L //. }
    intros addr ab Hlookab.
    rewrite lookup_fmap in Hlookab.
    eapply fmap_Some_1 in Hlookab as (ab'&Hlook'&Hflush).
    edestruct Hlook as (bd&Hin&Hlookbd); eauto.
    subst.
    eexists. split; last first => //=.
    eapply Hsynced in Hlookbd. rewrite //= in Hlookbd.
    rewrite /log_heap.flush//= Hlookbd //=.
    rewrite /log_heap.possible//=.
    econstructor.
  Qed.

  Lemma state_compat_post_flush_inv σ1 pσ2 :
    state_compat (RecordSet.set world AD.flush_disk σ1) pσ2 →
    state_compat σ1 pσ2 ∧ ADP.all_synced (world pσ2).
  Proof.
    rewrite /RecordSet.set //=.
    intros (Hheap&Hdisk&Htrace&Horacle&Hglobals).
    split.
    { split_and!; eauto.
      clear -Hdisk. rewrite //= in Hdisk.
      destruct Hdisk as (Hdom&Hvals).
      split.
      { rewrite -Hdom dom_fmap_L //. }
      intros addr ab Hlook.
      edestruct (Hvals addr (log_heap.flush ab)) as (bd'&Hpossible&?).
      { rewrite lookup_fmap Hlook //. }
      eexists; split; eauto. rewrite /log_heap.possible//= in Hpossible *.
      apply elem_of_app; eauto.
    }
    clear -Hdisk. rewrite //= in Hdisk.
    rewrite /ADP.all_synced//=.
    destruct Hdisk as (Hdom&Hvals).
    intros addr blk Hlook.
    destruct (world σ1 !! addr) as [ab|] eqn:Heqab; last first.
    { apply (not_elem_of_dom (D := gset Z) (world σ1)) in Heqab.
      rewrite dom_fmap_L in Hdom. rewrite Hdom in Heqab.
      apply elem_of_dom_2 in Hlook. set_solver. }
    edestruct (Hvals addr (log_heap.flush ab)) as (bd'&Hpossible&Hlook').
    { rewrite lookup_fmap Heqab //. }
    rewrite Hlook in Hlook'. inversion Hlook' => //=.
    rewrite /log_heap.possible//= in Hpossible *.
    set_solver.
  Qed.

   Ltac inv_pure_base_step :=
     match goal with
     | [ H: relation.denote _ _ _ _ |- _ ] =>
         rewrite //= in H;
         destruct_head; inversion H; subst;
         monad_inv
     end.

  Ltac inv_unwrap_case :=
    repeat match goal with
    | H : ?e = ?y |- context[relation.denote (unwrap ?e) _ _ _] => rewrite ?H
    | H: relation.denote (unwrap (Some _)) _ _ _ |- _ => inv_pure_base_step
    | H: relation.denote (unwrap ?e) _ _ _ |- _ =>
        destruct e eqn:?; last by (inv_monad_false); eauto; subst
    end.

  Ltac solve_step :=
      do 2 eexists; split_and!; eauto;
      econstructor; inv_unwrap_case; eauto; econstructor; eauto.

  Theorem base_step_simulation e1 σ1 g1 κ e2 σ2 g2 efs :
    base_step e1 σ1 g1 κ e2 σ2 g2 efs →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        base_step e1 pσ1 pg1 κ e2 pσ2 pg2 efs.
  Proof.
    rewrite /base_step.
    revert σ1 g1 κ e2 σ2 g2 efs.
    destruct e1; intros σ1 g1 κ e2 σ2 g2 efs Hstep; subst; try inversion Hstep; intuition eauto; subst;
      try (inv_pure_base_step; inversion Hstep; subst; monad_inv; solve_step; done).
    - inv_pure_base_step; inv_unwrap_case; solve_step.
    - inv_pure_base_step; inv_unwrap_case; solve_step.
    - rewrite /base_step//= in Hstep.
      destruct_head. destruct v; monad_inv; inv_pure_base_step; inv_unwrap_case; solve_step.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv. solve_step.
    - rewrite /base_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      inversion Hstep; monad_inv. inv_pure_base_step.
      solve_step; repeat econstructor.
    - rewrite /base_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      * inversion Hstep; monad_inv.
        simpl in H1.
        inv H1. inv H2. monad_inv.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        select (relation.denote (r_mbind  _ _) _ _ _) (fun H => inv H).
        destruct (heap σ1 !! l) eqn:Heq; subst.
        ** select (relation.denote (unwrap _) _ _ _) (fun H => inv H); monad_inv.
           inversion H.
           intuition.
           eexists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                      world := world pσ2 ; globals := globals pσ2 |}).
           eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite Heq. econstructor; eauto. }
               rewrite //=. repeat econstructor; eauto. f_equal.
               f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               congruence.
        ** inv H4; intuition.
      * inversion Hstep; monad_inv.
        simpl in H1.
        inv H1. inv H2. monad_inv.
        destruct x0. destruct n; monad_inv.
        inv H3.
        destruct (heap σ1 !! l) eqn:Heq; subst.
        ** select (relation.denote (unwrap _) _ _ _) (fun H => inv H); monad_inv.
           inversion H.
           intuition.
           exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                      world := world pσ2 ; globals := globals pσ2 |}).
           eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite Heq. econstructor; eauto. }
               rewrite //=. repeat econstructor; eauto. f_equal.
               f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               congruence.
        ** inversion H4; intuition.
      * inversion Hstep; monad_inv.
        simpl in H1.
        inv H1. inv H2. monad_inv.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        inv H3; monad_inv.
        destruct (heap σ1 !! l) eqn:Heq; subst.
        ** select (relation.denote (unwrap _) _ _ _) (fun H => inv H); monad_inv.
           inversion H.
           intuition.
           exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                      world := world pσ2; globals := globals pσ2 |}).
           eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite Heq. econstructor; eauto. }
               rewrite //=. repeat econstructor; eauto. f_equal.
               f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               congruence.
        ** inversion H4; intuition.
      * inversion Hstep; monad_inv.
        simpl in H1.
        inv H1. inv H2. monad_inv.
        destruct x0. destruct n; monad_inv.
        destruct (heap σ1 !! l) eqn:Heq; subst.
        ** select (relation.denote (unwrap _) _ _ _) (fun H => inv H); monad_inv.
           inversion H.
           intuition.
           do 2 eexists. split_and!; eauto.
           repeat econstructor; rewrite -?H1 ?Heq; eauto; repeat econstructor.
        ** inversion H4; intuition.
      * inversion Hstep; monad_inv.
        simpl in H1.
        inv H1. inv H3. monad_inv.
        inversion H; intuition.
           exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                      world := world pσ2; globals := globals pσ2 |}).
           eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto => //=.
               f_equal. f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               congruence.
      * inversion Hstep; monad_inv.
        simpl in H1.
        inv H1. monad_inv.
        inversion H; intuition.
           exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                      world := world pσ2; globals := globals pσ2 |}).
           eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto => //=.
               f_equal. f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               congruence.
      * inversion Hstep; monad_inv.
        simpl in H1.
        inv H1. inv H2. monad_inv.
        ** inversion H.
           intuition.
           do 2 eexists. split_and!; eauto.
           repeat econstructor; rewrite -?H6 ?Heq; eauto; repeat econstructor.
    - (* Primitive2 *)
      rewrite /base_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      * (* AllocN *)
        inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1. subst.
        inversion H3; monad_inv; subst; clear H3.
        inversion H4; monad_inv; subst; clear H4.
        destruct s0 as (?&[]).
        destruct (decide (0 < uint.Z n)); monad_inv.
        monad_inv. inversion H1.
        exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                   world := world pσ2; globals := globals pσ2 |}).
        eexists. subst. inversion H. intuition.
        ** simpl in *. split_and!; eauto.
        ** eauto.
        ** econstructor.
           *** inversion H6; econstructor; eauto; repeat (econstructor; eauto).
               { unfold check. rewrite ifThenElse_if; eauto. rewrite /=. econstructor. rewrite //=. }
               { eapply H7. }
               { rewrite //=. eapply H6. }
           *** repeat econstructor => //=.
               f_equal. f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
               f_equal; eauto.
      * (* FinishStore *)
        inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1. subst.
        inversion H3; monad_inv; subst; clear H3.
        destruct (decide (is_Writing (heap σ1 !! l))); monad_inv.
        inversion H2; monad_inv; subst; clear H2.
        exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                   world := world pσ2; globals := globals pσ2 |}).
        subst. eexists. inversion H. intuition.
        ** simpl in *. split_and!; eauto.
        ** eauto.
        ** econstructor.
           *** econstructor; eauto; repeat (econstructor; eauto).
               { unfold check. rewrite ifThenElse_if; eauto. rewrite /=. econstructor. rewrite //=. }
           *** repeat econstructor => //=.
               f_equal. f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
               f_equal; eauto.
      * (* AtomicStore *)
        inversion Hstep; monad_inv.
        inv H1. inv H2. monad_inv.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        inv H3; monad_inv.
        destruct s2 as [σ' g']. inv H1.
        destruct (heap σ1 !! l) eqn:Heq; subst.
        ** select (relation.denote (unwrap _) _ _ _) (fun H => inv H); monad_inv.
           inversion H.
           intuition.
           eexists ({| heap := _; oracle := _; trace := _;
                      world := world pσ2 |}).
           eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite Heq. econstructor; eauto. }
               rewrite //=. repeat econstructor; eauto. f_equal.
               f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               f_equal; eauto.
        ** match goal with
           | H: relation.denote (unwrap _) _ _ _ |- _ => inv H; intuition
           end.
      * (* AtomicOp *)
        rewrite /atomically /= in Hstep.
        monad_inv. simpl in Hstep.
        unfold unwrap in Hstep.
        destruct (heap σ1 !! l) as [[[|[|]]]|] eqn:Hlookup;
          repeat ((by exfalso) || simpl in * || monad_inv).
        destruct bin_op_eval eqn:Hop; repeat ((by exfalso) || simpl in * || monad_inv).
        inversion H. intuition.
        eexists ({| heap := heap _; oracle := _; trace := _;
                                                 world := world pσ2 |}).
        eexists. split_and!.
        *** simpl in *. split_and!; eauto.
        *** eauto.
        *** econstructor; eauto; repeat econstructor; eauto.
            { rewrite //=. rewrite Hlookup. econstructor; eauto. }
            rewrite //=. rewrite Hop. repeat econstructor; eauto. f_equal.
            f_equal. destruct pσ2; subst.
            simpl in * => //=. rewrite /RecordSet.set //=.
            f_equal; eauto.
      * (* GlobalPut *)
        inversion Hstep; monad_inv.
        inv H1. monad_inv.
        inv H. destruct H2 as (?&?&?&?).
        eexists ({| heap := _; oracle := _; trace := trace σ1;
                          world := world pσ2; globals := _ |}).
        eexists.
        split_and!.
        *** simpl in *. split_and!; eauto.
        *** eauto.
        *** econstructor; eauto; repeat econstructor; eauto.
            rewrite /RecordSet.set /=. repeat f_equal.
            destruct pσ2. destruct σ1.
            simpl in *. f_equal; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; monad_inv.
      simpl in H1.
      inv H1. inv H2. monad_inv.
      destruct_head.
      rewrite //= in H3.
      destruct (heap σ1 !! l) eqn:Heq; monad_inv; try inv_monad_false.
      destruct (decide (vals_compare_safe v1 v)); monad_inv; try inv_monad_false; last first.
      { intuition eauto. }
      inversion H3; monad_inv; subst; clear H3.
      destruct (decide (v1 = v)).
      * subst. rewrite ifThenElse_if in H1; eauto.
        destruct (decide (n = O)); monad_inv; last first.
        { rewrite ifThenElse_else in H1; eauto. simpl in H1. inversion H1; monad_inv. }
        rewrite ifThenElse_if in H1; eauto.
        simpl in H1. monad_inv. destruct s2; monad_inv.
        simpl in H4. monad_inv.
      exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                 world := world pσ2; globals := globals pσ2 |}).
      subst. eexists. inversion H. intuition.
      ** simpl in *. split_and!; eauto.
      ** eauto.
      ** econstructor.
         *** econstructor; eauto; repeat (econstructor; eauto).
             { rewrite Heq //=. }
             rewrite //=.
             unfold check. rewrite ifThenElse_if; eauto. rewrite /=. repeat econstructor; eauto.
             rewrite /when. rewrite ifThenElse_if; eauto. repeat econstructor.
         *** repeat econstructor => //=.
               f_equal. f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
               f_equal; eauto.
      * rewrite ifThenElse_else in H1; auto. simpl in H1. monad_inv.
        inversion H4. subst. monad_inv.
      subst. do 2 eexists. inversion H. intuition.
      ** simpl in *. split_and!; eauto.
      ** eauto.
      ** econstructor.
         *** econstructor; eauto; repeat (econstructor; eauto).
             { rewrite -H1 Heq //=. }
             rewrite //=.
             unfold check. rewrite ifThenElse_if; eauto. rewrite /=. repeat econstructor; eauto.
             rewrite /when. rewrite ifThenElse_else; eauto. repeat econstructor.
         *** repeat econstructor => //=.
    - destruct op.
      (* Read *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H1; monad_inv; clear H1. subst.
        simpl in H2; inversion H2; monad_inv; subst; clear H2.
        inversion H3; monad_inv; subst; clear H3.
        destruct_head.
        destruct (world σ1 !! uint.Z n) eqn:Heq; rewrite Heq in H4; subst; last first.
        { inv_monad_false. }
        inversion H1; monad_inv; clear H1. subst.
        inversion H2; monad_inv; subst; clear H2.
        inversion H3; monad_inv; subst; clear H3.
             exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                        world := world pσ2; globals := globals pσ2 |}).
        destruct s0 as (?&[]); monad_inv.
        inversion H4; monad_inv; subst; clear H4.
        inversion H. intuition.
        destruct (world pσ2 !! uint.Z n) eqn:Hlook; last first.
        { exfalso. destruct H4.
          rewrite //= in H4.
          revert Hlook. rewrite -not_elem_of_dom.  intros Hfalso.
          apply Hfalso. rewrite -H4. apply elem_of_dom. eauto.
        }
        eexists.
        split_and!.
        *** simpl in *. split_and!; eauto.
        *** eauto.
        *** econstructor; eauto; repeat (econstructor; eauto).
               { rewrite Hlook //=. }
               { intros Hfalso. eapply H2. eauto. }
               { eapply H2. }
               {f_equal. f_equal. destruct pσ2; subst.
                 simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
                 f_equal; eauto.
                 rewrite -H1. do 4 f_equal.
                 destruct H4. edestruct H7 as [? [? ?]]; eauto. destruct H8. rewrite H10 in Hlook.
                 inversion Hlook. rewrite //=.
               }
      (* WriteOp *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H1; monad_inv; clear H1. subst.
        simpl in H2; inversion H2; monad_inv; subst; clear H2.
        inversion H3; monad_inv; subst; clear H3.
        inversion H1; monad_inv; clear H1. subst.
        inversion H2; monad_inv; subst; clear H2.
        destruct s0.
        monad_inv.
        destruct (world σ1 !! uint.Z n) eqn:Heq; rewrite Heq in H4; subst; last first.
        { inv_monad_false. }

        inversion H4; monad_inv; subst; clear H4.
        edestruct (state_compat_write_inv) as (cb&Hlookupcb&Hcases); eauto.
        destruct Hcases as [(Hcbeq&Hcase1)|(Hneq&Hcase2)].
        ** do 2 eexists; split_and!; eauto; [].
           repeat econstructor => //=.
           { rewrite lookup_insert_eq //=. }
           { rewrite //=. destruct H as (Hheap&?). rewrite -Hheap //=. }
           { rewrite //=. simpl in * => //=.
             rewrite /RecordSet.set //=.
             rewrite insert_insert_eq //=. f_equal; eauto.
             f_equal. destruct pσ2; f_equal; eauto.
             rewrite //=. rewrite //= in Hlookupcb.
             Unshelve. 2:{exact true. }
             rewrite /ADP.cblk_upd//=.
             rewrite insert_id; eauto.
             rewrite -Hcbeq. eauto.
           }
        ** do 2 eexists; split_and!; eauto; [].
           repeat econstructor => //=.
           { rewrite lookup_insert_eq //=. }
           { rewrite //=. destruct H as (Hheap&?). rewrite -Hheap //=. }
           { rewrite //=. simpl in * => //=.
             rewrite /RecordSet.set //=.
             rewrite insert_insert_eq //=. f_equal; eauto.
             f_equal. destruct pσ2; f_equal; eauto.
             rewrite //=. rewrite //= in Hlookupcb.
             Unshelve. 2:{exact false. }
             rewrite /ADP.cblk_upd//=.
             rewrite insert_id; eauto.
             rewrite Hlookupcb. f_equal.
             rewrite /RecordSet.set //= in Hcase2.
             destruct H as (_&Hdisk&_).
             simpl in Hdisk. destruct Hdisk as (?&Hval).
             edestruct (Hval) as (?&Hin&Hval'); eauto.
             { apply: lookup_insert_eq. }
             rewrite Hlookupcb in Hval'. inversion Hval'. rewrite //=.
           }
      (* SizeOp *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv. clear Hstep.
        destruct_head.
        inversion H1; monad_inv; clear H1.
        do 2 eexists; split_and!; eauto.
         econstructor; eauto; repeat (econstructor; eauto).
         do 2 f_equal.
         erewrite state_compat_disk_size; eauto.
      (* BarrierOp *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv. clear Hstep.
        destruct_head.
        inversion H1; monad_inv; clear H1.
        exists pσ2.
        edestruct (state_compat_post_flush_inv); eauto.
        eexists; split_and!; eauto.
        econstructor; eauto; repeat (econstructor; eauto).
        rewrite decide_True //.
    - (* NewProph *)
      rewrite /base_step//= in Hstep.
      inversion Hstep; monad_inv.
      inversion H; monad_inv; clear H.
      inversion H0; monad_inv; clear H0.
      inversion H3; monad_inv; clear H3.
      exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                   world := world pσ2; globals := globals pσ2 |}).
      eexists ({| used_proph_id := used_proph_id g1 |}).
      inversion H4. inversion H5. intuition.
        ** simpl in *. split_and!; eauto.
        ** split_and!; eauto.
        ** econstructor.
           *** repeat (econstructor; eauto).
           *** rewrite H16. repeat econstructor => //=.
               f_equal. destruct pσ2, pg2; subst.
               simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
               do 2 f_equal; eauto. congruence.
    - (* ResolveProph *)
      rewrite /base_step//= in Hstep. destruct_head.
      do 2 eexists. intuition; eauto.
      repeat (econstructor; eauto).
  Qed.

  Theorem prim_step'_simulation e1 σ1 g1 κ e2 σ2 g2 efs :
    prim_step' e1 σ1 g1 κ e2 σ2 g2 efs →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        prim_step' e1 pσ1 pg1 κ e2 pσ2 pg2 efs.
  Proof.
    intros Hprim.
    inversion Hprim; subst.
    intros. edestruct (base_step_simulation) as (pσ1&pg1&?&?&?); eauto.
    do 2 eexists; split_and!; eauto.
    econstructor; eauto.
  Qed.

  Theorem rtc_prim_step'_simulation e1 σ1 g1 e2 σ2 g2 :
    rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' [])
        (e1, (σ1, g1)) (e2, (σ2, g2)) →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' [])
            (e1, (pσ1, pg1)) (e2, (pσ2, pg2)).
  Proof.
    remember (e1, (σ1, g1)) as ρ1 eqn:Heqρ1.
    remember (e2, (σ2, g2)) as ρ2 eqn:Heqρ2.
    intros Hrtc.
    revert e1 σ1 g1 Heqρ1.
    revert e2 σ2 g2 Heqρ2.
    induction Hrtc; intros; subst.
    - inversion Heqρ1; subst. do 2 eexists; split_and!; eauto.
      apply rtc_refl.
    - destruct y as (e1'&σ1'&g1').
      edestruct (IHHrtc) as (pσ1'&pg1'&Hcompat1&Hcompat2&Hrtc'); eauto.
      edestruct prim_step'_simulation as (pσ1&pg1&Hcompat1_0&Hcompat2_0&Hstep); eauto.
      do 2 eexists; split_and!; eauto.
      econstructor; eauto. simpl. eauto.
  Qed.

  Definition base_step_barrier_looping e1 pσ1 pg1 :=
    base_reducible e1 pσ1 pg1 ∧
    (∀ κ e2 pσ2 pg2 efs,
        base_step e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
        e2 = e1 ∧ efs = [] ∧ pσ2 = pσ1 ∧ pg2 = pg1).

  Definition prim_step'_barrier_looping e1 pσ1 pg1 :=
    (∀ κ e2 pσ2 pg2 efs,
        prim_step' e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
        e2 = e1 ∧ efs = [] ∧ pσ2 = pσ1 ∧ pg2 = pg1).

  Lemma base_step_looping_to_prim_step' K e1 pσ1 pg1 :
    base_step_barrier_looping e1 pσ1 pg1 →
    prim_step'_barrier_looping (fill' K e1) pσ1 pg1.
  Proof.
    intros Hloop ????? Hprim. inversion Hprim as [K' e1']; subst.
    assert (K' = K ∧ e1' = e1) as (->&->).
    { eapply base_redex_unique; eauto.
      - rewrite /base_reducible; last by (do 5 eexists; econstructor; eauto); auto.
      - eapply Hloop.
    }
    edestruct Hloop as (Heq1&He2&Heq3&Heq4); first eassumption; subst.
    eauto.
  Qed.

  Theorem base_step_simulation_rev e1 pσ1 pg1 pσ2 pg2 σ1 g1 κ e2 efs :
    base_step e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
    state_compat σ1 pσ1 →
    global_compat g1 pg1 →
    ∃ σ2 g2 e2',
      base_step e1 σ1 g1 κ e2' σ2 g2 efs ∧
      ((e2 = e1 ∧ efs = [] ∧ pσ2 = pσ1 ∧ pg2 = pg1) ∨
       (e2 = e2' ∧ state_compat σ2 pσ2 ∧ global_compat g2 pg2)).
  Proof.
    rewrite /base_step.
    revert σ1 g1 κ e2 pσ1 pσ2 pg1 pg2 efs.
    destruct e1; intros σ1 g1 κ e2 pσ1 pσ2 pg1 pg2 efs Hstep; subst; try inversion Hstep; intuition eauto; subst.
    - monad_inv. do 3 eexists. split_and!; eauto.
      repeat econstructor.
    - rewrite /base_step//= in Hstep.
      destruct_head. inversion Hstep; subst.
      monad_inv. do 3 eexists. split_and!; eauto.
      repeat econstructor.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      destruct (un_op_eval op v) eqn:Heq; eauto; subst.
      * rewrite /unwrap /= in Hstep.
        inversion Hstep; monad_inv.
        do 3 eexists. split_and!; eauto.
        econstructor; rewrite ?Heq; eauto; econstructor; eauto.
      * simpl in Hstep. inversion Hstep; subst. inv_monad_false.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      destruct (bin_op_eval op v) eqn:Heq; eauto; subst.
      * rewrite /unwrap /= in Hstep.
        inversion Hstep; monad_inv.
        do 3 eexists. split_and!; eauto.
        econstructor; rewrite ?Heq; eauto; econstructor; eauto.
      * simpl in Hstep. inversion Hstep; subst. inv_monad_false.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct e1_1; monad_inv.
      destruct e1_2; monad_inv.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      destruct v; monad_inv.
      * inversion Hstep; subst. monad_inv.
        do 3 eexists. split_and!; eauto.
        econstructor; eauto; econstructor; eauto.
      * inversion Hstep; subst. monad_inv.
        do 3 eexists. split_and!; eauto.
        econstructor; eauto; econstructor; eauto.
    - inversion Hstep; subst; monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv. inversion H1. subst. monad_inv.
      inversion H2; subst.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; repeat econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        simpl in H2; inversion H2; monad_inv; subst; clear H2.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        inversion H3; monad_inv; subst; clear H3.
        destruct (heap pσ1 !! l) eqn:Heq; subst.
        ** inversion H7; monad_inv; subst.
           inversion H.
           intuition.
           eexists ({| heap := _; oracle := oracle σ1; trace := trace σ1;
                      world := world σ1 |}).
           do 2 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite H1 Heq. econstructor; eauto. }
               subst.
               rewrite //=. repeat econstructor; eauto.
           *** right. split_and!; eauto.
               split_and!; eauto. rewrite /RecordSet.set//=. congruence.
        ** inversion H7; intuition.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        simpl in H2; inversion H2; monad_inv; subst; clear H2.
        destruct x0. destruct n; monad_inv.
        inversion H3; monad_inv; subst; clear H3.
        destruct (heap pσ1 !! l) eqn:Heq; subst.
        ** inversion H7; monad_inv; subst.
           inversion H.
           intuition.
           eexists ({| heap := _; oracle := oracle σ1; trace := trace σ1;
                      world := world σ1 |}).
           do 2 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite H1 Heq. econstructor; eauto. }
               subst.
               rewrite //=. repeat econstructor; eauto.
           *** right. split_and!; eauto.
               split_and!; eauto. rewrite /RecordSet.set//=. congruence.
        ** inversion H7; intuition.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        simpl in H2; inversion H2; monad_inv; subst; clear H2.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        inversion H3; monad_inv; subst; clear H3.
        destruct (heap pσ1 !! l) eqn:Heq; subst.
        ** inversion H7; monad_inv; subst.
           inversion H.
           intuition.
           eexists ({| heap := _; oracle := oracle σ1; trace := trace σ1;
                      world := world σ1 |}).
           do 2 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite H1 Heq. econstructor; eauto. }
               subst.
               rewrite //=. repeat econstructor; eauto.
           *** right. split_and!; eauto.
               split_and!; eauto. rewrite /RecordSet.set//=. congruence.
        ** inversion H7; intuition.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        simpl in H2; inversion H2; monad_inv; subst; clear H2.
        destruct x0. destruct n; monad_inv.
        destruct (heap pσ1 !! l) eqn:Heq; subst.
        ** inversion H7; monad_inv; subst.
           inversion H.
           intuition.
           do 3 eexists. split_and!; eauto.
           repeat econstructor; rewrite ?H1 ?Heq; eauto; repeat econstructor.
        ** inversion H7; intuition.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        inversion H3; monad_inv; subst; clear H3.
        inversion H; intuition.
           eexists ({| heap := heap σ1; oracle := oracle σ1; trace := _;
                      world := world σ1 |}).
           do 2 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
           *** right. split_and!; eauto; subst; try congruence.
               split_and!; eauto. rewrite /RecordSet.set//=. congruence.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        inversion H; intuition.
           eexists ({| heap := heap σ1; oracle := oracle σ1; trace := _;
                      world := world σ1 |}).
           do 2 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
           *** right. split_and!; eauto; subst; try congruence.
               split_and!; eauto. rewrite /RecordSet.set//=. congruence.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        simpl in *. monad_inv.
        monad_inv; subst.
        inversion H. intuition.
        do 3 eexists. split_and!; eauto.
        repeat econstructor; rewrite ?H6 ?Heq; eauto; repeat econstructor.
    - rewrite /base_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      * (* AllocN *)
        inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1. subst.
        inversion H3; monad_inv; subst; clear H3.
        inversion H4; monad_inv; subst; clear H4.
        destruct s0 as (?&[]).
        destruct (decide (0 < uint.Z n)); monad_inv.
        monad_inv. inversion H1.
        eexists ({| heap := _; oracle := oracle σ1; trace := trace σ1;
                   world := world σ1 |}).
        subst. do 2 eexists. inversion H. intuition.
        ** econstructor.
           *** inversion H6; econstructor; eauto; repeat (econstructor; eauto).
               { unfold check. rewrite ifThenElse_if; eauto. rewrite /=. econstructor. rewrite //=. }
               { eapply H7. }
               { rewrite //=. rewrite H2. eapply H7. }
           *** repeat econstructor => //=.
        ** right. split_and!; eauto.
           split_and!; eauto. rewrite /RecordSet.set//=. congruence.
      * (* FinishStore *)
        inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1. subst.
        inversion H3; monad_inv; subst; clear H3.
        destruct (decide (is_Writing (heap pσ1 !! l))); monad_inv.
        inversion H2; monad_inv; subst; clear H2.
        eexists ({| heap := _; oracle := oracle σ1; trace := trace σ1;
                   world := world σ1 |}).
        subst. do 2 eexists. inversion H. intuition.
        ** econstructor.
           *** econstructor; eauto; repeat (econstructor; eauto).
               { unfold check. rewrite H1. rewrite ifThenElse_if; eauto. rewrite /=. econstructor. rewrite //=. }
           *** repeat econstructor => //=.
        ** right. split_and!; eauto.
           split_and!; eauto. rewrite /RecordSet.set//=. congruence.
      * (* AtomicStore *)
        inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        simpl in H2; inversion H2; monad_inv; subst; clear H2.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        inversion H3; monad_inv; subst; clear H3.
        destruct (heap pσ1 !! l) eqn:Heq; subst.
        ** inversion H7; monad_inv; subst.
           inversion H.
           intuition.
           eexists ({| heap := _; oracle := oracle σ1; trace := trace σ1;
                      world := world σ1 |}).
           do 2 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite H1 Heq. econstructor; eauto. }
               subst.
               rewrite //=. repeat econstructor; eauto.
           *** right. split_and!; eauto.
               split_and!; eauto. rewrite /RecordSet.set//=. congruence.
        ** inversion H7; intuition.
      * (* AtomicOp *)
        rewrite /atomically /= in Hstep.
        monad_inv.
        destruct (heap pσ1 !! l) eqn:Heq.
        2:{ simpl in *. by monad_inv. }
        rewrite /= in Hstep.
        monad_inv.
        rewrite /= in Hstep.
        destruct p. destruct n.
        { simpl in *. by monad_inv. }
        destruct n.
        2:{ simpl in *. by monad_inv. }
        destruct bin_op_eval eqn:Hbin.
        2:{ simpl in *. by monad_inv. }
        rewrite /= in Hstep.
        monad_inv.

        inversion H. intuition.
        do 2 eexists.
        eexists.
        split_and!.
        *** simpl in *. econstructor; eauto; repeat econstructor; eauto.
            { rewrite H1. rewrite Heq. done. }
            simpl in *.
            monad_simpl.
            unfold ret.
            monad_simpl.
            simpl.
            monad_simpl.
        *** right. split_and!; eauto.
            split_and!; eauto.
            rewrite /RecordSet.set//=. congruence.
      * (* GlobalPut *)
        inversion Hstep; monad_inv.
        simpl in *.
        monad_inv.
        destruct H. intuition.
        eexists ({| heap := _; oracle := oracle σ1; trace := trace σ1;
                                                    world := world σ1 |}).
        do 2 eexists.
        split_and!.
        *** econstructor; eauto; repeat econstructor; eauto.
        *** right. split_and!; eauto.
            split_and!; eauto.
            rewrite /RecordSet.set//=. congruence.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; monad_inv.
      inversion H1; monad_inv; clear H1. subst.
      simpl in H2; inversion H2; monad_inv; subst; clear H2.
      destruct_head.
      rewrite //= in H3.
      destruct (heap pσ1 !! l) eqn:Heq; monad_inv; try inv_monad_false.
      destruct (decide (vals_compare_safe v1 v)); monad_inv; try inv_monad_false; last first.
      { intuition eauto. }
      inversion H3; monad_inv; subst; clear H3.
      destruct (decide (v1 = v)).
      * subst. rewrite ifThenElse_if in H1; eauto.
        destruct (decide (n = O)); monad_inv; last first.
        { rewrite ifThenElse_else in H1; eauto. simpl in H1. inversion H1; monad_inv. }
        rewrite ifThenElse_if in H1; eauto.
        simpl in H1. monad_inv. destruct s2; monad_inv.
        simpl in H4. monad_inv.
        eexists ({| heap := _; oracle := oracle σ1; trace := trace σ1;
                    world := world σ1 |}).
        subst. do 2 eexists. inversion H. intuition.
        ** econstructor.
           *** econstructor; eauto; repeat (econstructor; eauto).
               { rewrite H1 Heq //=. }
               rewrite //=.
               unfold check. rewrite ifThenElse_if; eauto. rewrite /=. repeat econstructor; eauto.
               rewrite /when. rewrite ifThenElse_if; eauto. repeat econstructor.
           *** repeat econstructor => //=.
        ** right. split_and!; eauto.
           split_and!; eauto. rewrite /RecordSet.set//=. congruence.
      * rewrite ifThenElse_else in H1; auto. simpl in H1. monad_inv.
        inversion H4. subst. monad_inv.
      subst. do 3 eexists. inversion H. intuition.
      ** econstructor.
         *** econstructor; eauto; repeat (econstructor; eauto).
             { rewrite H1 Heq //=. }
             rewrite //=.
             unfold check. rewrite ifThenElse_if; eauto. rewrite /=. repeat econstructor; eauto.
             rewrite /when. rewrite ifThenElse_else; eauto. repeat econstructor.
         *** repeat econstructor => //=.
      ** right. split_and!; eauto.
    - destruct op.
      (* Read *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H1; monad_inv; clear H1. subst.
        simpl in H2; inversion H2; monad_inv; subst; clear H2.
        inversion H3; monad_inv; subst; clear H3.
        destruct_head.
        destruct (world pσ1 !! uint.Z n) eqn:Heq; rewrite Heq in H4; subst; last first.
        { inv_monad_false. }
        inversion H1; monad_inv; clear H1. subst.
        inversion H2; monad_inv; subst; clear H2.
        inversion H3; monad_inv; subst; clear H3.
             eexists ({| heap := heap pσ2; oracle := oracle σ1; trace := trace σ1;
                        world := world σ1 |}).
        destruct s0 as (?&[]); monad_inv.
        inversion H4; monad_inv; subst; clear H4.
        inversion H. intuition.
        destruct (world σ1 !! uint.Z n) eqn:Hlook; last first.
        { exfalso. destruct H4.
          rewrite //= in H4.
          revert Hlook. rewrite -not_elem_of_dom.  intros Hfalso.
          apply Hfalso. rewrite H4. apply elem_of_dom. eauto.
        }
        do 2 eexists.
        split_and!.
        *** econstructor; eauto; repeat (econstructor; eauto).
               { rewrite Hlook //=. }
               { intros Hfalso. eapply H2. eauto. }
               { rewrite H1. eapply H2. }
               { f_equal. f_equal. destruct σ1; subst.
                 simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
                 f_equal; eauto.
                 rewrite H1. do 4 f_equal.
                 destruct H4. edestruct H7 as [? [? ?]]; eauto. destruct H8. rewrite H10 in Heq. inversion Heq.
                 subst. eauto.
               }
        *** right. split_and!; eauto.
            split_and!; eauto.
      (* WriteOp *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H1; monad_inv; clear H1. subst.
        simpl in H2; inversion H2; monad_inv; subst; clear H2.
        inversion H3; monad_inv; subst; clear H3.
        inversion H1; monad_inv; clear H1. subst.
        inversion H2; monad_inv; subst; clear H2.
        destruct s0.
        monad_inv.
        destruct (world pσ1 !! uint.Z n) eqn:Heq; rewrite Heq in H4; subst; last first.
        { inv_monad_false. }
        inversion H. intuition.
        destruct (world σ1 !! uint.Z n) eqn:Hlook; last first.
        { exfalso. inversion H4.
          subst. revert Hlook. rewrite -not_elem_of_dom.  intros Hfalso.
          apply Hfalso. destruct H7 as (Heqdom&_). rewrite Heqdom.
          eapply (elem_of_dom_2 (D := gset _) (world pσ1)); eauto.
        }
        inversion H4; monad_inv; subst; clear H4.
        inversion H1; monad_inv; subst. clear H1.
        inversion H5; monad_inv; subst.
        destruct H7.
        eexists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                    world := _ |}).
        do 2 eexists; split_and!; eauto.
        ** econstructor; eauto; repeat (econstructor; eauto).
           { rewrite Hlook //. }
           { rewrite //=. rewrite H2. eauto. }
           rewrite //=.
        ** right. split_and!; eauto.
           split_and!; eauto.
           split => //=.
           *** rewrite ?dom_insert_L; eauto. rewrite H1 //.
           *** intros addr ab Hlookup.
               destruct (decide (addr = uint.Z n)); last first.
               {
                 rewrite lookup_insert_ne // in Hlookup.
                 edestruct H7 as (bd&?&?); try eapply Hlookup; eauto. exists bd; split_and!; eauto.
                 rewrite lookup_insert_ne; eauto.
               }
               subst.
               destruct x2.
               **** rewrite lookup_insert_eq // in Hlookup. inversion Hlookup; subst.
                    eexists. rewrite lookup_insert_eq //; split; eauto.
                    rewrite log_heap.possible_async_put elem_of_app. right.
                    econstructor.
               **** rewrite lookup_insert_eq // in Hlookup. inversion Hlookup; subst.
                    eexists. rewrite lookup_insert_eq //; split; eauto.
                    rewrite log_heap.possible_async_put elem_of_app. left.
                    edestruct H7 as (?&Hposs&Hlook'); eauto.
                    rewrite Heq in Hlook'. inversion Hlook' => //=.
      (* SizeOp *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H1; monad_inv; clear H1.
        do 3 eexists; split_and!; eauto.
         econstructor; eauto; repeat (econstructor; eauto).
         do 2 f_equal.
         erewrite state_compat_disk_size; eauto.
      (* BarrierOp *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H1; monad_inv; clear H1.
        destruct (decide (ADP.all_synced _)).
        **  monad_inv.
            do 3 eexists. split_and!.
            { repeat econstructor. }
            right. split_and!; eauto.
            eapply state_compat_all_synced_post_flush; eauto.
        ** monad_inv.
            do 3 eexists. split_and!.
            { repeat econstructor. }
            left. split_and!; eauto.
    - (* NewProph *)
      rewrite /base_step//= in Hstep.
      inversion Hstep; monad_inv.
      inversion H; monad_inv; clear H.
      simpl in H0; inversion H0; monad_inv.
      simpl in H3; inversion H3; monad_inv; clear H3.
      eexists σ1.
      eexists ({| used_proph_id := _ |}).
      eexists. inversion H4. inversion H5. intuition.
      { simpl in *. repeat (econstructor; eauto). rewrite H6. done. }
      right. split_and!; eauto.
      { congruence. }
      split_and!; eauto. rewrite /RecordSet.set//=. congruence.
    - (* ResolveProph *)
      rewrite /base_step//= in Hstep. destruct_head.
      do 3 eexists. intuition; eauto.
      repeat (econstructor; eauto).
  Qed.

  Theorem prim_step'_simulation_rev e1 pσ1 pg1 pσ2 pg2 σ1 g1 κ e2 efs :
    prim_step' e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
    state_compat σ1 pσ1 →
    global_compat g1 pg1 →
    ∃ σ2 g2 e2',
      prim_step' e1 σ1 g1 κ e2' σ2 g2 efs ∧
      ((e2 = e1 ∧ efs = [] ∧ pσ2 = pσ1 ∧ pg2 = pg1) ∨
       (e2 = e2' ∧ state_compat σ2 pσ2 ∧ global_compat g2 pg2)).
  Proof.
    intros Hprim.
    inversion Hprim; subst.
    intros. edestruct (base_step_simulation_rev) as (σ2&g2&e2alt'&Hstep&Hcases); eauto.
    do 3 eexists. split_and!; eauto.
    { econstructor; eauto. }
    { destruct Hcases as [Hleft|Hright].
      { left. destruct Hleft as (->&->&->&->); eauto. }
      destruct Hright as (->&Hcompat&Hgcompat); eauto.
    }
  Qed.

  Lemma prim_step'_rtc_looping e1 pσ1 pg1 e2 pσ2 pg2 :
    prim_step'_barrier_looping e1 pσ1 pg1 →
    rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' [])
        (e1, (pσ1, pg1)) (e2, (pσ2, pg2)) →
    e2 = e1 ∧ pσ2 = pσ1 ∧ pg2 = pg1.
  Proof.
    intros Hlooping Hrtc.
    remember (e1, (pσ1, pg1)) as pρ1 eqn:Heqρ1.
    remember (e2, (pσ2, pg2)) as pρ2 eqn:Heqρ2.
    revert Hlooping.
    revert e1 pσ1 pg1 Heqρ1.
    revert e2 pσ2 pg2 Heqρ2.
    induction Hrtc; intros; subst.
    - inversion Heqρ1; subst; eauto.
    - destruct y as (e1'&pσ1'&pg1').
      eapply Hlooping in H as (->&?&->&->).
      eapply IHHrtc; eauto.
  Qed.

  Theorem prim_step'_rtc_simulation_rev e1 pσ1 pg1 pσ2 pg2 σ1 g1 e2 :
    rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' [])
        (e1, (pσ1, pg1)) (e2, (pσ2, pg2)) →
    state_compat σ1 pσ1 →
    global_compat g1 pg1 →
    ∃ σ2 g2,
      rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' [])
          (e1, (σ1, g1)) (e2, (σ2, g2)) ∧
       (state_compat σ2 pσ2 ∧ global_compat g2 pg2).
  Proof.
    remember (e1, (pσ1, pg1)) as pρ1 eqn:Heqρ1.
    remember (e2, (pσ2, pg2)) as pρ2 eqn:Heqρ2.
    intros Hrtc.
    revert e1 σ1 pσ1 pg1 Heqρ1.
    revert e2 g1 pσ2 pg2 Heqρ2.
    induction Hrtc; intros; subst.
    - inversion Heqρ1; subst. do 2 eexists; split_and!; eauto.
      apply rtc_refl.
    - destruct y as (e1'&pσ1'&pg1').
      edestruct prim_step'_simulation_rev as (σ1'&g1'&e2'&Hstep&Hcases); eauto.
      destruct Hcases as [Hloop|Hprogress].
      * edestruct Hloop as (Heq1&Heq2&Heq3&Heq4); eauto; subst.
        edestruct IHHrtc; eauto.
      * destruct Hprogress as (->&Hcompat'&Hgcompat').
        edestruct IHHrtc as (σ2&g2&Hrtc'&Hcompat''&Hgcompat''); eauto.
        do 2 eexists; split; eauto.
        { econstructor; eauto. simpl. eauto. }
  Qed.

  Definition match_curr (dd : @ffi_state ADP.disk_model) (ad: @ffi_state ADP.disk_model) :=
    dom dd = dom ad ∧
    (∀ addr ab, dd !! addr = Some ab → ∃ ab', ad !! addr = Some ab' ∧ ADP.curr_val ab = ADP.curr_val ab').

  Definition state_match_curr (pσ1 : pstate) (pσ2 : pstate) :=
    heap pσ1 = heap pσ2 ∧
    match_curr (world pσ1) (world pσ2) ∧
    trace pσ1 = trace pσ2 ∧
    oracle pσ1 = oracle pσ2 ∧
    globals pσ1 = globals pσ2
  .

  Lemma state_match_curr_disk_size σ pσ :
    state_match_curr σ pσ →
    ADP.disk_size (world σ) = ADP.disk_size (world pσ).
  Proof.
    intros (?&(Hdom&Hdisk)&_). rewrite /AD.disk_size/ADP.disk_size Hdom //.
  Qed.

  Lemma disk_compat_common_match_curr d pd1 pd2 :
    disk_compat d pd1 →
    disk_compat d pd2 →
    match_curr pd1 pd2.
  Proof.
    intros (Hdom1&Hlook1) (Hdom2&Hlook2).
    split; first congruence.
    intros addr cb Hin1.
    assert (is_Some (d !! addr)) as (ab'&Hab).
    { apply (elem_of_dom d). rewrite Hdom1. apply (elem_of_dom pd1); eauto. }
    edestruct Hlook1 as (b&Hin&Heq1); eauto.
    edestruct Hlook2 as (b'&Hin'&Heq2); eauto.
    eexists. split; eauto. rewrite //=. rewrite Hin1 in Heq1. inversion Heq1; subst; eauto.
  Qed.

  Lemma state_compat_state_match_curr σ pσ1 pσ2:
    state_compat σ pσ1 →
    state_compat σ pσ2 →
    state_match_curr pσ1 pσ2.
  Proof.
    rewrite /state_compat/state_match_curr.
    intros. intuition (try congruence).
    eapply disk_compat_common_match_curr; eauto.
  Qed.

  Lemma global_compat_match_eq g pg1 pg2 :
    global_compat g pg1 →
    global_compat g pg2 →
    pg1 = pg2.
  Proof.
    destruct g, pg1, pg2. rewrite /global_compat /=.
    intros. intuition. congruence.
  Qed.

  Lemma all_synced_match_curr_compat_full (pσ1' pσ1 : pstate) :
    ADP.all_synced (world pσ1') →
    state_match_curr pσ1 pσ1' →
    ∀ σ2 : dstate, state_compat σ2 pσ1 → state_compat σ2 pσ1'.
  Proof.
    intros Hsynced (Hheap&Hmatch_curr&?&?&?).
    intros σ2 (?&Hdisk&?&?&?). split_and!; try congruence.
    destruct Hmatch_curr as (Hdom&Hvals).
    destruct Hdisk as (Hdom'&Hvals').
    split; first congruence.
    intros addr ab Hlook.
    edestruct Hvals' as (bd&Hin&Hlook'); eauto.
    edestruct Hvals as (cb'&Hlook''&Hcurr); eauto.
    destruct cb'.
    exists (log_heap.latest ab); split.
    { rewrite /log_heap.possible//=. apply elem_of_app; right; econstructor. }
    rewrite Hlook''.
    rewrite //= in Hcurr. subst. do 2 f_equal; eauto.
    opose proof (Hsynced _ _ _); eauto.
  Qed.

  Lemma all_synced_compat_full (pσ1' pσ1 : pstate) σ1:
    ADP.all_synced (world pσ1') →
    state_compat σ1 pσ1 →
    state_compat σ1 pσ1' →
    ∀ σ2 : dstate, state_compat σ2 pσ1 → state_compat σ2 pσ1'.
  Proof.
    intros Hsynced Hcompat1 Hcompat1'.
    intros. eapply all_synced_match_curr_compat_full; eauto.
    eapply state_compat_state_match_curr.
    { eapply Hcompat1. }
    eauto.
  Qed.

  Definition d_to_pd (d : gmap Z _) :=
    ((λ ab, {| ADP.curr_val := log_heap.latest ab;
                       ADP.crash_val := log_heap.latest ab |}) <$> d).

  Lemma stable_disk_compat_unique d pd :
    stable_disk d →
    disk_compat d pd →
    pd = d_to_pd d.
  Proof.
    rewrite /stable_disk/disk_compat.
    intros Hstable (Hdom&Hcompat). unshelve (apply: map_eq).
    intros z.
    rewrite /d_to_pd//= lookup_fmap. destruct (d !! z) as [cb|] eqn:Hd.
    - rewrite Hd //=. edestruct Hcompat as (b&Hposs&->); eauto.
      do 2 f_equal. rewrite /log_heap.possible in Hposs.
      erewrite Hstable in Hposs; eauto.
      simpl in Hposs. set_solver.
    - rewrite Hd /=. apply not_elem_of_dom.
      rewrite -Hdom. apply (not_elem_of_dom d). eauto.
  Qed.

  Lemma disk_compat_inhabited_all_synced d :
    ADP.all_synced (d_to_pd d) ∧ disk_compat d (d_to_pd d).
  Proof.
    split.
    - intros z cblk. rewrite lookup_fmap.
      intros Hsome%fmap_Some_1. destruct Hsome as (ab'&Hlook'&Hflush).
      rewrite Hflush => //=.
    - split.
      { rewrite dom_fmap_L //. }
      intros z cblk Hlook. eexists; split; last first.
      { rewrite lookup_fmap Hlook //. }
      rewrite /log_heap.possible//=. apply elem_of_app; right; econstructor.
  Qed.

  Lemma compat_inhabited_all_synced σ g :
    ∃ (pσ : pstate) pg, ADP.all_synced (world pσ) ∧ state_compat σ pσ ∧ global_compat g pg.
  Proof.
    edestruct (disk_compat_inhabited_all_synced (world σ)) as (pd&?&?).
    eexists {| heap := heap σ;
               world := _;
               trace := trace σ;
               oracle := oracle σ |}.
    eexists {| used_proph_id := _ |}; split; auto => //=.
  Qed.

  Lemma compat_inhabited σ g :
    ∃ pσ pg, state_compat σ pσ ∧ global_compat g pg.
  Proof. edestruct compat_inhabited_all_synced as (?&?&?&?); eauto. Qed.

  Lemma disk_compat_inhabited_rev pd :
    ∃ d, disk_compat d pd.
  Proof.
    exists ((λ ab, {| log_heap.latest := ADP.curr_val ab;
                      log_heap.pending := [ADP.crash_val ab] |}) <$> pd).
    split.
    { rewrite dom_fmap_L //. }
    - intros z cblk. rewrite lookup_fmap.
      intros Hsome%fmap_Some_1. destruct Hsome as (ab'&Hlook'&Hflush).
      rewrite Hflush => //=.
      destruct ab'.
      eexists; split; last first.
      { rewrite Hlook' //=. }
      rewrite //= /log_heap.possible//=. left.
  Qed.

  Lemma compat_inhabited_rev pσ pg:
    ∃ σ g, state_compat σ pσ ∧ global_compat g pg.
  Proof.
    edestruct (disk_compat_inhabited_rev (world pσ)) as (d&?).
    eexists {| heap := heap pσ;
               world := _;
               trace := trace pσ;
               oracle := oracle pσ |}.
    eexists {| used_proph_id := _ |}; split; auto => //=.
  Qed.

  Lemma match_curr_insert_hd x0 x1 x2 c0 d1 d2 n :
    match_curr d1 d2 →
    match_curr (<[n:=ADP.cblk_upd x0 x1 x2]> d1) (<[n:=ADP.cblk_upd c0 x1 true]> d2).
  Proof.
    intros (Hdom&Hvals).
    split.
    - rewrite ?dom_insert_L; eauto. rewrite Hdom //.
    - intros ?? Hlook.
      destruct (decide (addr = n)).
      { subst. eexists. rewrite lookup_insert_eq. rewrite lookup_insert_eq in Hlook.
        split.
        { rewrite //=. }
        inversion Hlook. subst. rewrite //=.
      }
      rewrite lookup_insert_ne //. rewrite lookup_insert_ne // in Hlook.
      eapply Hvals; eauto.
  Qed.

  Lemma all_synced_insert_synced d n c0 x1 :
    ADP.all_synced d →
    ADP.all_synced (<[n:=ADP.cblk_upd c0 x1 true]> d).
  Proof.
    rewrite /ADP.all_synced. intros Hvals z cblk Hlook.
    destruct (decide (z = n)).
    { subst. rewrite lookup_insert_eq in Hlook. inversion Hlook; subst => //=. }
    eapply Hvals. rewrite lookup_insert_ne in Hlook; eauto.
  Qed.

  Theorem base_step_compat_simulation e1 pσ1 pg1 pσ1' pg1' pσ2 pg2 κ e2 efs :
    base_step e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
    state_match_curr pσ1 pσ1' →
    pg1 = pg1' →
    (∃ e2' pσ2' pg2' efs',
        base_step e1 pσ1' pg1' κ e2' pσ2' pg2' efs' ∧
        state_match_curr pσ2 pσ2' ∧
        pg2 = pg2' ∧
        (ADP.all_synced (world pσ1') →
           ADP.all_synced (world pσ2') ∧
           ((e2 = e1 ∧ efs = [] ∧ pσ2 = pσ1 ∧ pg2 = pg1) ∨
            (e2 = e2' ∧ efs = efs')))).
  Proof.
    rewrite /base_step.
    intros Hstep Hmatch_curr <-.
    destruct e1; subst; try inversion Hstep; intuition eauto; subst.
    - rewrite /base_step//= in Hstep.
      destruct_head. inversion Hstep; subst.
      monad_inv. do 4 eexists. split_and!; eauto.
      { repeat econstructor; eauto. }
    - rewrite /base_step//= in Hstep.
      destruct_head. inversion Hstep; subst.
      monad_inv. do 4 eexists. split_and!; eauto.
      { repeat econstructor; eauto. }
    - rewrite /base_step//= in Hstep.
      destruct_head.
      destruct (un_op_eval op v) eqn:Heq; eauto; subst.
      * rewrite /unwrap /= in Hstep.
        inversion Hstep; monad_inv.
        do 4 eexists. split_and!; eauto.
        econstructor; rewrite ?Heq; eauto; econstructor; eauto.
      * simpl in Hstep. inversion Hstep; subst. inv_monad_false.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      destruct (bin_op_eval op v) eqn:Heq; eauto; subst.
      * rewrite /unwrap /= in Hstep.
        inversion Hstep; monad_inv.
        do 4 eexists. split_and!; eauto.
        econstructor; rewrite ?Heq; eauto; econstructor; eauto.
      * simpl in Hstep. inversion Hstep; subst. inv_monad_false.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 4 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct e1_1; monad_inv.
      destruct e1_2; monad_inv.
      inversion Hstep; subst.
      monad_inv.
      do 4 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 4 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 4 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 4 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 4 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      destruct v; monad_inv.
      * inversion Hstep; subst. monad_inv.
        do 4 eexists. split_and!; eauto.
        econstructor; eauto; econstructor; eauto.
      * inversion Hstep; subst. monad_inv.
        do 4 eexists. split_and!; eauto.
        econstructor; eauto; econstructor; eauto.
    - inversion Hstep; subst; monad_inv.
      do 4 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv. inversion H. subst. monad_inv.
      inversion H0; subst.
      do 4 eexists. split_and!; eauto.
      econstructor; eauto; repeat econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      * inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H.
        simpl in H0; inversion H0; monad_inv; subst; clear H0.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        inversion H1; monad_inv; subst; clear H1.
        destruct (heap pσ1 !! l) eqn:Heq; subst.
        ** inversion H5; monad_inv; subst.
           destruct Hmatch_curr as (?&?&?&?&?).
           do 4 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite -H Heq. econstructor; eauto. }
               subst.
               rewrite //=. repeat econstructor; eauto.
           *** split_and!; eauto. rewrite /RecordSet.set//=. congruence.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
        ** inversion H5; intuition.
      * inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H.
        simpl in H0; inversion H0; monad_inv; subst; clear H0.
        destruct x0. destruct n; monad_inv.
        inversion H1; monad_inv; subst; clear H1.
        destruct (heap pσ1 !! l) eqn:Heq; subst.
        ** inversion H5; monad_inv; subst.
           destruct Hmatch_curr as (?&?&?&?).
           intuition.
           do 4 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite -H Heq. econstructor; eauto. }
               subst.
               rewrite //=. repeat econstructor; eauto.
           *** split_and!; eauto. destruct pσ1, pσ1' => //=.
               simpl in H. rewrite -H. eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
        ** inversion H5; intuition.
      * inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H.
        simpl in H0; inversion H0; monad_inv; subst; clear H0.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        inversion H1; monad_inv; subst; clear H1.
        destruct (heap pσ1 !! l) eqn:Heq; subst.
        ** inversion H5; monad_inv; subst.
           destruct Hmatch_curr as (?&?&?&?&?).
           do 4 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite -H Heq. econstructor; eauto. }
               subst.
               rewrite //=. repeat econstructor; eauto.
           *** split_and!; eauto. destruct pσ1, pσ1' => //=.
               simpl in H. rewrite -H. eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
        ** inversion H5; intuition.
      * inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H.
        simpl in H0; inversion H0; monad_inv; subst; clear H0.
        destruct x0. destruct n; monad_inv.
        destruct (heap pσ1 !! l) eqn:Heq; subst.
        ** inversion H5; monad_inv; subst.
           destruct Hmatch_curr as (?&?&?&?&?).
           do 4 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite -H Heq. econstructor; eauto. }
               subst.
               rewrite //=.
           *** split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
        ** inversion H5; intuition.
      * inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H.
        inversion H1; monad_inv; subst; clear H1.
        inversion Hmatch_curr; intuition.
           do 4 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
           *** split_and!; eauto. destruct pσ1, pσ1' => //=.
               simpl in *. subst. eauto.
           *** eauto.
           *** rewrite //=. intros; split; eauto.
               right. intuition congruence.
      * inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H.
        inversion Hmatch_curr; intuition.
           do 4 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
           *** split_and!; eauto. destruct pσ1, pσ1' => //=.
               simpl in *. intuition congruence.
           *** eauto.
           *** rewrite //=. intros; split; eauto.
      * inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H.
        simpl in *. monad_inv.
        destruct Hmatch_curr as (?&?&?&?&?).
        do 4 eexists.
        split_and!.
        ** repeat econstructor.
        ** split_and!; eauto.
        ** eauto.
        ** intros. econstructor; eauto. right. repeat econstructor; eauto.
           rewrite H3. done.
    - (* Primitive2 *)
      rewrite /base_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      * (* AllocN *)
        inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H. subst.
        inversion H1; monad_inv; subst; clear H1.
        inversion H2; monad_inv; subst; clear H2.
        destruct s0 as (?&[]).
        destruct (decide (0 < uint.Z n)); monad_inv.
        monad_inv. inversion H. subst.
        do 4 eexists.
        subst. inversion Hmatch_curr. intuition.
        ** econstructor.
           *** inversion H4; econstructor; eauto.
               { unfold check. rewrite ifThenElse_if; eauto. rewrite /=. econstructor. rewrite //=. }
               { repeat econstructor => //=; try eapply H4. rewrite -H0; eapply H4. }
           *** repeat econstructor => //=.
        ** split_and!; eauto. rewrite //=.
           simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
           intuition congruence.
        ** rewrite //=.
      * (* FinishStore *)
        inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H. subst.
        inversion H1; monad_inv; subst; clear H1.
        destruct (decide (is_Writing (heap pσ1 !! l))); monad_inv.
        inversion H0; monad_inv; subst; clear H0.
        do 4 eexists. inversion Hmatch_curr; intuition.
        ** econstructor.
           *** econstructor; eauto; repeat (econstructor; eauto).
               { unfold check. rewrite -H. rewrite ifThenElse_if; eauto. rewrite /=. econstructor. rewrite //=. }
           *** repeat econstructor => //=.
        ** split_and!; eauto. rewrite //=.
           simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
           intuition congruence.
        ** rewrite //=.
      * (* AtomicStore *)
        inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H.
        simpl in H0; inversion H0; monad_inv; subst; clear H0.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        inversion H1; monad_inv; subst; clear H1.
        destruct (heap pσ1 !! l) eqn:Heq; subst.
        ** inversion H5; monad_inv; subst.
           destruct Hmatch_curr as (?&?&?&?&?).
           do 4 eexists.
           split_and!.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite -H Heq. econstructor; eauto. }
               subst.
               rewrite //=. repeat econstructor; eauto.
           *** split_and!; eauto. destruct pσ1, pσ1' => //=.
               simpl in H. rewrite -H. eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
        ** inversion H5; intuition.
      * (* AtomicOp *)
        rewrite /atomically in Hstep. simpl in *.
        monad_inv. simpl in *.
        destruct (heap _ !! _) eqn:Hheap; simpl in *; monad_inv.
        2:{ by exfalso. }
        simpl in *; monad_inv;
        simpl in *; destruct p;
        destruct n; simpl in *; monad_inv.
        { by exfalso. }
        destruct n; simpl in *; monad_inv.
        2:{ by exfalso. }
        simpl in *. monad_inv.
        destruct bin_op_eval eqn:Hbin; simpl in *; monad_inv.
        2:{ by exfalso. }
        destruct Hmatch_curr as (?&?&?&?&?).
        do 4 eexists.
        split_and!.
        ** monad_simpl.
           rewrite -H.
           repeat (simpl || monad_simpl).
        ** simpl. split_and!; eauto. simpl. f_equal. done.
        ** done.
        ** eauto.
      * (* GlobalPut *)
        inversion Hstep; monad_inv.
        inversion H; monad_inv; clear H.
        destruct Hmatch_curr as (?&?&?&?&?).
        do 4 eexists.
        split_and!.
        ** econstructor; eauto; repeat econstructor; eauto.
        ** split_and!; eauto. destruct pσ1, pσ1' => //=.
            simpl in *. subst. eauto.
        ** eauto.
        ** econstructor; eauto; repeat econstructor; eauto.
    - rewrite /base_step//= in Hstep.
      destruct_head.
      inversion Hstep; monad_inv.
      inversion H; monad_inv; clear H. subst.
      simpl in H0; inversion H0; monad_inv; subst; clear H0.
      destruct_head.
      rewrite //= in H1.
      destruct (heap pσ1 !! l) eqn:Heq; monad_inv; try inv_monad_false.
      destruct (decide (vals_compare_safe v1 v)); monad_inv; try inv_monad_false; last first.
      { intuition eauto. }
      inversion H2; monad_inv; subst; clear H2.
      destruct (decide (v1 = v)).
      * subst. rewrite ifThenElse_if in H1; eauto.
        destruct (decide (n = O)); monad_inv; last first.
        { rewrite ifThenElse_else in H1; eauto. simpl in H1. inversion H1; monad_inv. exfalso; eauto. }
        rewrite ifThenElse_if in H1; eauto.
        simpl in H1. monad_inv.
        do 4 eexists. inversion Hmatch_curr. intuition.
        ** econstructor.
           *** econstructor; eauto; repeat (econstructor; eauto).
               { rewrite -H Heq //=. }
               rewrite //=.
               unfold check. rewrite ifThenElse_if; eauto. rewrite /=. repeat econstructor; eauto.
               rewrite /when. rewrite ifThenElse_if; eauto. repeat econstructor.
           *** repeat econstructor => //=.
        ** split_and!; eauto. rewrite //=.
           simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
           intuition congruence.
        ** rewrite //=.
      * rewrite ifThenElse_else in H1; auto. simpl in H1. monad_inv.
        do 4 eexists. inversion Hmatch_curr. intuition.
        ** econstructor.
           *** econstructor; eauto; repeat (econstructor; eauto).
               { rewrite -H Heq //=. }
               rewrite //=.
               unfold check. rewrite ifThenElse_if; eauto. rewrite /=. repeat econstructor; eauto.
               rewrite /when. rewrite ifThenElse_else; eauto. repeat econstructor.
           *** repeat econstructor => //=.
        ** rewrite //=.
        ** rewrite //=.
    - destruct op.
      (* Read *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H; monad_inv; clear H. subst.
        simpl in H0; inversion H0; monad_inv; subst; clear H0.
        inversion H1; monad_inv; subst; clear H1.
        destruct_head.
        destruct (world pσ1 !! uint.Z n) eqn:Heq; rewrite Heq in H2; subst; last first.
        { inv_monad_false. }
        inversion H0; monad_inv; clear H0. subst.
        inversion H2; monad_inv; subst; clear H2.
        destruct s0 as (?&[]); monad_inv.
        inversion H; monad_inv; subst; clear H.
        inversion H4; monad_inv; subst; clear H4.
        inversion Hmatch_curr. intuition.
        destruct (world pσ1' !! uint.Z n) eqn:Hlook; last first.
        { exfalso. destruct H3.
          rewrite //= in H3.
          revert Hlook. rewrite -not_elem_of_dom.  intros Hfalso.
          apply Hfalso. rewrite -H3. apply elem_of_dom. eauto.
        }
        do 4 eexists.
        split_and!.
        *** econstructor; eauto.
            { repeat econstructor.
              { rewrite Hlook //=. }
               { intros Hfalso. eapply H. eauto. }
               { rewrite -H1. eapply H. }
               { eauto. }
            }
            repeat econstructor.
        *** simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
            rewrite /state_match_curr//=.
            split_and!; eauto.
            assert (ADP.curr_val x0 = ADP.curr_val c) as ->; last by congruence.
            {  edestruct H3 as (Hdom&Hlook'). edestruct (Hlook') as (?&?&?); eauto.
               destruct s, pσ1'. simpl in *; subst.
               inversion Hlook. congruence.
            }
        *** eauto.
        *** eauto.
      (* WriteOp *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H; monad_inv; clear H. subst.
        inversion H1; monad_inv; subst; clear H1.
        inversion H; monad_inv; subst; clear H.
        destruct s0.
        inversion H2; monad_inv; subst; clear H2.
        inversion H3; monad_inv; subst; clear H3.
        inversion H; monad_inv; subst; clear H.
        simpl in H0; inversion H0.
        subst. monad_inv.
        destruct (world pσ1 !! uint.Z n) eqn:Heq; rewrite Heq in H4; subst; last first.
        { inv_monad_false. }
        inversion Hmatch_curr. intuition.
        inversion H4. subst.
        destruct (world pσ1' !! uint.Z n) eqn:Hlook; last first.
        { exfalso. inversion H4.
          subst. revert Hlook. rewrite -not_elem_of_dom.  intros Hfalso.
          apply Hfalso. destruct H5 as (Heqdom&_). rewrite -Heqdom.
          eapply (elem_of_dom_2 (D := gset _) (world pσ1)); eauto.
        }
        inversion H4; monad_inv; subst; clear H4.
        subst.
        destruct H5.
        do 4 eexists; split_and!.
        ** econstructor; eauto.
            { repeat econstructor.
              { rewrite Hlook //. }
              { rewrite //=. rewrite -H. eauto. }
            }
            repeat econstructor.
        ** simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
            rewrite /state_match_curr//=.
            split_and!; eauto.
            apply match_curr_insert_hd; split; eauto.
        ** eauto.
        ** rewrite //=. intros Hsynced.
           split; last first.
           { right. eauto. }
           apply all_synced_insert_synced; auto.
      (* SizeOp *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H; monad_inv; clear H.
        do 4 eexists; split_and!; eauto.
         econstructor; eauto; repeat (econstructor; eauto).
         do 2 f_equal.
         symmetry. erewrite state_match_curr_disk_size; eauto.
      (* BarrierOp *)
      * rewrite /base_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H; monad_inv; clear H.
        destruct (decide (ADP.all_synced _)).
        **  monad_inv.
            destruct (decide (ADP.all_synced (world pσ1'))).
            *** do 4 eexists. split_and!.
                { repeat econstructor. rewrite decide_True //=. }
                { eauto. }
                { eauto. }
                intros; split; eauto.
            *** do 4 eexists. split_and!.
                { repeat econstructor. rewrite decide_False //=. }
                { eauto. }
                { eauto. }
                intros; intuition.
        **  monad_inv.
            destruct (decide (ADP.all_synced (world pσ1'))).
            *** do 4 eexists. split_and!.
                { repeat econstructor. rewrite decide_True //=. }
                { eauto. }
                { eauto. }
                intros; split; eauto.
            *** do 4 eexists. split_and!.
                { repeat econstructor. rewrite decide_False //=. }
                { eauto. }
                { eauto. }
                intros; intuition.
    - (* NewProph *)
      rewrite /base_step//= in Hstep.
      monad_inv; destruct_head.
      inversion H; monad_inv; clear H.
      inversion H0; monad_inv; clear H0.
      simpl in H2; inversion H2; monad_inv; clear H2.
      eexists _, _, {| used_proph_id := _ |}, _.
      inversion Hmatch_curr. intuition.
        ** repeat (econstructor; eauto). rewrite H4.
           rewrite /RecordSet.set/= H13. done.
        ** split_and!; eauto.
        ** rewrite //=.
    - (* ResolveProph *)
      rewrite /base_step//= in Hstep.
      monad_inv; destruct_head.
      do 4 eexists. inversion Hmatch_curr. intuition.
      + repeat (econstructor; eauto).
      + split_and!; eauto.
      + done.
  Qed.

  Theorem prim_step'_compat_simulation e1 pσ1 pg1 pσ1' pg1' pσ2 pg2 κ e2 efs :
    prim_step' e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
    state_match_curr pσ1 pσ1' →
    pg1 = pg1' →
    (∃ e2' pσ2' pg2' efs',
        prim_step' e1 pσ1' pg1' κ e2' pσ2' pg2' efs' ∧
        state_match_curr pσ2 pσ2' ∧
        pg2 = pg2' ∧
        (ADP.all_synced (world pσ1') →
           ADP.all_synced (world pσ2') ∧
           ((e2 = e1 ∧ efs = [] ∧ pσ2 = pσ1 ∧ pg2 = pg1) ∨
            (e2 = e2' ∧ efs = efs')))).
  Proof.
    intros Hprim Hc <-.
    inversion Hprim; subst.
    intros. edestruct (base_step_compat_simulation) as (e2_s'&pσ2'&pg2'&efs'&Hstep'&Hcurr&Hg&Hifsynced); eauto.
    do 4 eexists; split_and!.
    { econstructor; eauto. }
    { eauto. }
    { eauto. }
    intros Hsynced.
    apply Hifsynced in Hsynced as (?&Hcases). split; auto.
    destruct Hcases as [Hcases1|Hcases2].
    - left. intuition congruence.
    - right. intuition congruence.
  Qed.

  Theorem prim_step'_compat_rtc_simulation e1 pσ1 pg1 (pσ1' : pstate) pg1' pσ2 pg2 σ1 g1 e2 :
    ADP.all_synced (world pσ1') →
    rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' [])
        (e1, (pσ1, pg1)) (e2, (pσ2, pg2)) →
    state_compat σ1 pσ1 →
    global_compat g1 pg1 →
    state_compat σ1 pσ1' →
    global_compat g1 pg1' →
    ∃ pσ2' pg2',
      rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' [])
          (e1, (pσ1', pg1')) (e2, (pσ2', pg2')) ∧
       (∀ σ2, state_compat σ2 pσ2 → state_compat σ2 pσ2') ∧
       (∀ g2, global_compat g2 pg2 → global_compat g2 pg2').
  Proof.
    intros Hsynced.
    remember (e1, (pσ1, pg1)) as pρ1 eqn:Heqρ1.
    remember (e2, (pσ2, pg2)) as pρ2 eqn:Heqρ2.
    intros Hrtc.
    revert e1 σ1 g1 pσ1 pg1 pσ1' pg1' Heqρ1 Hsynced.
    revert e2 pσ2 pg2 Heqρ2.
    induction Hrtc; intros; subst.
    - inversion Heqρ1; subst. do 2 eexists; split_and!.
      * apply rtc_refl.
      * eapply all_synced_compat_full; eauto.
      * destruct (global_compat_match_eq _ _ _ H0 H2). auto.
    - destruct y as (emid&pσmid&pgmid).
      edestruct (prim_step'_compat_simulation) as (e2'&pσ2'&pg2'&efs'&Hstep&Hmatch_curr&Hpg&Hifsynced); eauto.
      { eapply state_compat_state_match_curr; eauto. }
      generalize Hsynced as Hsynced' => Hsynced'.
      apply Hifsynced in Hsynced'. destruct Hsynced' as (Hsynced'&Hcases).
      destruct Hcases as [Hloop|Hprogress].
      { destruct Hloop as (->&[]&->&->).
        eapply IHHrtc.
        { reflexivity. }
        { reflexivity. }
        { auto. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
      }
      {
      assert (∃ σ1' g1', state_compat σ1' pσmid ∧
                         state_compat σ1' pσ2' ∧
                         global_compat g1' pgmid ∧
                         global_compat g1' pg2') as (σ1'&g1'&?&?&?&?).
      { edestruct (compat_inhabited_rev pσmid pgmid) as (σ1'&g1'&?&?).
        do 2 eexists; split_and!; eauto.
        { eapply all_synced_match_curr_compat_full; eauto. }
        subst pgmid. done.
      }
      edestruct IHHrtc as (pσ2_IH&pg2_IH&Hrtc_IH&Hcompat_IH&Hcompatg_IH); try eapply Hrtc.
      { reflexivity. }
      { reflexivity. }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      { do 2 eexists; split.
        { econstructor; eauto. simpl. destruct Hprogress as (->&<-).
          destruct (global_compat_match_eq _ _ _ H1 H3).
          eauto. }
        eauto. } }
  Qed.

  Theorem base_step_compat_reducible e1 pσ1 pg1 pσ1' pg1' pσ2 pg2 σ1 g1 κ e2 efs :
    base_step e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
    state_compat σ1 pσ1 →
    global_compat g1 pg1 →
    state_compat σ1 pσ1' →
    global_compat g1 pg1' →
    (∃ κ e2' pσ2' pg2' efs', base_step e1 pσ1' pg1' κ e2' pσ2' pg2' efs').
  Proof.
    intros.  edestruct base_step_compat_simulation as (?&?&?&?&?&?&?&?); eauto.
    { eapply state_compat_state_match_curr; eauto. }
    destruct (global_compat_match_eq _ _ _ H1 H3).
    subst. eauto 10.
  Qed.

  Lemma stuck'_transport_rev e σ g pσ pg:
    stuck' e pσ pg →
    state_compat σ pσ →
    global_compat g pg →
    stuck' e σ g.
  Proof.
    rewrite /stuck'/irreducible'. intros Hstuck Hcompat Hgcompat.
    destruct Hstuck as (Hnval&Hirred).
    split; auto.
    intros κ e' σ' g' efs Hprim.
    edestruct (compat_inhabited σ' g') as (pσ'&pg'&?&?).
    edestruct prim_step'_simulation as (pσ1'&pg1'&?&?&Hstep); eauto.
    inversion Hstep as [ ????? Hstep'].
    eapply (base_step_compat_reducible _ _ _ pσ pg) in Hstep'; eauto.
    destruct Hstep' as (?&?&?&?&?&?). subst.
    eapply Hirred.
    econstructor; eauto.
  Qed.

  Lemma stuck'_transport e σ g pσ pg:
    stuck' e σ g →
    state_compat σ pσ →
    global_compat g pg →
    stuck' e pσ pg.
  Proof.
    rewrite /stuck'/irreducible'. intros Hstuck Hcompat Hgcompat.
    destruct Hstuck as (Hnval&Hirred).
    split; auto.
    intros κ e' σ' g' efs Hprim.
    edestruct prim_step'_simulation_rev as (pσ1'&pg1'&?&?&Hstep); eauto.
    eapply Hirred.
    eauto.
  Qed.

  Lemma prim_step'_safe_transport e σ1 g1 pσ1 pg1:
    prim_step'_safe e σ1 g1 →
    state_compat σ1 pσ1 →
    global_compat g1 pg1 →
    prim_step'_safe e pσ1 pg1.
  Proof.
    rewrite /prim_step'_safe. intros Hsafe Hcompat Hgcompat.
    intros e' pσ2 pg2 Hrtc.
    eapply prim_step'_rtc_simulation_rev in Hrtc; eauto.
    destruct Hrtc as (σ2&g2&Hrtc&Hcases).
    destruct Hcases as (Hcompat2&Hgcompat2).
    intros Hnstuck.
    eapply stuck'_transport_rev in Hnstuck; eauto.
    eapply Hsafe; last eassumption. eauto.
  Qed.

  Theorem base_step_atomic_simulation e1 σ1 g1 κ e2 σ2 g2 efs :
    base_step_atomic e1 σ1 g1 κ e2 σ2 g2 efs →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        base_step_atomic e1 pσ1 pg1 κ e2 pσ2 pg2 efs.
  Proof.
    intros Hprim.
    inversion Hprim; subst.
    - intros.
      edestruct (base_step_simulation) as (?&?&?&?); eauto.
      do 2 eexists. split_and!; intuition eauto.
      econstructor; eauto.
    - intros.
      edestruct (rtc_prim_step'_simulation) as (?&?&?&?); eauto.
      do 2 eexists. split_and!; intuition eauto.
      apply base_step_atomically; eauto.
      { eapply prim_step'_safe_transport; eauto. }
    - intros. do 2 eexists. split_and!; eauto.
      eapply base_step_atomically_fail.
      { eapply prim_step'_safe_transport; eauto. }
  Qed.

  Lemma prim_step'_safe_transport_rev e σ1 g1 (pσ1 : pstate) pg1:
    ADP.all_synced (world pσ1) →
    prim_step'_safe e pσ1 pg1 →
    state_compat σ1 pσ1 →
    global_compat g1 pg1 →
    prim_step'_safe e σ1 g1.
  Proof.
    rewrite /prim_step'_safe. intros Hsynced Hsafe Hcompat Hgcompat.
    intros e' σ2 g2 Hrtc.
    destruct (compat_inhabited σ2 g2) as (pσ2'&pg2'&?&?).
    edestruct rtc_prim_step'_simulation as (pσ1'&pg1'&Hcompat1'&Hgcompat1'&Hrtc'); eauto.
    assert (∃ pσ2 pg2,  state_compat σ2 pσ2 ∧ global_compat g2 pg2 ∧
                    rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' [])
                        (e, (pσ1, pg1)) (e', (pσ2, pg2))) as (pσ2&pg2&?&?&Hstep).
    {
      edestruct (prim_step'_compat_rtc_simulation) as (pσ2&pg2&Hrtc''&Hcompat_impl&Hgcompat_impl); eauto.
      exists pσ2, pg2. split; first by eauto. split; first by eauto.
      destruct (global_compat_match_eq _ _ _ Hgcompat Hgcompat1'). eauto.
    }
    eapply Hsafe in Hstep as Hnstuck.
    intros Hstuck. apply Hnstuck.
    eapply stuck'_transport in Hstuck; eauto.
  Qed.

  Theorem base_step_atomic_simulation_rev e1 (pσ1 : pstate) pg1 κ pσ2 pg2 efs σ1 g1 e2 :
    ADP.all_synced (world pσ1) →
    base_step_atomic e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
    state_compat σ1 pσ1 →
    global_compat g1 pg1 →
    ∃ σ2 g2 e2',
      base_step_atomic e1 σ1 g1 κ e2' σ2 g2 efs ∧
      ((e2 = e1 ∧ efs = [] ∧ pσ2 = pσ1 ∧ pg2 = pg1) ∨
       (e2 = e2' ∧ state_compat σ2 pσ2 ∧ global_compat g2 pg2)).
  Proof.
    intros Hsynced Hprim.
    inversion Hprim; subst.
    - intros.
      edestruct (base_step_simulation_rev) as (?&?&?&?&Hcases); eauto.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto.
    - intros.
      edestruct (prim_step'_rtc_simulation_rev) as (?&?&?&?); eauto.
      do 3 eexists. split_and!; intuition eauto.
      apply base_step_atomically; eauto.
      { eapply prim_step'_safe_transport_rev; eauto. }
    - intros. do 3 eexists. split_and!; eauto.
      eapply base_step_atomically_fail.
      { eapply prim_step'_safe_transport_rev; eauto. }
  Qed.

  Theorem prim_step_simulation e1 σ1 g1 κ e2 σ2 g2 efs :
    prim_step e1 σ1 g1 κ e2 σ2 g2 efs →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        @prim_step (@goose_lang _ _ ADP.disk_semantics) e1 pσ1 pg1 κ e2 pσ2 pg2 efs.
  Proof.
    intros Hprim.
    inversion Hprim. simpl in *.
    intros. edestruct (base_step_atomic_simulation) as (?&?&?&?); eauto.
    do 2 eexists; split_and!; intuition eauto.
    econstructor; eauto.
  Qed.

  Theorem step_simulation t1 σ1 g1 κ t2 σ2 g2:
    step (t1, (σ1, g1)) κ (t2, (σ2, g2)) →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        @step (@goose_lang _ _ ADP.disk_semantics) (t1, (pσ1, pg1)) κ (t2, (pσ2, pg2)).
  Proof.
    intros Hstep.
    inversion Hstep. simpl in *.
    monad_inv. intros. edestruct (prim_step_simulation) as (?&?&?&?); eauto.
    do 2 eexists; split_and!; intuition eauto.
    econstructor; eauto.
  Qed.

  Theorem erased_step_simulation t1 σ1 g1 t2 σ2 g2:
    erased_step (t1, (σ1, g1)) (t2, (σ2, g2)) →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        @erased_step (@goose_lang _ _ ADP.disk_semantics) (t1, (pσ1, pg1)) (t2, (pσ2, pg2)).
  Proof.
    intros Hstep.
    inversion Hstep. simpl in *.
    intros. edestruct (step_simulation) as (?&?&?&?); eauto.
    do 2 eexists; split_and!; intuition eauto.
    econstructor; eauto.
  Qed.

  Theorem rtc_erased_step_simulation t1 σ1 g1 t2 σ2 g2:
    rtc erased_step (t1, (σ1, g1)) (t2, (σ2, g2)) →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        rtc (@erased_step (@goose_lang _ _ ADP.disk_semantics)) (t1, (pσ1, pg1)) (t2, (pσ2, pg2)).
  Proof.
    remember (t1, (σ1, g1)) as ρ1 eqn:Heqρ1.
    remember (t2, (σ2, g2)) as ρ2 eqn:Heqρ2.
    intros Hrtc.
    revert t1 σ1 g1 Heqρ1.
    revert t2 σ2 g2 Heqρ2.
    induction Hrtc; intros; subst.
    - inversion Heqρ1; subst. do 2 eexists; split_and!; eauto.
      apply rtc_refl.
    - destruct y as (e1'&σ1'&g1').
      edestruct (IHHrtc) as (pσ1'&pg1'&Hcompat1&Hcompat2&Hrtc'); eauto.
      edestruct erased_step_simulation as (pσ1&pg1&Hcompat1_0&Hcompat2_0&Hstep); eauto.
      do 2 eexists; split_and!; eauto.
      econstructor; eauto.
  Qed.

  Lemma disk_compat_crash_inv d1 d2 pd2:
    @ffi_crash_step _ _ (AD.disk_semantics) d1 d2 →
    disk_compat d2 pd2 →
    ∃ pd1, @ffi_crash_step _ _ (ADP.disk_semantics) pd1 pd2 ∧
           disk_compat d1 pd1.
  Proof.
    revert d2 pd2.
    induction (d1 : gmap Z _) as [| ???? IH] using map_ind.
    - intros d2 pd2. intros Hcrash Hcompat.
      assert (pd2 = ∅) as ->.
      { inversion Hcrash. destruct Hcompat as (Hdom&_).
        apply (dom_empty_inv_L (D := gset _) pd2).
        { rewrite dom_empty_L in H. destruct H. rewrite H. rewrite Hdom //. }
      }
      exists ∅. split.
      * econstructor; split; eauto. set_solver.
      * split; rewrite ?dom_empty_L //.
    - intros d2 pd2 Hcrash.
      inversion Hcrash. subst.
      assert (@ffi_crash_step _ _ (AD.disk_semantics) m (delete i d2)).
      {
        econstructor; split.
        * rewrite dom_delete_L. destruct H0. rewrite dom_insert_L in H0.
          assert (i ∉ dom m).
          { apply not_elem_of_dom. eauto. }
          set_solver.
        * intros addr ab Hdel.
          destruct H0 as (_&Hlookup).
          apply (lookup_delete_Some d2) in Hdel.
          edestruct Hlookup.
          { intuition eauto. }
          eexists; split; intuition eauto.
          rewrite /AD.is_possible in H4 *.
          destruct H4 as (ab'&Hlookup'&Hin).
          rewrite lookup_insert_ne in Hlookup'; eauto.
      }
      intros Hcompat.
      assert (disk_compat (delete i d2) (delete i pd2)).
      {
        split.
        - rewrite ?dom_delete_L. destruct Hcompat as (Heq&_); eauto.
          rewrite Heq //.
        - intros addr ab Hdel.
          destruct Hcompat as (_&Hlook). edestruct Hlook as (b'&Hin&Hlook').
          { apply (lookup_delete_Some d2) in Hdel.
            intuition eauto. }
          exists b'. split; eauto.
          rewrite lookup_delete_ne //.
          intros Heq. rewrite Heq lookup_delete_eq in Hdel. congruence.
      }
      edestruct IH as (pd1&Hcrash'&Hcompat'); eauto.
      destruct Hcompat as (Hdom&Hlook).
      destruct H0 as (Hdom'&?).
      assert (is_Some (d2 !! i)) as (ab&?).
      { apply (elem_of_dom (D := gset Z) d2).
        rewrite dom_insert_L in Hdom'. rewrite -Hdom'; set_solver. }
      edestruct (Hlook) as (cb&?&?); eauto.
      exists (<[i := {| ADP.curr_val := log_heap.latest x; ADP.crash_val := cb |}]> pd1).
      split.
      { econstructor; split.
        * rewrite dom_insert_L. inversion Hcrash'. destruct H6 as (Heqdom&_).
          rewrite Heqdom. rewrite dom_delete_L. apply (elem_of_dom_2 (D := gset _) pd2) in H5.
          rewrite -union_difference_singleton_L //.
        * intros. destruct (decide (addr = i)).
          ** subst. rewrite lookup_insert_eq in H6. inversion H6.
             rewrite //=. rewrite H5 => //=.
             edestruct H0; eauto. destruct H7 as (->&?). rewrite //=.
             rewrite /log_heap.possible/log_heap.sync//= in H4.
             apply list_elem_of_singleton in H4. subst. eauto.
          **  rewrite lookup_insert_ne // in H6.
              inversion Hcrash'. subst. destruct H7 as (_&Hlookup).
              eapply Hlookup in H6. rewrite lookup_delete_ne in H6; eauto.
      }
      {
        split.
        * rewrite ?dom_insert_L. destruct Hcompat' as (Hdomeq&_). rewrite Hdomeq; eauto.
        * intros. destruct (decide (addr = i)).
          ** subst. rewrite lookup_insert_eq in H6. inversion H6; subst.
             rewrite lookup_insert_eq. exists cb; split; eauto.
             inversion Hcrash. subst. destruct H7 as (?&Hlook_crash).
             edestruct (Hlook_crash) as (b&?&His_possible); eauto.
             subst. rewrite /AD.is_possible in His_possible.
             edestruct His_possible as (?&?&?Hin).
             rewrite lookup_insert_eq in H8. inversion H8; subst.
             rewrite /log_heap.possible/log_heap.sync//= in H4.
             apply list_elem_of_singleton in H4; subst. eauto.
          ** rewrite lookup_insert_ne //.
             destruct Hcompat' as (?&Hlook_compat).
             rewrite lookup_insert_ne // in H6.
             edestruct Hlook_compat; eauto.
      }
  Qed.

  Theorem crash_step_simulation σ1 σ2:
    crash_prim_step (goose_crash_lang)  σ1 σ2 →
    ∀ pσ2,
      state_compat σ2 pσ2 →
      ∃ pσ1,
        state_compat σ1 pσ1 ∧
        crash_prim_step (goose_crash_lang) pσ1 pσ2.
  Proof.
    inversion 1; subst.
    inversion H1; subst.
    intros pσ2 Hcompat.
    destruct Hcompat as (?&?&?&?&?).
    simpl in *.
    edestruct (disk_compat_crash_inv) as (pd1&?&?); eauto.
    exists ({| trace := trace σ1;
         heap := heap σ1;
         oracle := oracle σ1;
         world := pd1;
         globals := globals σ1
       |}).
    split.
    { split_and!; eauto. }
    { destruct pσ2; simpl in *; subst. econstructor; eauto. }
  Qed.

  Definition config_compat (ρ : cfg _) (dρ : cfg _) :=
    state_compat (ρ.2.1) (dρ.2.1) ∧
    global_compat (ρ.2.2) (dρ.2.2) ∧
    ρ.1 = dρ.1.

  Lemma config_compat_inhabited_all_synced ρ :
    ∃ dρ, config_compat ρ dρ ∧ (ADP.all_synced (world (dρ.2.1))).
  Proof.
    edestruct (compat_inhabited_all_synced (ρ.2.1) (ρ.2.2)) as (dσ&dg&?&?&?).
    eexists (_, (_, _)).
    split => //=; auto.
    split_and!; eauto.
    destruct ρ => //=.
  Qed.

  Lemma stable_disk_config_compat_unique ρ pρ :
    stable_disk (world (ρ.2.1)) →
    config_compat ρ pρ →
    (world (pρ.2.1) = d_to_pd (world (ρ.2.1))).
  Proof.
    intros Hstable ((?&?)&?&?).
    eapply stable_disk_compat_unique; eauto.
    intuition eauto.
  Qed.

  Lemma erased_rsteps_simulation r ρ1 ρ2 s :
    erased_rsteps (CS := @goose_crash_lang _ _ AD.disk_semantics) r ρ1 ρ2 s →
    ∀ dρ2,
      config_compat ρ2 dρ2 →
      ∃ dρ1, config_compat ρ1 dρ1 ∧
             erased_rsteps (CS := @goose_crash_lang _ _ ADP.disk_semantics) r dρ1 dρ2 s.
  Proof.
    induction 1 as [ρ1 ρ2 Hrtc|ρ1 ρ2 ρ3 σ s Hrtc Hcrash Herased].
    - intros dρ2 Hcompat.
      destruct ρ1 as (t1, (σ1, g1)).
      destruct ρ2 as (t2, (σ2, g2)).
      destruct dρ2 as (dt2, (dσ2, [])).
      destruct Hcompat as (?&?&Heq).
      edestruct (rtc_erased_step_simulation) as (dσ1&dg1&Hcompats&?&Hrtc'); eauto.
      exists (t1, (dσ1, dg1)); eauto.
      simpl in Heq. subst.
      split; eauto.
      * split_and!; eauto.
      * econstructor; eauto.
    - intros dρ3 Hcompat.
      edestruct IHHerased as (dρ2&Hcompat'&Hrtc'); eauto.
      destruct Hcompat' as (?&?&Heq).
      simpl in Heq.
      edestruct (crash_step_simulation) as (dσ2'&?&?); eauto.
      destruct ρ1 as (t1, (σ1, g1)).
      destruct ρ2 as (t2, (σ2, g2)).
      destruct ρ3 as (t3, (σ3, g3)).
      destruct dρ2 as (dt2, (dσ2, [])).
      destruct dρ3 as (dt3, (dσ3, [])).
      edestruct (rtc_erased_step_simulation) as (dp1&dg1&Hcompat1&Hgcompat&Hrtc1); try eapply Hrtc; eauto.
      exists (t1, (dp1, dg1)).
      split.
      { split_and!; eauto. }
      econstructor; eauto => //=. simpl in Heq. subst.
      eauto.
  Qed.

  Definition dstate_to_pstate (σ : dstate) : pstate :=
    {| heap := heap σ;
       world := (d_to_pd (world σ) : (@ffi_state ADP.disk_model));
       trace := trace σ;
       oracle := oracle σ;
       globals := globals σ;
    |}.
  Definition dglobal_to_pglobal (g : dglobal) : pglobal :=
    {| used_proph_id := g.(used_proph_id);
       global_world := (global_world g : @ffi_global_state ADP.disk_model) |}.

  Lemma stable_disk_config_compat_unique_init e σ g ρ1 :
    stable_disk (world σ) →
    config_compat ([e], (σ, g)) ρ1 →
    ρ1 = ([e], (dstate_to_pstate σ, dglobal_to_pglobal g)).
  Proof.
    intros Hstable. destruct ρ1 as (?&(?&?)).
    destruct 1 as ((Hheap&Hdisk&Htrace&Horacle&Hglobals)&(Hproph&[])&Htp).
    simpl in Htp; inversion Htp; subst.
    do 2 f_equal.
    - rewrite /dstate_to_pstate.
      destruct σ; destruct s.
      simpl in Horacle, Htrace, Hdisk, Hheap.
      f_equal; eauto.
      eapply stable_disk_compat_unique in Hstable; eauto.
    - destruct g, g0. rewrite /dglobal_to_pglobal /=.
      simpl in Hproph. f_equal; eauto.
      destruct global_world1, global_world0. done.
  Qed.

  Lemma recv_adequate_transport s e r (σ : dstate) (g : dglobal) φ φr:
    stable_disk (world σ) →
    recovery_adequacy.recv_adequate (CS := goose_crash_lang) s e r (dstate_to_pstate σ) (dglobal_to_pglobal g)
                                    (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, True) →
    recovery_adequacy.recv_adequate (CS := @goose_crash_lang _ AD.disk_model _) s e r σ g
                                    (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, True).
  Proof.
    intros Hstable [Hnormal Hcrashed Hnstuck _].
    split; last done.
    - intros t2 σ2 g2 v2 Hsteps.
      edestruct (config_compat_inhabited_all_synced (of_val v2 :: t2, (σ2, g2)))
                as (ρ2&Hcompat&Hsynced).
      edestruct erased_rsteps_simulation as (ρ1&Hcompat1&Hpsteps); eauto.
      eapply stable_disk_config_compat_unique_init in Hcompat1; auto. subst.
      destruct ρ2 as (?&?&?).
      destruct Hcompat as (?&?&Heq).
      eapply (Hnormal t2 _ _ v2).
      simpl in Heq. rewrite Heq. eauto.
    - intros t2 σ2 g2 v2 Hsteps.
      edestruct (config_compat_inhabited_all_synced (of_val v2 :: t2, (σ2, g2)))
                as (ρ2&Hcompat&Hsynced).
      edestruct erased_rsteps_simulation as (ρ1&Hcompat1&Hpsteps); eauto.
      eapply stable_disk_config_compat_unique_init in Hcompat1; auto. subst.
      destruct ρ2 as (?&?&?).
      destruct Hcompat as (?&?&Heq).
      eapply (Hcrashed t2 _ _ v2).
      simpl in Heq. rewrite Heq. eauto.
    - intros t2 σ2 g2 e2 st -> Hsteps Hin.
      edestruct (config_compat_inhabited_all_synced (t2, (σ2, g2)))
                as (ρ2&Hcompat&Hsynced).
      edestruct erased_rsteps_simulation as (ρ1&Hcompat1&Hpsteps); eauto.
      eapply stable_disk_config_compat_unique_init in Hcompat1; auto. subst.
      destruct ρ2 as (?&?&?).
      destruct Hcompat as (?&?&Heq).
      edestruct (Hnstuck t2) as [Hval|Hred]; eauto.
      { simpl in Heq. rewrite Heq. eauto. }
      right. destruct Hred as (?&?&?&?&?&Hprim_step).
      inversion Hprim_step; subst. simpl in *.
      edestruct (base_step_atomic_simulation_rev) as (?&?&?&?&?); eauto.
      econstructor. do 4 eexists. econstructor; eauto.
  Qed.

End translate.

(*
Print Assumptions recv_adequate_transport.
*)
