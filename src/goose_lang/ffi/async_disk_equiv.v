From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang.ffi Require async_disk.
From Perennial.goose_lang.ffi Require async_disk_proph.


Module ADP := async_disk_proph.
Module AD := async_disk.

Section translate.
  Notation pstate := (@state async_disk_syntax.disk_op ADP.disk_model).
  Notation pglobal := (@global_state ADP.disk_model).
  Notation dstate := (@state async_disk_syntax.disk_op AD.disk_model).
  Notation dglobal := (@global_state AD.disk_model).

  Definition disk_compat (dd : @ffi_state AD.disk_model) (ad: @ffi_state ADP.disk_model) :=
    dom (gset _) dd = dom (gset _) ad ∧
    (∀ addr ab, dd !! addr = Some ab →
     ∃ bd, bd ∈ log_heap.possible ab ∧
           ad !! addr = Some ({| ADP.curr_val := log_heap.latest ab;
                                 ADP.crash_val := bd |})).

  Definition state_compat (dσ : state) (pσ : pstate) :=
    heap dσ = heap pσ ∧
    disk_compat (world dσ) (world pσ) ∧
    trace dσ = trace pσ ∧
    oracle dσ = oracle pσ.

  Definition global_compat (dg : dglobal) (pg : pglobal) := dg = pg.

  Ltac inv_head_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : head_step ?e _ _ _ _ _ _ _ |- _ =>
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
    world σ !! int.Z n = Some ab →
    state_compat (RecordSet.set world <[int.Z n:=log_heap.async_put bnew ab]> σ) pσ →
    ∃ cb, world pσ !! int.Z n = Some cb ∧
          ((cb = {| ADP.curr_val := bnew; ADP.crash_val := bnew |} ∧
            state_compat σ (RecordSet.set world <[int.Z n:= {| ADP.curr_val := log_heap.latest ab;
                                                               ADP.crash_val := log_heap.latest ab|}]>
                            pσ)) ∨
           (ADP.crash_val cb ≠ bnew ∧
            state_compat σ (RecordSet.set world <[int.Z n:= {| ADP.curr_val := log_heap.latest ab;
                                                               ADP.crash_val := ADP.crash_val cb |}]>
                            pσ))).
  Proof.
    intros Hlookup Hcompat.
    destruct Hcompat as (Hheap&Hdisk&?&?).
    destruct Hdisk as (Hdom&Hvals).
    destruct (world pσ !! int.Z n) as [cb|] eqn:Heqp; last first.
    { exfalso. revert Heqp. rewrite -not_elem_of_dom.
      move: Hdom. rewrite /RecordSet.set//=. rewrite dom_insert_L. set_solver. }
    exists cb. split; first done.
    assert (ADP.curr_val cb = bnew).
    { edestruct Hvals as (b'&Hposs&Hlookup2); eauto.
      { rewrite /RecordSet.set//=. apply: lookup_insert. }
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
        destruct (decide (addr = int.Z n)).
        { subst. assert (ab' = ab) by congruence; subst.
          exists (log_heap.latest ab); split.
          * rewrite /log_heap.possible. apply elem_of_app; right. econstructor.
          * rewrite lookup_insert //=.
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
        destruct (decide (addr = int.Z n)).
        { subst. assert (ab' = ab) by congruence; subst.
          exists (ADP.crash_val cb); split.
          * edestruct (Hvals) as (b'&Hin&Hlook'); eauto.
            { rewrite /RecordSet.set//=. apply lookup_insert. }
            rewrite Heqp in Hlook'. inversion Hlook' as [Heq'].
            rewrite //=. move:Hin. rewrite /log_heap.possible //= ?elem_of_app.
            intros [Hin1|Hin2]; eauto.
            apply elem_of_list_singleton in Hin2. exfalso. subst.
            clear -Heq' Hneq. destruct cb. simpl in *; congruence.
          * rewrite lookup_insert //=.
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

  Lemma state_compat_post_flush_inv σ1 pσ2 :
    state_compat (RecordSet.set world AD.flush_disk σ1) pσ2 →
    state_compat σ1 pσ2 ∧ ADP.all_synced (world pσ2).
  Proof.
    rewrite /RecordSet.set //=.
    intros (Hheap&Hdisk&Htrace&Horacle).
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

  Theorem head_step_simulation e1 σ1 g1 κ e2 σ2 g2 efs :
    head_step e1 σ1 g1 κ e2 σ2 g2 efs →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1 pg2,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        head_step e1 pσ1 pg1 κ e2 pσ2 pg2 efs.
  Proof.
    rewrite /head_step.
    revert σ1 g1 κ e2 σ2 g2 efs.
    destruct e1; intros σ1 g1 κ e2 σ2 g2 efs Hstep; subst; try inversion Hstep; intuition eauto; subst.
    - monad_inv. do 3 eexists. split_and!; eauto.
      repeat econstructor.
    - rewrite /head_step//= in Hstep.
      destruct_head. inversion Hstep; subst.
      monad_inv. do 3 eexists. split_and!; eauto.
      repeat econstructor.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      destruct (un_op_eval op v) eqn:Heq; eauto; subst.
      * inversion Hstep; monad_inv.
        do 3 eexists. split_and!; eauto.
        econstructor; rewrite ?Heq; eauto; econstructor; eauto.
      * simpl in Hstep. inversion Hstep; subst. inv_monad_false.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      destruct (bin_op_eval op v) eqn:Heq; eauto; subst.
      * inversion Hstep; monad_inv.
        do 3 eexists. split_and!; eauto.
        econstructor; rewrite ?Heq; eauto; econstructor; eauto.
      * simpl in Hstep. inversion Hstep; subst. inv_monad_false.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct e1_1; monad_inv.
      destruct e1_2; monad_inv.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
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
    - rewrite /head_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv. inversion H1. subst. monad_inv.
      inversion H2; subst.
      do 3 eexists. split_and!; eauto.
      econstructor; eauto; repeat econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        inversion H2; monad_inv; subst; clear H2.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        inversion H3; monad_inv; subst; clear H3.
        destruct (heap σ1 !! l) eqn:Heq; subst.
        ** inversion H7; monad_inv; subst.
           inversion H.
           intuition.
           exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                      world := world pσ2 |}).
           do 2 eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite Heq. econstructor; eauto. }
               rewrite //=. repeat econstructor; eauto. f_equal.
               f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               congruence.
        ** inversion H7; intuition.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        inversion H2; monad_inv; subst; clear H2.
        destruct x0. destruct n; monad_inv.
        inversion H3; monad_inv; subst; clear H3.
        destruct (heap σ1 !! l) eqn:Heq; subst.
        ** inversion H7; monad_inv; subst.
           inversion H.
           intuition.
           exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                      world := world pσ2 |}).
           do 2 eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite Heq. econstructor; eauto. }
               rewrite //=. repeat econstructor; eauto. f_equal.
               f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               congruence.
        ** inversion H7; intuition.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        inversion H2; monad_inv; subst; clear H2.
        destruct x0. destruct n; monad_inv.
        destruct n; monad_inv.
        inversion H3; monad_inv; subst; clear H3.
        destruct (heap σ1 !! l) eqn:Heq; subst.
        ** inversion H7; monad_inv; subst.
           inversion H.
           intuition.
           exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                      world := world pσ2 |}).
           do 2 eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto.
               { rewrite //=. rewrite Heq. econstructor; eauto. }
               rewrite //=. repeat econstructor; eauto. f_equal.
               f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               congruence.
        ** inversion H7; intuition.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        inversion H2; monad_inv; subst; clear H2.
        destruct x0. destruct n; monad_inv.
        destruct (heap σ1 !! l) eqn:Heq; subst.
        ** inversion H7; monad_inv; subst.
           inversion H.
           intuition.
           do 3 eexists. split_and!; eauto.
           repeat econstructor; rewrite -?H1 ?Heq; eauto; repeat econstructor.
        ** inversion H7; intuition.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        inversion H3; monad_inv; subst; clear H3.
        inversion H; intuition.
           exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                      world := world pσ2 |}).
           do 2 eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto => //=.
               f_equal. f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               congruence.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1.
        inversion H; intuition.
           exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                      world := world pσ2 |}).
           do 2 eexists.
           split_and!.
           *** simpl in *. split_and!; eauto.
           *** eauto.
           *** econstructor; eauto; repeat econstructor; eauto => //=.
               f_equal. f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /RecordSet.set //=.
               congruence.
    - rewrite /head_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1. subst.
        inversion H3; monad_inv; subst; clear H3.
        inversion H4; monad_inv; subst; clear H4.
        destruct s0 as (?&[]).
        destruct (decide (0 < int.Z n)); monad_inv.
        monad_inv. inversion H1.
        exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                   world := world pσ2 |}).
        subst. do 2 eexists. inversion H. intuition.
        ** simpl in *. split_and!; eauto.
        ** eauto.
        ** econstructor.
           *** inversion H6; econstructor; eauto; repeat (econstructor; eauto).
               { unfold check. rewrite ifThenElse_if; eauto. rewrite /=. econstructor. rewrite //=. }
               { eapply H5. }
               { rewrite //=. eapply H5. }
           *** repeat econstructor => //=.
               f_equal. f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
               f_equal; eauto.
      * inversion Hstep; monad_inv.
        inversion H1; monad_inv; clear H1. subst.
        inversion H3; monad_inv; subst; clear H3.
        destruct (decide (is_Writing (heap σ1 !! l))); monad_inv.
        inversion H2; monad_inv; subst; clear H2.
        exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                   world := world pσ2 |}).
        subst. do 2 eexists. inversion H. intuition.
        ** simpl in *. split_and!; eauto.
        ** eauto.
        ** econstructor.
           *** econstructor; eauto; repeat (econstructor; eauto).
               { unfold check. rewrite ifThenElse_if; eauto. rewrite /=. econstructor. rewrite //=. }
           *** repeat econstructor => //=.
               f_equal. f_equal. destruct pσ2; subst.
               simpl in * => //=. rewrite /state_init_heap/state_insert_list. rewrite /RecordSet.set //=.
               f_equal; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      inversion Hstep; monad_inv.
      inversion H1; monad_inv; clear H1. subst.
      inversion H2; monad_inv; subst; clear H2.
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
                 world := world pσ2 |}).
      subst. do 2 eexists. inversion H. intuition.
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
      subst. do 3 eexists. inversion H. intuition.
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
      * rewrite /head_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H1; monad_inv; clear H1. subst.
        inversion H2; monad_inv; subst; clear H2.
        inversion H3; monad_inv; subst; clear H3.
        destruct_head.
        destruct (world σ1 !! int.Z n) eqn:Heq; rewrite Heq in H4; subst; last first.
        { inv_monad_false. }
        inversion H1; monad_inv; clear H1. subst.
        inversion H2; monad_inv; subst; clear H2.
        inversion H3; monad_inv; subst; clear H3.
             exists ({| heap := heap σ1; oracle := oracle σ1; trace := trace σ1;
                        world := world pσ2 |}).
        destruct s0 as (?&[]); monad_inv.
        inversion H4; monad_inv; subst; clear H4.
        inversion H. intuition.
        destruct (world pσ2 !! int.Z n) eqn:Hlook; last first.
        { exfalso. destruct H4.
          rewrite //= in H4.
          revert Hlook. rewrite -not_elem_of_dom.  intros Hfalso.
          apply Hfalso. rewrite -H4. apply elem_of_dom. eauto.
        }
        do 2 eexists.
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
                 destruct H4. edestruct H6; eauto. destruct H8. rewrite H9 in Hlook. simpl in Hlook.
                 inversion Hlook. rewrite //=.
               }
      (* WriteOp *)
      * rewrite /head_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H1; monad_inv; clear H1. subst.
        inversion H2; monad_inv; subst; clear H2.
        inversion H3; monad_inv; subst; clear H3.
        inversion H1; monad_inv; clear H1. subst.
        inversion H2; monad_inv; subst; clear H2.
        destruct s0.
        monad_inv.
        destruct (world σ1 !! int.Z n) eqn:Heq; rewrite Heq in H4; subst; last first.
        { inv_monad_false. }

        inversion H4; monad_inv; subst; clear H4.
        edestruct (state_compat_write_inv) as (cb&Hlookupcb&Hcases); eauto.
        destruct Hcases as [(Hcbeq&Hcase1)|(Hneq&Hcase2)].
        ** do 3 eexists; split_and!; eauto; [].
           repeat econstructor => //=.
           { rewrite lookup_insert //=. }
           { rewrite //=. destruct H as (Hheap&?). rewrite -Hheap //=. }
           { rewrite //=. simpl in * => //=.
             rewrite /RecordSet.set //=.
             rewrite insert_insert //=. f_equal; eauto.
             f_equal. destruct pσ2; f_equal; eauto.
             rewrite //=. rewrite //= in Hlookupcb.
             Unshelve. 2:{exact true. }
             rewrite /ADP.cblk_upd//=.
             rewrite insert_id; eauto.
             rewrite -Hcbeq. eauto.
           }
        ** do 3 eexists; split_and!; eauto; [].
           repeat econstructor => //=.
           { rewrite lookup_insert //=. }
           { rewrite //=. destruct H as (Hheap&?). rewrite -Hheap //=. }
           { rewrite //=. simpl in * => //=.
             rewrite /RecordSet.set //=.
             rewrite insert_insert //=. f_equal; eauto.
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
             { apply: lookup_insert. }
             rewrite Hlookupcb in Hval'. inversion Hval'. rewrite //=.
           }
      (* SizeOp *)
      * rewrite /head_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H1; monad_inv; clear H1.
        do 3 eexists; split_and!; eauto.
         econstructor; eauto; repeat (econstructor; eauto).
         do 2 f_equal.
         erewrite state_compat_disk_size; eauto.
      (* BarrierOp *)
      * rewrite /head_step//= in Hstep.
        destruct_head. inversion Hstep; monad_inv.
        destruct_head.
        inversion H1; monad_inv; clear H1.
        exists pσ2.
        edestruct (state_compat_post_flush_inv); eauto.
        do 2 eexists; split_and!; eauto.
        econstructor; eauto; repeat (econstructor; eauto).
        rewrite decide_True //.
  Qed.

  Theorem prim_step'_simulation e1 σ1 g1 κ e2 σ2 g2 efs :
    prim_step' e1 σ1 g1 κ e2 σ2 g2 efs →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1 pg2,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        prim_step' e1 pσ1 pg1 κ e2 pσ2 pg2 efs.
  Proof.
    intros Hprim.
    inversion Hprim; subst.
    intros. edestruct (head_step_simulation) as (pσ1&pg1&pg2'&?&?&?); eauto.
    do 3 eexists; split_and!; eauto.
    econstructor; eauto.
  Qed.

  Theorem rtc_prim_step'_simulation e1 σ1 g1 e2 σ2 g2 :
    rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' [])
        (e1, (σ1, g1)) (e2, (σ2, g2)) →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1 pg2,
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
    - inversion Heqρ1; subst. do 3 eexists; split_and!; eauto.
      apply rtc_refl.
    - destruct y as (e1'&σ1'&g1').
      edestruct (IHHrtc) as (pσ1'&pg2_&pg1'&Hcompat1&Hcompat2&Hrtc'); eauto.
      edestruct prim_step'_simulation as (pσ1&pg1&pg0&Hcompat1_0&Hcompat2_0&Hstep); eauto.
      do 3 eexists; split_and!; eauto.
      econstructor; eauto. simpl.
      destruct pg0, pg2_; eauto.
  Qed.

  Definition head_step_barrier_looping e1 pσ1 pg1 :=
    head_reducible e1 pσ1 pg1 ∧
    (∀ κ e2 pσ2 pg2 efs,
        head_step e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
        e2 = e1 ∧ efs = [] ∧ pσ2 = pσ1 ∧ pg2 = pg1).

  Definition prim_step'_barrier_looping e1 pσ1 pg1 :=
    (∀ κ e2 pσ2 pg2 efs,
        prim_step' e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
        e2 = e1 ∧ efs = [] ∧ pσ2 = pσ1 ∧ pg2 = pg1).

  Lemma head_step_looping_to_prim_step' K e1 pσ1 pg1 :
    head_step_barrier_looping e1 pσ1 pg1 →
    prim_step'_barrier_looping (fill' K e1) pσ1 pg1.
  Proof.
    intros Hloop ????? Hprim. inversion Hprim as [K' e1']; subst.
    assert (K' = K ∧ e1' = e1) as (->&->).
    { eapply head_redex_unique; eauto.
      - rewrite /head_reducible; last by (do 5 eexists; econstructor; eauto); auto.
      - eapply Hloop.
    }
    edestruct Hloop as (Heq1&He2&Heq3&Heq4); first eassumption; subst.
    eauto.
  Qed.

  Theorem head_step_simulation_rev e1 pσ1 pg1 pσ2 pg2 σ1 g1 κ e2 efs :
    head_step e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
    state_compat σ1 pσ1 →
    global_compat g1 pg1 →
    ∃ σ2 g2 e2',
      head_step e1 σ1 g1 κ e2' σ2 g2 efs ∧
      (head_step_barrier_looping e1 pσ1 pg1 ∨
       (e2 = e2' ∧ state_compat σ2 pσ2 ∧ global_compat g2 pg2)).
  Proof.
  Admitted.

  Theorem prim_step'_simulation_rev e1 pσ1 pg1 pσ2 pg2 σ1 g1 κ e2 efs :
    prim_step' e1 pσ1 pg1 κ e2 pσ2 pg2 efs →
    state_compat σ1 pσ1 →
    global_compat g1 pg1 →
    ∃ σ2 g2 e2',
      prim_step' e1 σ1 g1 κ e2' σ2 g2 efs ∧
      (prim_step'_barrier_looping e1 pσ1 pg1 ∨
       (e2 = e2' ∧ state_compat σ2 pσ2 ∧ global_compat g2 pg2)).
  Proof.
    intros Hprim.
    inversion Hprim; subst.
    intros. edestruct (head_step_simulation_rev) as (σ2&g2&e2alt'&Hstep&Hcases); eauto.
    do 3 eexists. split_and!; eauto.
    { econstructor; eauto. }
    { destruct Hcases as [Hleft|Hright].
      { left. eapply head_step_looping_to_prim_step'; eauto. }
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
    eapply Hirred.
  Admitted.

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

  Theorem head_step_atomic_simulation e1 σ1 g1 κ e2 σ2 g2 efs :
    head_step_atomic e1 σ1 g1 κ e2 σ2 g2 efs →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1 pg2,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        head_step_atomic e1 pσ1 pg1 κ e2 pσ2 pg2 efs.
  Proof.
    intros Hprim.
    inversion Hprim; subst.
    - intros.
      edestruct (head_step_simulation) as (?&?&?&?); eauto.
      do 3 eexists. split_and!; intuition eauto.
      econstructor; eauto.
    - intros.
      edestruct (rtc_prim_step'_simulation) as (?&?&?&?); eauto.
      do 3 eexists. split_and!; intuition eauto.
      apply head_step_atomically; eauto.
      { eapply prim_step'_safe_transport; eauto. }
    - intros. do 3 eexists. split_and!; eauto.
      eapply head_step_atomically_fail.
      { eapply prim_step'_safe_transport; eauto. }
  Qed.

  Theorem prim_step_simulation e1 σ1 g1 κ e2 σ2 g2 efs :
    prim_step e1 σ1 g1 κ e2 σ2 g2 efs →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1 pg2,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        @prim_step (@goose_lang _ _ ADP.disk_semantics) e1 pσ1 pg1 κ e2 pσ2 pg2 efs.
  Proof.
    intros Hprim.
    inversion Hprim. simpl in *.
    intros. edestruct (head_step_atomic_simulation) as (?&?&?&?); eauto.
    do 3 eexists; split_and!; intuition eauto.
    econstructor; eauto.
  Qed.

  Theorem step_simulation t1 σ1 g1 κ t2 σ2 g2:
    step (t1, (σ1, g1)) κ (t2, (σ2, g2)) →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1 pg2,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        @step (@goose_lang _ _ ADP.disk_semantics) (t1, (pσ1, pg1)) κ (t2, (pσ2, pg2)).
  Proof.
    intros Hstep.
    inversion Hstep. simpl in *.
    monad_inv. intros. edestruct (prim_step_simulation) as (?&?&?&?); eauto.
    do 3 eexists; split_and!; intuition eauto.
    econstructor; eauto.
  Qed.

  Theorem erased_step_simulation t1 σ1 g1 t2 σ2 g2:
    erased_step (t1, (σ1, g1)) (t2, (σ2, g2)) →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1 pg2,
        state_compat σ1 pσ1 ∧
        global_compat g1 pg1 ∧
        @erased_step (@goose_lang _ _ ADP.disk_semantics) (t1, (pσ1, pg1)) (t2, (pσ2, pg2)).
  Proof.
    intros Hstep.
    inversion Hstep. simpl in *.
    intros. edestruct (step_simulation) as (?&?&?&?); eauto.
    do 3 eexists; split_and!; intuition eauto.
    econstructor; eauto.
  Qed.

  Theorem rtc_erased_step_simulation t1 σ1 g1 t2 σ2 g2:
    rtc erased_step (t1, (σ1, g1)) (t2, (σ2, g2)) →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pσ1 pg1 pg2,
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
    - inversion Heqρ1; subst. do 3 eexists; split_and!; eauto.
      apply rtc_refl.
    - destruct y as (e1'&σ1'&g1').
      edestruct (IHHrtc) as (pσ1'&pg2_&pg1'&Hcompat1&Hcompat2&Hrtc'); eauto.
      edestruct erased_step_simulation as (pσ1&pg1&pg0&Hcompat1_0&Hcompat2_0&Hstep); eauto.
      do 3 eexists; split_and!; eauto.
      econstructor; eauto. simpl.
      destruct pg0, pg2_; eauto.
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
          assert (i ∉ dom (gset _) m).
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
          intros Heq. rewrite Heq lookup_delete in Hdel. congruence.
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
          ** subst. rewrite lookup_insert in H6. inversion H6.
             rewrite //=. rewrite H5 => //=.
             edestruct H0; eauto. destruct H7 as (->&?). rewrite //=.
             rewrite /log_heap.possible/log_heap.sync//= in H4.
             apply elem_of_list_singleton in H4. subst. eauto.
          **  rewrite lookup_insert_ne // in H6.
              inversion Hcrash'. subst. destruct H7 as (_&Hlookup).
              eapply Hlookup in H6. rewrite lookup_delete_ne in H6; eauto.
      }
      {
        split.
        * rewrite ?dom_insert_L. destruct Hcompat' as (Hdomeq&_). rewrite Hdomeq; eauto.
        * intros. destruct (decide (addr = i)).
          ** subst. rewrite lookup_insert in H6. inversion H6; subst.
             rewrite lookup_insert. exists cb; split; eauto.
             inversion Hcrash. subst. destruct H7 as (?&Hlook_crash).
             edestruct (Hlook_crash) as (b&?&His_possible); eauto.
             subst. rewrite /AD.is_possible in His_possible.
             edestruct His_possible as (?&?&?Hin).
             rewrite lookup_insert in H8. inversion H8; subst.
             rewrite /log_heap.possible/log_heap.sync//= in H4.
             apply elem_of_list_singleton in H4; subst. eauto.
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
    destruct Hcompat as (?&?&?&?).
    simpl in *.
    edestruct (disk_compat_crash_inv) as (pd1&?&?); eauto.
    exists ({| trace := trace σ1;
               heap := heap σ1;
               oracle := oracle σ1;
               world := pd1 |}).
    split.
    { split_and!; eauto. }
    { destruct pσ2; simpl in *; subst. econstructor; eauto. }
  Qed.

  Definition config_compat (ρ : cfg _) (dρ : cfg _) :=
    state_compat (ρ.2.1) (dρ.2.1) ∧
    global_compat (ρ.2.2) (dρ.2.2) ∧
    ρ.1 = dρ.1.

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
      edestruct (rtc_erased_step_simulation) as (dσ1&dg1&[]&Hcompats&?&Hrtc'); eauto.
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
      edestruct (rtc_erased_step_simulation) as (dp1&dg1&[]&Hcompat1&Hgcompat&Hrtc1); try eapply Hrtc; eauto.
      exists (t1, (dp1, dg1)).
      split.
      { split_and!; eauto. }
      econstructor; eauto => //=. simpl in Heq. subst.
      eauto.
  Qed.

End translate.
