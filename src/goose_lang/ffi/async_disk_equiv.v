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
        inversion H. intuition.
        destruct (world pσ2 !! int.Z n) eqn:Hlook; last first.
        { exfalso. destruct H4.
          rewrite //= in H4.
          revert Hlook. rewrite -not_elem_of_dom.  intros Hfalso.
          apply Hfalso. rewrite -H4. apply elem_of_dom. eauto.
          Search is_Some lookup.
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
      * (* WriteOp *)
               eapply H4.

               (*

             rewrite //=.
             unfold check. rewrite ifThenElse_if; eauto. rewrite /=. repeat econstructor; eauto.
             rewrite /when. rewrite ifThenElse_else; eauto. repeat econstructor.
         *** repeat econstructor => //=.

        rewrite //= in H4. econstructor; eauto; repeat econstructor; rewrite ?Heq; eauto => //=.
          { 
          destruct H4.
          {
          f_equal. f_equal. destruct pσ2; subst.
          simpl in * => //=. rewrite /RecordSet.set //=.
          congruence.

      inv
      d
      inv
      monad_inv.

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


  Theorem prim_step_simulation de1 pe1 σ1 g1 κ de2 σ2 g2 defs :
    translate de1 pe1 →
    prim_step de1 σ1 g1 κ de2 σ2 g2 defs →
    ∀ pg2 pσ2,
      state_compat σ2 pσ2 →
      global_compat g2 pg2 →
      ∃ pκ pσ1 pg1 pg2 pe2 pefs, state_compat σ1 pσ1 ∧
                          global_compat g1 pg1 ∧
                          translate de2 pe2 ∧
                          translate_tp defs pefs ∧
                          (prim_step pe1 pσ1 pg1 pκ pe2 pσ2 pg2 pefs ∨
                          rtc prim_step_noefs (pe1, pσ1) (pe2, pσ2)).
  Proof.
    intros Htrans Hprim.
    inversion Hprim.
    simpl in *.
    inversion H1; subst.
    - admit.
    -
      
*)
