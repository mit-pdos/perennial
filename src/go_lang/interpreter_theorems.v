From RecordUpdate Require Import RecordSet.
From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From stdpp Require Import pretty.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From Perennial.Helpers Require Import Integers Transitions.
From Perennial.go_lang Require Export locations.
From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Import prelude.
From Perennial.go_lang Require Import interpret_types.
From Perennial.go_lang Require Import interpreter.

From Perennial.go_lang.examples Require Import goose_unittest.
From Perennial.go_lang.ffi Require Import disk.
Require Import Program.

Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.


(* The step relation is transitive. Doing n steps and then m steps is
the same as doing (n + m) steps.

Useful in interpret_ok for splitting goals like [If e0 e1 e2] ~~> [v]
into [If e0 e1 e2] ~~> [If #true e1 e2] and [If #true e1 e2] ~~> [v]. *)
Lemma nsteps_transitive : forall L n m p1 p2 p3 l1 l2,
    @language.nsteps L n p1 l1 p2 ->
    @language.nsteps L m p2 l2 p3 ->
    @language.nsteps L (n + m) p1 (l1 ++ l2) p3.
Proof.
  induction n.
  { (* n = 0 *)
    intros.
    inversion H.
    simpl.
    exact H0.
  }
  { (* S n *)
    intros.
    inversion H.
    rewrite <- app_assoc.
    eapply language.nsteps_l.
    {
      exact H2.
    }
    eapply IHn; [exact H3|exact H0].
  }
Qed.


(* Helper used for proving that no threads are spawned during an interpreter
step (this applies to any step except [Fork], which we don't
implement). *)
Lemma list_empty_surroundings : forall X (e:X) (e':X) (t1:list X) (t2:list X),
    [e] = t1 ++ e' :: t2 ->
    (t1 = []) /\ (t2 = []) /\ (e = e').
Proof.
  intros.
  assert (t1 = []).
  {
    destruct t1; [trivial|].
    inversion H.
    pose proof (app_cons_not_nil t1 t2 e').
    contradiction.
  }
  rewrite H0 in H.
  split; [exact H0|].
  assert (t2 = []).
  {
    destruct t2; [trivial|].
    inversion H.
  }
  rewrite H1 in H.
  inversion H.
  split; eauto.
Qed.

(* Another helper, but with efs. *)
Lemma list_empty_surroundings_strong : forall X (e:X) (e':X) (t1:list X) (t2:list X) (efs:list X),
    [e] = t1 ++ e' :: t2 ++ efs ->
    (t1 = []) /\ (t2 = []) /\ (efs = []) /\ (e = e').
Proof.
  intros.
  assert (t1 = []).
  {
    destruct t1; [trivial|].
    inversion H.
    pose proof (app_cons_not_nil t1 (t2 ++ efs) e').
    contradiction.
  }
  rewrite H0 in H.
  split; [exact H0|].
  assert (t2 = []).
  {
    destruct t2; [trivial|].
    inversion H.
  }
  rewrite H1 in H.
  inversion H.
  split; eauto.
Qed.

(* No threads are destroyed during any number of steps in the
language. If we know that [ρ ~~> ([e], σ)] in n steps, then we know that
ρ contained a list of expressions with only one element. *)
Lemma nsteps_no_thread_destroy `{!@LanguageCtx Λ K} n ρ e σ l:
  @language.nsteps Λ n ρ l ([e], σ) ->
  exists e' σ', ρ = ([e'], σ'). (* We learn that ρ steps to something that only has one thread. *)
Proof.
  generalize ρ l e σ.
  induction n.
  {
    intros.
    inversion H0.
    do 2 eexists; reflexivity.
  }
  {
    intros.
    inversion H0; try eauto.
    rewrite <- H4 in *.
    pose proof (IHn _ _ _ _ H3) as IH.
    destruct IH as (e' & IH').
    destruct IH' as (σ' & IH'').
    rewrite IH'' in H2.
    inversion H2.
    inversion H8.
    pose proof (list_empty_surroundings_strong _ _ _ _ _ _ H11) as one_thread.
    inversion one_thread.
    inversion H13.
    inversion H15.
    rewrite H10 in H7.
    rewrite H14 in H7.
    simpl in H7.
    do 2 eexists; exact H7.
  }
Qed.

(* If we know a step is valid outside of the context, then it is valid
within a context. *)
Lemma nsteps_ctx `{!@LanguageCtx Λ K} n e1 e2 σ1 σ2 l:
@language.nsteps Λ n ([e1], σ1) l ([e2], σ2) →
@language.nsteps Λ n ([K e1], σ1) l ([K e2], σ2).
Proof.
  generalize e1 e2 σ1 σ2 l.
  induction n.
  { (* n = 0 *)
    intros e e' σ σ' l' nstep_ooc; inversion nstep_ooc. (* nsteps hypothesis out-of-context *)
    apply language.nsteps_refl. }
  { (* S n *)
    intros e e' σ σ' l' nstep_ooc.
    inversion nstep_ooc as [|n' ρ1 ρ2 ρ3 κ κs step_ooc nstep_ooc_rest].
    pose proof (nsteps_no_thread_destroy _ _ _ _ _ nstep_ooc_rest) as intermediate_cfg_has_one_thread.
    inversion intermediate_cfg_has_one_thread as (e'' & (σ'' & P)).
    rewrite P in nstep_ooc_rest.
    pose proof (IHn _ _ _ _ _ nstep_ooc_rest) as nstep_ic_rest. (* nsteps in-context *)
    rewrite P in step_ooc.
    inversion step_ooc as [e_s σ_s e''_s σ''_s spawned_threads t1 t2 Pes Pe''s prim_step_e_e''].
    inversion Pes as [Pe].
    rewrite <- H4.
    rewrite <- H4 in prim_step_e_e''.
    pose proof (list_empty_surroundings _ _ _ _ _ Pe).
    inversion H5.
    inversion H7.
    rewrite <- H9 in prim_step_e_e''.
    inversion Pe''s as [Pe''].
    rewrite <- H10 in prim_step_e_e''.
    pose proof (list_empty_surroundings _ _ _ _ _ Pe'').
    inversion H11.
    inversion H13.
    pose proof (app_eq_nil t2 spawned_threads H14).
    inversion H16.
    rewrite <- H15 in prim_step_e_e''.
    rewrite H18 in prim_step_e_e''.
    pose proof (fill_step _ _ _ _ _ _ prim_step_e_e'') as prim_step_ic.
    eapply language.nsteps_l; [|exact nstep_ic_rest].
    eapply step_atomic with (t3 := []) (t4 := []); [| |exact prim_step_ic]; eauto.
  }
Qed.

(* Deals with monadic wrappers around head_trans. *)
Ltac head_step :=
  rewrite /= /head_step /=; repeat (monad_simpl; simpl).

(* Suppose we want to show that [a -> b] in 1 step. Then, nsteps
doesn't have a constructor for stepping just once. Instead we have to
use the nsteps_l constructor, which splits our goal into [a -> b] and
[b ~~> b]. We can then apply step_atomic for the first goal, and the
second is just nsteps_refl.

Note that we always apply step_atomic with t1, t2 as [] since we don't
care about threading. *)
Ltac single_step :=
  eapply language.nsteps_l; [|apply language.nsteps_refl];
  eapply step_atomic with (t1:=[]) (t2:=[]); [simpl; reflexivity|simpl; reflexivity|apply head_prim_step; head_step].

(* Given that the first part of a computation succeeds, rewrites the
hypothesis to be about the rest of the computation. If the first part
fails, deduces a contradiction. *)
Ltac runStateT_bind :=
  match goal with
  | [H : runStateT (mbind (fun x => @?F x) ?ma) ?σ = _ |- _] =>
    match goal with
    | [ma_result : runStateT ma σ = Works _ (?v, ?σ') |- _] =>
      try rewrite (runStateT_Error_bind _ _ _ _ _ _ F ma_result) in H
    | [ma_result : runStateT ma σ = Fail _ ?s |- _] =>
      (* If we're in a Fail case, inversion completes the subgoal. *)
      try rewrite (runStateT_Error_bind_false _ _ _ _ F s ma_result) in H; try inversion H
    | _ => fail
    end
  | _ => fail
  end.

Lemma biggest_loc_rec_ok ps :
  forall l l' (v: nonAtomic val),
    ({| loc_car := l |}, v) ∈ ps ->
    biggest_loc_rec ps = {| loc_car := l' |} ->
    l' >= l.
Proof.
  induction ps as [|hd].
  { (* empty list *)
    intros.
    inversion H.
  }
  { (* hd :: ps *)
    intros l l' v.
    unfold elem_of.
    unfold elem_of in IHps.
    pose ({| loc_car := l |}, v) as p.
    fold p.
    intros p_in_ps.
    pose proof (elem_of_cons ps p hd) as where_is_p.
    rewrite -> where_is_p in p_in_ps.
    destruct p_in_ps.
    { (* p :: ps *)
      rewrite <- H.
      simpl.
      intros.
      inversion H0.
      lia.
    }
    { (* hd :: (p in here) *)
      unfold p, elem_of in H.
      simpl.
      destruct (biggest_loc_rec ps) as [l_old] eqn:bloc_old.
      pose proof (IHps l l_old _ H).
      assert (l_old >= l) by (apply H0; reflexivity).
      intros.
      destruct hd.
      inversion H2.
      lia.
    }
  }
Qed.

Lemma biggest_loc_ok (σ: state) :
  forall l l' v,
    ({| loc_car := l |}, v) ∈ gmap_to_list (heap σ) ->
    biggest_loc σ = {| loc_car := l' |} ->
    l' >= l.
Proof.
  intros l l' v elem bloc.
  unfold biggest_loc in bloc.
  apply (biggest_loc_rec_ok _ _ _ _ elem bloc).
Qed.


(* Guarantees find_alloc_location returns a location that is the
  start of a fresh range of length 'bound'. *)
Lemma find_alloc_location_fresh :
  forall s bound, isFreshTo bound s (find_alloc_location s bound).
Proof.
  intros s bound i i_gt_z i_lt_len.
  destruct (find_alloc_location s bound +ₗ i) as [l] eqn:fal.
  destruct (heap s !! {| loc_car := l |}) eqn:s_val; [|by reflexivity].
  unfold find_alloc_location in fal.
  pose proof elem_of_map_to_list (heap s) {| loc_car := l |} n as mtl_iff.
  pose proof s_val as mtl_val.
  rewrite <- mtl_iff in mtl_val.
  unfold map_to_list in mtl_val.
  destruct (biggest_loc s) as [l'] eqn:blocs.
  pose proof biggest_loc_ok s _ _ _ mtl_val blocs as blok.
  inversion fal.
  lia.
Qed.

Lemma find_alloc_location_ok (v0 : val) :
  ∀ s (i : Z) ,
    0 ≤ i →
    i < strings.length (flatten_struct v0) →
    heap s !! (find_alloc_location s (strings.length (flatten_struct v0)) +ₗ i) =
    None.
Proof.
  intros.
  pose proof (find_alloc_location_fresh s (strings.length (flatten_struct v0))).
  eauto.
Qed.

(* For computations where the first component is an interpret call,
  destructs on runStateT of that interpret call. If it Fails,
  immediately find a contradiction with runStateT_bind. If it Works,
  apply the inductive hypothesis from interpret_ok, passed in as IHn. *)
Ltac run_next_interpret IHn :=
  match goal with
  | [H : runStateT (mbind (fun x => @?F x) (interpret ?n ?e)) ?σ = _ |- _] =>
    let interp_e := fresh "interp_e" in
    let IHe := fresh "IHe" in
    let e_to_v := fresh "nsteps_interp" in
    let v0 := fresh "v" in
    let m := fresh "m" in
    let l := fresh "l" in
    let v := fresh "v" in
    let s := fresh "s" in
    destruct (runStateT (interpret n e) σ) as [v0|] eqn:interp_e; [|runStateT_bind];
    destruct v0 as (v & s);
    pose (IHn e σ v s interp_e) as IHe;
    destruct IHe as (m & l & e_to_v);
    runStateT_bind
  | _ => fail
  end.

(* Given ctx_expr, a fill of some context, looks for hypotheses like
  [e ~~> v] and a goal like [ctx_expr e ~~> ctx_expr v]. Uses nsteps_ctx
  lemma to dispatch the goal. *)
Ltac ctx_step ctx_expr :=
  match goal with
  | [ nsteps_interp : nsteps _ ([?e], ?s) _ (_, _) |- _ ] =>
    let r := eval simpl in (ctx_expr e) in
        match goal with
        | [ |- nsteps _ ([r], s) _ _ ] =>
          let H := fresh "nsteps_interp_ctx" in
          pose proof (@nsteps_ctx _ ctx_expr _ _ _ _ _ _ _ nsteps_interp) as H;
          simpl in H;
          exact H
        | _ => fail
        end
  | _ => fail
  end.

(* For any expression e that we can successfully interpret to a
  value v, there exists some number m of steps in the heap transition
  function that steps e to v. *)
Theorem interpret_ok : forall (n: nat) (e: expr) (σ: state) (v: val) (σ': state),
    (((runStateT (interpret n e) σ) = Works _ (v, σ')) ->
     exists m l, @language.nsteps heap_lang m ([e], σ) l ([Val v], σ')).
Proof.
  intros n. induction n.
  { by intros []. }

  intros e σ v σ' interp. destruct e; simpl; inversion interp; simpl.
  
  (* Val *)
  { eexists. eexists. apply language.nsteps_refl. }
  (* Var *)
  
  (* Rec *)
  { do 2 eexists.
    single_step.
  }
  
  (* App *)
  { 
    run_next_interpret IHn.
    run_next_interpret IHn.
    destruct v2; simpl in H0; try by inversion H0.
    pose proof (IHn _ _ _ _ H0) as IHapp.
    destruct IHapp as (k & IHapp').
    destruct IHapp' as (l'' & app_to_v).
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [App e1 e2] -> [App e1 v1] *)
      ctx_step (fill [(AppRCtx e1)]).
    }
    eapply nsteps_transitive.
    { (* [App e1 v1] -> [App (rec f x := e) v1] *)
      ctx_step (fill [(AppLCtx v1)]).
    }
    eapply nsteps_transitive.
    {
      single_step.
    }
    exact app_to_v.
  }

  (* UnOp *)
  { run_next_interpret IHn.
    inversion H0.
    destruct (un_op_eval op v1) eqn:uo_eval; inversion H1; subst; clear H1.
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [UnOp op e] -> [UnOp op v1] *)
      ctx_step (fill [(UnOpCtx op)]).
    }
    {
      (* [UnOp op v1] -> [v] *)
      single_step.
    }
  }

  (* BinOp *)
  {
    run_next_interpret IHn.
    run_next_interpret IHn.
    inversion H0.
    destruct (bin_op_eval op v2 v1) eqn:bo_eval; inversion H1.
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [BinOp op e1 e2] -> [BinOp op v2 e2] *)
      ctx_step (fill [(BinOpLCtx op e2)]).
    }
    eapply nsteps_transitive.
    { (* [BinOp op v2 e2] -> [BinOp op v2 v1] *)
      ctx_step (fill [(BinOpRCtx op v2)]).
    }
    { (* [BinOp op v2 v1] -> [v] *)
      subst.
      single_step.
    }
  }

  (* If *)
  { run_next_interpret IHn.
    destruct v1; simpl in H0; try by inversion H0.
    destruct l0; simpl in H0; try by inversion H0.
    destruct b.
    { (* v1 = true *)
      pose (IHn _ _ _ _ H0) as IH2.
      destruct IH2 as (m' & IH2').
      destruct IH2' as (l' & e2_to_v).
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [if e1 e2 e3] -> [if #true e2 e3] *)
        ctx_step (fill [(IfCtx e2 e3)]).
      }
      eapply nsteps_transitive.
      { (* [if #true e2 e3] -> [e2] *)
        single_step.
      }
      (* [e2] -> [v] *)
      exact e2_to_v.
    }

    { (* v1 = false *)
      pose (IHn _ _ _ _ H0) as IH3.
      destruct IH3 as (m' & IH3').
      destruct IH3' as (l' & e3_to_v).
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [if e1 e2 e3] -> [if #false e2 e3] *)
        ctx_step (fill [(IfCtx e2 e3)]).
      }
      eapply nsteps_transitive.
      { (* [if #false e2 e3] -> [e3] *)
        single_step.
      }
      (* [e3] -> [v] *)
      exact e3_to_v.
    }
  }

  (* Pair *)
  { 
    run_next_interpret IHn.
    run_next_interpret IHn.
    inversion H0.
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [Pair e1 e2] -> [Pair v1 e2] *)
      ctx_step (fill [(PairLCtx e2)]).
    }
    eapply nsteps_transitive.
    { (* [Pair v1 e2] -> [Pair v1 v2] *)
      ctx_step (fill [(PairRCtx v1)]).
    }
    subst.
    single_step.
  }

  (* Fst *)
  { run_next_interpret IHn.
    destruct v1; simpl in H0; inversion H0.
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [Fst e] -> [Fst v0] *)
      ctx_step (fill [FstCtx]).
    }
    subst.
    single_step.
  }

  (* Snd *)
  { run_next_interpret IHn.
    destruct v1; simpl in H0; inversion H0.
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [Snd e] -> [Snd v0] *)
      ctx_step (fill [SndCtx]).
    }
    subst.
    single_step.
  }
  
  (* InjL *)
  { run_next_interpret IHn.
    inversion H0.
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [InjL e] -> [InjL v1] *)
      ctx_step (fill [InjLCtx]).
    }
    {
      (* [InjL v1] -> [v] *)
      subst.
      single_step.
    }
  }

  (* InjR *)
  { run_next_interpret IHn.
    inversion H0.
    do 2 eexists.
    eapply nsteps_transitive.
    { (* [InjR e] -> [InjR v1] *)
      ctx_step (fill [InjRCtx]).
    }
    {
      (* [InjR v1] -> [v] *)
      subst.
      single_step.
    }
  }

  (* Case *)
  { run_next_interpret IHn.
    destruct v1 eqn:v1_type; simpl in H0; try by inversion H0.
    { (* InjL *)
      pose proof (IHn _ _ _ _ H0) as IHe2.
      destruct IHe2 as (m' & IHe2').
      destruct IHe2' as (l' & e2_to_v).
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [Case e1 e2 e3] -> [Case (InjLV v0) e2 e3] *)
        ctx_step (fill [(CaseCtx e2 e3)]).
      }
      eapply nsteps_transitive.
      {
        single_step.
      }
      exact e2_to_v.
    }
    { (* InjR *)
      pose proof (IHn _ _ _ _ H0) as IHe3.
      destruct IHe3 as (m' & IHe3').
      destruct IHe3' as (l' & e3_to_v).
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [Case e1 e2 e3] -> [Case (InjRV v0) e2 e3] *)
        ctx_step (fill [(CaseCtx e2 e3)]).
      }
      eapply nsteps_transitive.
      {
        single_step.
      }
      exact e3_to_v.
    }
  }

  (* Primitive0 *)
  {
    (* TODO: Remove dependent destruction using
       https://jamesrwilcox.com/dep-destruct.html technique *)
    dependent destruction op.
    inversion H0.
  }

  (* Primitive1 *)
  {
    dependent destruction op.
    { (* AllocStruct *)
      run_next_interpret IHn.
      simpl in H0.
      inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [AllocStruct e] -> [AllocStruct v0] *)
        ctx_step (fill [(Primitive1Ctx AllocStructOp)]).
      }
      single_step.
      eapply relation.bind_suchThat.
      (* Must prove the location find_alloc_location found is adequate *)
      { intros i ? ?.
        eapply find_alloc_location_ok; eauto. }
      monad_simpl.
    }

    { (* PrepareWrite *)
      run_next_interpret IHn.
      destruct v1; simpl in H0; try by inversion H0.
      destruct l0; simpl in H0; try by inversion H0.
      destruct (heap s !! l0) as [heap_na_val|] eqn:hv; simpl in H0; [|by inversion H0].
      destruct heap_na_val as [|heap_val n0]; simpl in H0; try by inversion H0.
      destruct n0; simpl in H0; inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [PrepareWrite e] -> [PrepareWrite #l0] *)
        ctx_step (fill [(Primitive1Ctx PrepareWriteOp)]).
      }
      rewrite <- H2.
      single_step.
    }

    { (* StartRead *)
      run_next_interpret IHn.
      destruct v1; simpl in H0; try by inversion H0.
      destruct l0; simpl in H0; try by inversion H0.
      destruct (heap s !! l0) eqn:heap_at_l0; try by inversion H0.
      destruct n0; simpl in H0; try by inversion H0.
      inversion H0; subst; clear H0.
      do 2 eexists.
      eapply nsteps_transitive.
      {
        ctx_step (fill [(Primitive1Ctx StartReadOp)]).
      }
      single_step.
    }

    { (* FinishRead *)
      run_next_interpret IHn.
      destruct v1; simpl in H0; try by inversion H0.
      destruct l0; simpl in H0; try by inversion H0.
      destruct (heap s !! l0) eqn:heap_at_l0; try by inversion H0.
      destruct n0; simpl in H0; try by inversion H0.
      destruct n0; simpl in H0; try by inversion H0.
      inversion H0; subst; clear H0.
      do 2 eexists.
      eapply nsteps_transitive.
      {
        ctx_step (fill [(Primitive1Ctx FinishReadOp)]).
      }
      single_step.
    }

    { (* Load *)
      run_next_interpret IHn.
      destruct v1; simpl in H0; try by inversion H0.
      destruct l0; simpl in H0; try by inversion H0.
      destruct (heap s !! l0) eqn:heap_at_l0; try by inversion H0.
      destruct n0; simpl in H0; try by inversion H0.
      destruct n0; simpl in H0; try by inversion H0.
      inversion H0; subst; clear H0.
      do 2 eexists.
      eapply nsteps_transitive.
      {
        ctx_step (fill [(Primitive1Ctx LoadOp)]).
      }
      single_step.
    }

    { (* Input *)
      run_next_interpret IHn.
      destruct v1; simpl in H0; inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      {
        ctx_step (fill [(Primitive1Ctx InputOp)]).
      }
      single_step.
    }

    { (* Output *)
      run_next_interpret IHn.
      destruct v1; simpl in H0; inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      {
        ctx_step (fill [(Primitive1Ctx OutputOp)]).
      }
      single_step.
    }
  }

  (* Primitive2 *)
  { dependent destruction op.
    { (* AllocN *)
      run_next_interpret IHn.
      run_next_interpret IHn.
      destruct v1; simpl in H0; try by inversion H0.
      destruct l1; simpl in H0; inversion H0.
      destruct (int.val n0 <=? 0) eqn:n0_int; simpl in H0; inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      {
        ctx_step (fill [(Primitive2LCtx AllocNOp e2)]).
      }
      eapply nsteps_transitive.
      {
        ctx_step (fill [(Primitive2RCtx AllocNOp #n0)]).
      }
      single_step.
      rewrite -> ifThenElse_if; [|(rewrite -> Z.leb_nle in n0_int; lia)].
      simpl.
      monad_simpl.
      pose proof (find_alloc_location_fresh s0 (int.val n0)) as loc_fresh.
      eapply relation.bind_suchThat.
      {
        apply loc_fresh.
      }
      monad_simpl.
    }

    { (* FinishStore *)
      do 2 run_next_interpret IHn.
      destruct v1; simpl in H0; try by inversion H0.
      destruct l1; simpl in H0; try by inversion H0.
      destruct (heap s0 !! l1) eqn:heap_at_l1; simpl in H0; try by inversion H0.
      destruct n0 eqn:n0_is_writing; simpl in H0; inversion H0.
      do 2 eexists.
      eapply nsteps_transitive.
      { (* [FinishStore e1 e2] -> [FinishStore #l1 e2] *)
        ctx_step (fill [(Primitive2LCtx FinishStoreOp e2)]).
      }
      eapply nsteps_transitive.
      { (* [FinishStore #l0 e2] -> [FinishStore #l1 v2] *)
        ctx_step (fill [(Primitive2RCtx FinishStoreOp #l1)]).
      }
      single_step.
    }
  }

  (* CmpXchg *)
  {
    do 3 run_next_interpret IHn.
    destruct v1; simpl in H0; try by inversion H0.
    destruct l2; simpl in H0; try by inversion H0.
    destruct (heap s1 !! l2) as [x|] eqn:heap_at_l2; simpl in H0; try by inversion H0.
    destruct x as [|vl] eqn:x_is; simpl in H0; try by inversion H0.
    destruct n0 eqn:n0_is_0; simpl in H0; try by inversion H0.
    destruct (bin_op_eval EqOp vl v2) as [some_b|] eqn:boe; simpl in H0; try by inversion H0.
    destruct some_b; simpl in H0; try by inversion H0.
    destruct l3; simpl in H0; try by inversion H0.
    destruct b; simpl in H0; inversion H0.
    { (* CmpXchg succeeds (true case) *)
      do 2 eexists.
      eapply nsteps_transitive.
      {
        ctx_step (fill ([CmpXchgLCtx e2 e3])).
      }
      eapply nsteps_transitive.
      {
        ctx_step (fill ([CmpXchgMCtx #l2 e3])).
      }
      eapply nsteps_transitive.
      {
        ctx_step (fill ([CmpXchgRCtx #l2 v2])).
      }
      single_step.
      unfold bin_op_eval in boe; simpl in boe.

      destruct (decide (vals_compare_safe vl v2)) eqn:vcs; inversion boe.
      monad_simpl.
      case_bool_decide; inversion H3.
      repeat (monad_simpl; simpl).
    }
    { (* CmpXchg fails (false case) *)
      do 2 eexists.
      eapply nsteps_transitive.
      {
        ctx_step (fill ([CmpXchgLCtx e2 e3])).
      }
      eapply nsteps_transitive.
      {
        ctx_step (fill ([CmpXchgMCtx #l2 e3])).
      }
      eapply nsteps_transitive.
      {
        ctx_step (fill ([CmpXchgRCtx #l2 v2])).
      }
      single_step.
      unfold bin_op_eval in boe; simpl in boe.
      destruct (decide (vals_compare_safe vl v2)) eqn:vcs; inversion boe.
      monad_simpl.
      case_bool_decide; inversion H3.
      repeat (monad_simpl; simpl).
      constructor.
      rewrite H2.
      reflexivity.
    }
  }

  (* ExternalOp *)
  { run_next_interpret IHn.
    destruct (runStateT (ext_interpret_step op v1) s) as [e_result|] eqn:ext_interp_v1; [|runStateT_bind].
    destruct e_result as (e' & s').
    pose proof (ext_interpret_ok _ _ _ _ _ ext_interp_v1) as ei_ok.
    destruct ei_ok as (m' & (l' & nstep_ext_interp)).
    runStateT_bind.
    pose proof (IHn _ _ _ _ H0).
    destruct H as (m'' & (l'' & rest_nstep)).
    do 2 eexists.
    eapply nsteps_transitive.
    {
      ctx_step (fill ([ExternalOpCtx op])).
    }
    eapply nsteps_transitive.
    {
      exact nstep_ext_interp.
    }
    exact rest_nstep.
  }
Qed.


(* If state_readn_vec succeeds, for each i in the range requested, the
heap at l + i should be some nonatomic value and that nonatomic value
should be at the return value in index i. *)
Lemma state_readn_vec_ok : forall n σ l v,
    (state_readn_vec σ l n = Some v) ->
    (forall (i:fin n),
        match σ.(heap) !! (l +ₗ i) with
        | Some nav => nav = v !!! i
        | _ => False
        end).
Proof.
  induction n.
  {
    intros.
    inversion i.
  }
  {
    intros.
    dependent destruction v.
    simpl in H.
    destruct (heap σ !! l) as [nav|] eqn:heap_at_l; try by inversion H.
    simpl in H.
    destruct (state_readn_vec σ (l +ₗ 1) n) as [vtl|] eqn:srv_ind; try by inversion H.
    simpl in H.
    unfold mret in H.
    inversion H.
    inv_fin i.
    {
      simpl.
      assert (l +ₗ 0%nat = l) as plus_zero.
      {
        unfold loc_add.
        rewrite Zplus_0_r.
        destruct l.
        simpl.
        reflexivity.
      }
      rewrite plus_zero heap_at_l; by exact H1.
    }
    {
      intros.
      assert (l +ₗ FS i = (l +ₗ 1) +ₗ i) as l_plus_one.
      {
        unfold loc_add.
        destruct l.
        simpl.
        replace (loc_car + S i) with (loc_car + 1 + i); [reflexivity|].
        lia.
      }
      rewrite l_plus_one.
      pose proof (IHn σ (l +ₗ 1) vtl srv_ind i).
      destruct (heap σ !! (l +ₗ 1 +ₗ i)) as [navi|] eqn:heap_at_l1i; [|contradiction].
      simpl.
      rewrite H0.
      apply Eqdep_dec.inj_pair2_eq_dec in H2.
      {
        rewrite H2; reflexivity.
      }
      exact Nat.eq_dec.
    }
  }
Qed.

Lemma commute_option_vec_ok {A} : forall n (ov: vec (option A) n) (v: vec A n),
    (commute_option_vec A ov = Some v) ->
    (forall (i:fin n), ov !!! i = Some (v !!! i)).
Proof.
  induction n.
  {
    intros.
    inversion i.
  }
  {
    intros.
    dependent destruction ov.
    simpl in H.
    destruct h as [a|]; [simpl in H|by inversion H].
    destruct (commute_option_vec A ov) as [v'|] eqn:cov_tail; [unfold mret, option_ret in H; simpl in H|by inversion H].
    pose proof (IHn _ _ cov_tail) as IH_tail.
    inversion H.
    inv_fin i.
    {
      simpl.
      reflexivity.
    }
    {
      intros i.
      simpl.
      exact (IH_tail i).
    }
  }
Qed.

Lemma read_block_from_heap_ok (σ: state) (l: loc) (b: Block) :
  (read_block_from_heap σ l = Some b) ->
  (forall (i:Z), 0 <= i -> i < 4096 ->
            match σ.(heap) !! (l +ₗ i) with
            | Some (Reading v _) => Block_to_vals b !! Z.to_nat i = Some v
            | _ => False
            end).
Proof.
  intros.
  unfold read_block_from_heap in H.
  unfold mbind in H.
  unfold option_bind in H.
  destruct (state_readn_vec σ l block_bytes) as [navs|] eqn:vec_at_l; try by inversion H.
  unfold block_bytes in *.
  destruct (commute_option_vec val (vmap free_val navs)) as [v|] eqn:all_free; try by inversion H.

  (* Only way to convert (Z.to_nat i) to a (fin 4096) is to have
  hypothesis that says exactly this. *)
  assert ((Z.to_nat i < 4096)%nat) as fin_i by lia. 
  
  pose proof (commute_option_vec_ok _ _ _ H (fin_of_nat fin_i)) as cov_ok_v.
  pose proof (commute_option_vec_ok _ _ _ all_free (fin_of_nat fin_i)) as cov_ok_navs.
  pose proof (state_readn_vec_ok _ _ _ _ vec_at_l (fin_of_nat fin_i)) as srv_ok_l.

  destruct (heap σ !! (l +ₗ fin_of_nat fin_i)) as [nav|] eqn:heap_at_fin_i; [|rewrite heap_at_fin_i in srv_ok_l; contradiction].
  assert ((l +ₗ i) = (l +ₗ fin_of_nat fin_i)).
  {
    unfold loc_add.
    replace (loc_car l + (fin_of_nat fin_i)) with (loc_car l + i); [reflexivity|].
    pose proof (fin_to_of_nat _ _ fin_i).
    rewrite H2.
    lia.
  }
  rewrite -> H2.
  rewrite heap_at_fin_i in srv_ok_l.
  rewrite heap_at_fin_i.
  rewrite srv_ok_l.
  rewrite -> (vlookup_map free_val navs (fin_of_nat fin_i)) in cov_ok_navs.
  unfold free_val in cov_ok_navs.
  destruct (navs !!! fin_of_nat fin_i) as [|nav'] eqn:navs_at_fin_i; inversion cov_ok_navs.
  destruct n eqn:n_is_free; inversion cov_ok_navs.
  clear cov_ok_navs navs_at_fin_i heap_at_fin_i H4 H5 H2 srv_ok_l nav'
        n n_is_free nav all_free H navs vec_at_l.
  unfold block_bytes in cov_ok_v. (* block_bytes doesn't show, but is here and needs to be unfolded *)
  rewrite -> (vlookup_map byte_val v (fin_of_nat fin_i)) in cov_ok_v.
  destruct (v !!! fin_of_nat fin_i) eqn:v_at_fin_i; try by inversion cov_ok_v.
  unfold Block_to_vals.
  pose proof (list_lookup_fmap b2val b (Z.to_nat i)) as llf.
  rewrite llf.
  simpl in cov_ok_v.
  destruct l0; try by inversion cov_ok_v.
  inversion cov_ok_v as [b_at_fin_i].
  rewrite <- b_at_fin_i.
  pose proof (vlookup_lookup' b (Z.to_nat i) n) as vll.
  assert ((b : list u8) !! Z.to_nat i = Some n).
  {
    apply vll.
    exists fin_i.
    rewrite b_at_fin_i; reflexivity.
  }
  rewrite H.
  unfold b2val.
  simpl; reflexivity.
Qed.


Lemma disk_interpret_ok : forall (eop : DiskOp) (arg : val) (result : expr) (σ σ': state),
    (runStateT (disk_interpret_step eop arg) σ = Works _ (result, σ')) ->
    exists m l, @language.nsteps heap_lang m ([ExternalOp eop (Val arg)], σ) l ([result], σ').
Proof.
  intros eop arg result σ σ' H.
  destruct eop; inversion H.
  { (* ReadOp *)
    destruct arg; try by inversion H1.
    destruct l; try by inversion H1.
    simpl in H1.
    destruct (world σ !! int.val n) eqn:disk_at_n; rewrite disk_at_n in H1; try by inversion H1.
    simpl in H1.
    inversion H1.
    do 2 eexists.
    single_step.
    rewrite disk_at_n.
    simpl.
    monad_simpl.
    pose proof (find_alloc_location_fresh σ 4096) as fresh.
    {
      eapply relation.bind_suchThat.
      {
        simpl.
        exact fresh.
      }
      monad_simpl.
    }
  }
  { (* WriteOp *)
    destruct arg; try by inversion H1.
    destruct arg1; try by inversion H1.
    destruct l; try by inversion H1.
    destruct arg2; try by inversion H1.
    destruct l; try by inversion H1. (* takes a very long time (why?) *)
    simpl in H1.
    destruct (world σ !! int.val n) eqn:disk_at_n; rewrite disk_at_n in H1; try by inversion H1. (* also takes a long time *)
    destruct (read_block_from_heap σ l) eqn:block_at_l; try by inversion H1.
    simpl in H1.
    inversion H1.
    do 2 eexists.
    single_step.
    rewrite disk_at_n.
    simpl.
    monad_simpl.
    pose proof (read_block_from_heap_ok _ _ _ block_at_l) as rbfsok.
    eapply relation.bind_suchThat; [exact rbfsok|].
    monad_simpl.
  }
  { (* SizeOp *)
    destruct arg; try by inversion H1.
    destruct l; try by inversion H1.
    simpl in H1.
    inversion H1.
    do 2 eexists.
    single_step.
  }
Qed.
