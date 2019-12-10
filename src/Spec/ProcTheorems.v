Require Import Setoid.
Require Import Morphisms.
From Perennial Require Import Spec.Proc.
From Classes Require Import Classes.
From Transitions Require Import Relations Rewriting.
Require Import Tactical.ProofAutomation.
Require Import List.

Import RelationNotations.

Section Dynamics.
  Context `(sem: Dynamics Op OpState).
  Notation proc := (proc Op).
  Notation proc_seq := (proc_seq Op).
  Notation rec_seq := (rec_seq Op).
  Notation step := sem.(step).
  Notation crash_step := (lifted_crash_step sem).
  Notation finish_step := (lifted_finish_step sem).
  Notation State := (@State OpState).
  Notation exec_halt := (exec_halt sem).
  Notation exec_partial := (exec_partial sem).
  Notation exec := (exec sem).
  Notation exec_pool := (exec_pool sem).
  Notation exec_seq_partial := (exec_seq_partial sem).
  Notation exec_seq := (exec_seq sem).
  Notation rexec_seq := (rexec_seq sem).
  Notation exec_recover1 := (exec_recover1 sem).
  Notation exec_recover := (exec_recover sem).
  Notation exec_recover_partial := (exec_recover_partial sem).
  Notation rexec := (rexec sem).
  Notation rexec_partial := (rexec_partial sem).
  Notation rexec_seq_partial := (rexec_seq_partial sem).
  Notation proc_exec_seq := (proc_exec_seq sem).
  Notation exec_or_rexec := (exec_or_rexec sem).

  Hint Resolve rimpl_refl requiv_refl.

  Ltac destruct_hd :=
    match goal with
    | [ |- and_then (match ?v with | _ => _  end) _ ---> _ ] => destruct v
    end.

  Theorem exec_halt_finish T (p: proc T) :
    (exec p;; pure tt) ---> exec_halt p.
  Proof.
    unfold exec, exec_halt; induction p; simpl in *; norm; try rel_congruence;
      repeat destruct_hd; norm; apply from_none.
  Qed.

  Theorem exec_halt_noop T (p: proc T) :
    pure tt ---> exec_halt p.
  Proof.
    unfold exec_halt. setoid_rewrite <-bind_star_expand_r. Left.
  Qed.

  Theorem exec_seq_partial_noop (p: rec_seq) :
    pure tt ---> exec_seq_partial p.
  Proof.
    induction p; simpl; eauto.
    Right. apply exec_halt_noop.
  Qed.

  Lemma exec_partial_ret T (v: T) :
    exec_partial (Ret v) <---> pure (existT _ _ (Ret v) :: nil)%list.
  Proof.
    apply rimpl_to_requiv.
    - unfold exec_partial. apply bind_star_ind_r_pure.
      Split. simpl in *. unfold exec_pool_hd. simpl in *. norm.
      rew none_plus_r. apply from_none.
    - setoid_rewrite <-bind_star_expand_r. Left.
  Qed.

  Lemma exec_partial_finish T (p: proc T) s1 s2 (v: T) tp:
    exec_partial p s1 (Val s2 (cons (existT _ _ (Ret v)) tp)) ->
    exec p s1 (Val s2 (existT _ _ v)).
  Proof.
    intros. do 2 eexists. split; eauto.
    simpl. econstructor; eauto.
  Qed.

  Theorem exec_halt_ret T (v: T) :
    exec_halt (Ret v) <---> pure tt.
  Proof.
    unfold exec_halt. rew exec_partial_ret.
  Qed.

  Theorem exec_halt_idem T (p: proc T) :
    pure tt + exec_halt p <---> exec_halt p.
  Proof.
    apply rimpl_or; auto using exec_halt_noop.
  Qed.

  Theorem exec_seq_partial_idem (p: rec_seq) :
    pure tt + exec_seq_partial p <---> exec_seq_partial p.
  Proof.
    apply rimpl_or; auto using exec_seq_partial_noop.
  Qed.

  Definition exec_equiv T (p p': proc T) :=
    exec p <---> exec p' /\
    exec_halt p <---> exec_halt p'.

  Definition exec_seq_equiv (p p': rec_seq) :=
    exec_seq p <---> exec_seq p' /\
    exec_seq_partial p <---> exec_seq_partial p'.

  Global Instance exec_equiv_equiv T : Equivalence (exec_equiv (T:=T)).
  Proof.
    unfold exec_equiv.
    RelInstance_t; (intuition idtac);
      repeat match goal with
             | [ H: _ <---> _ |- _ ] =>
               apply requiv_to_rimpls in H
             | |- _ <---> _ =>
               apply rimpl_to_requiv
             | _ => progress propositional
             end;
      auto;
      try solve [ etransitivity; eauto ].
  Qed.

  Infix "<==>" := exec_equiv (at level 70).

  (* TODO: there is a more general theorem of this form *)
  Lemma exec_partial_crash_pure T (p: proc T):
    (_ <- exec_partial p; crash_step) <---> _ <- (exec_partial p;; pure tt); crash_step.
  Proof. rewrite bind_assoc. norm. Qed.

  Theorem rexec_equiv T (p p': proc T) (rec: rec_seq) :
    p <==> p' ->
    rexec p rec <---> rexec p' rec.
  Proof.
    unfold "<==>"; propositional.
    unfold exec_halt in H0.
    setoid_rewrite <-bind_assoc.
    rel_congruence.
    rewrite exec_partial_crash_pure.
    rewrite H0.
    norm.
  Qed.

  Theorem rexec_partial_equiv T (p p': proc T) (rec: rec_seq) :
    p <==> p' ->
    rexec_partial p rec <---> rexec_partial p' rec.
  Proof.
    unfold "<==>"; propositional.
    unfold exec_halt in H0.
    setoid_rewrite <-bind_assoc.
    rel_congruence.
    rewrite exec_partial_crash_pure.
    rewrite H0.
    norm.
  Qed.

  Global Instance exec_respectful T:
    Proper (@exec_equiv T ==> @requiv State State _) exec.
  Proof. intros ?? (?&?); intuition. Qed.

  Global Instance exec_halt_respectful T:
    Proper (@exec_equiv T ==> @requiv State State unit) exec_halt.
  Proof. intros ?? (?&?); intuition. Qed.

  Global Instance rexec_respectful T:
    Proper (@exec_equiv T ==> @eq (rec_seq) ==> @requiv State State _) rexec.
  Proof. intros ?? ? ?? ->. eapply rexec_equiv; eauto. Qed.

  Global Instance rexec_partial_respectful T:
    Proper (@exec_equiv T ==> @eq (rec_seq) ==> @requiv State State _) rexec_partial.
  Proof. intros ?? ? ?? ->. eapply rexec_partial_equiv; eauto. Qed.

  Theorem monad_left_id T T' (p: T' -> proc T) v :
      Bind (Ret v) p <==> p v.
  Proof.
    split; simpl; norm.
    - unfold exec, exec_partial.
      apply rimpl_to_requiv.
      * rew<- bind_star_expand.
        Split; [ apply from_none |].
        simpl. setoid_rewrite none_absorb_l at 1. setoid_rewrite none_plus_r at 1.
        unfold exec_pool_hd; norm; simpl.
        setoid_rewrite <-bind_star_expand at 1.
        rel_congruence; simpl.
      * setoid_rewrite <-bind_star_expand at 2.
        Right. simpl. setoid_rewrite none_absorb_l_equiv at 1. rew none_plus_r.
        simpl. unfold exec_pool_hd; norm.
    - unfold exec_halt, exec_partial.
      apply rimpl_to_requiv.
      * setoid_rewrite <-bind_star_expand at 1; norm.
        Split; [rew<- bind_star_expand; Left|].
        simpl. setoid_rewrite none_absorb_l at 1. setoid_rewrite none_plus_r at 1.
        simpl. unfold exec_pool_hd; norm; simpl.
      * setoid_rewrite <-bind_star_expand at 2; norm.
        Right. simpl. setoid_rewrite none_absorb_l_equiv at 1. rew none_plus_r.
        simpl. unfold exec_pool_hd; norm; simpl.
  Qed.

  (*
  Theorem monad_assoc
          `(p1: proc T1)
          `(p2: T1 -> proc T2)
          `(p3: T2 -> proc T3) :
    Bind (Bind p1 p2) p3 <==> Bind p1 (fun v => Bind (p2 v) p3).
  Proof.
    induction p1.
    - split; simpl; norm.
      unfold exec. exec_partial.
  Qed.
   *)

  Lemma exec_seq_partial_nil: exec_seq_partial Seq_Nil <---> pure tt.
  Proof. eauto. Qed.

  Lemma exec_seq_nil: exec_seq Seq_Nil <---> pure tt.
  Proof. eauto. Qed.

  Lemma exec_recover_nil: exec_recover Seq_Nil <---> seq_star (crash_step).
  Proof.
    unfold exec_recover.
    setoid_rewrite exec_seq_partial_nil.
    norm. apply bind_right_id_unit.
  Qed.
  
  Definition exec_partial_n {T} (p: proc T) n :=
    bind_rep_n n (exec_pool) ((existT _ T p) :: nil).

  Definition exec_n {T} (e: proc T) n (σ: State) (res: Return (State) {T : Type & T})
           : Prop :=
    match res with
    | Err => bind_rep_n n (exec_pool) (existT _ _ e :: nil) σ Err
    | Val σ' v => exists tp, bind_rep_n n (exec_pool)
                                        (existT _ _ e :: nil) σ
                                        (Val σ' (existT _ _ (Ret (projT2 v)) :: tp))
    end.

  Lemma exec_equiv_exec_n {T} (e : proc T) σ res:
    exec e σ res <-> exists n, exec_n e n σ res.
  Proof.
    destruct res.
    - split.
      * intros (tp&?&Hhd&Htl).
        destruct tp as [| (v'&[]) tp']; try inversion Htl.
        subst. apply bind_star_inv_rep_n in Hhd as (n&?).
        exists n, tp'. eauto.
      * intros (n&tp&Hexec).
        apply bind_star_rep_n_to_bind_star in Hexec.
        eexists (_ :: tp), _; split; eauto.
        simpl. destruct t; econstructor.
    - split.
      * intros H%bind_with_no_err.
        { apply bind_star_inv_rep_n in H as (n&?).
          exists n. eauto. }
        { intros ? [| (?&[])]; inversion 1. }
      * intros (n&Hexec).
        left. apply bind_star_rep_n_to_bind_star in Hexec. eauto.
  Qed.


  Lemma exec_partial_equiv_exec_partial_n {T} (e : proc T) σ res:
    exec_partial e σ res <-> exists n, exec_partial_n e n σ res.
  Proof.
    split.
    - intros (n&Hrep)%bind_star_inv_rep_n. exists n; eauto.
    - intros (n&?). eapply bind_star_rep_n_to_bind_star; eauto.
  Qed.

  Opaque Proc.exec.

  Definition rec_singleton {T} (rec: proc T) : rec_seq := Seq_Cons rec Seq_Nil.


  Lemma exec_seq_snoc T `(p: proc T) `(rec: rec_seq ):
    exec_seq (rec_seq_snoc rec p) <--->
             (exec_seq rec;; exec p;; pure tt).
  Proof.
    induction rec.
    - simpl. norm.
    - simpl. rew IHrec.
  Qed.

  Lemma exec_seq_append `(rec1: rec_seq) (rec2: rec_seq):
    exec_seq (rec_seq_append rec1 rec2) <--->
             (exec_seq rec1;; exec_seq rec2).
  Proof.
    induction rec1.
    - simpl. norm.
    - simpl. rew IHrec1.
  Qed.

  Lemma exec_seq_partial_snoc T `(p: proc T) `(rec: rec_seq ):
    exec_seq_partial (rec_seq_snoc rec p) <--->
                     (exec_seq_partial rec + (exec_seq rec ;; exec_halt p)).
  Proof.
    induction rec.
    - simpl. rewrite bind_left_id, exec_halt_idem. apply rimpl_to_requiv.
      * rewrite exec_halt_finish, rel_or_idem; auto.
      * Right.
    - simpl. setoid_rewrite IHrec.
      rewrite bind_dist_l.
      norm.
      rewrite <-rel_or_assoc.
      rewrite <-rel_or_assoc.
      apply or_respects_equiv; eauto.
      apply rel_or_symmetric.
  Qed.

  Lemma exec_seq_partial_singleton {T} (rec: proc T) :
    exec_seq_partial (rec_singleton rec) <---> exec_halt rec.
  Proof.
    simpl. apply rimpl_to_requiv.
    - Split. apply exec_halt_finish.
    - Right.
  Qed.

  Lemma exec_seq_partial_append `(rec1: rec_seq) `(rec2: rec_seq):
    exec_seq_partial (rec_seq_append rec1 rec2) <--->
                     (exec_seq_partial rec1 + (exec_seq rec1 ;; exec_seq_partial rec2)).
  Proof.
    induction rec1.
    - simpl. rewrite bind_left_id, exec_seq_partial_idem; auto.
    - simpl. setoid_rewrite IHrec1.
      rewrite bind_dist_l.
      norm.
      rewrite <-rel_or_assoc.
      rewrite <-rel_or_assoc.
      apply or_respects_equiv; eauto.
      apply rel_or_symmetric.
  Qed.


  (* TODO: this is probably unneeded *)
  Theorem exec_recover_snoc T `(p: proc T) `(rec: rec_seq) :
    exec_recover (rec_seq_snoc rec p) <--->
                 (exec_recover rec;;
                  seq_star (rexec p rec);;
                  exec p;; pure tt).
  Proof.
    unfold exec_recover.
    unfold exec_recover, rexec, rexec_seq; simpl; norm.
    rewrite exec_seq_partial_snoc.
    rewrite ?bind_dist_r.
    unfold exec_recover.
    setoid_rewrite exec_seq_snoc.
    gen (exec_seq rec) (exec_seq_partial rec) crash_step;
      clear rec.
    intros rec1 rec1_crash crash.
    rew denesting.
    rel_congruence.
    rewrite <- ?bind_assoc.
    rel_congruence; norm.
    rewrite <-bind_assoc.
    rewrite seq_unit_sliding_equiv.
    norm.
  Qed.

  Lemma exec_recover_append_helper
        (rec1 rec1_crash rec2 rec2_crash crash : relation State State unit):
    (_ <- seq_star ((_ <- rec1_crash; crash) + (_ <- _ <- rec1; rec2_crash; crash));
       _ <- rec1;
       rec2)
      <--->
      (_ <- seq_star (_ <- rec1_crash; crash);
         _ <- rec1;
         _ <- seq_star (_ <- rec2_crash; _ <- crash; _ <- seq_star (_ <- rec1_crash; crash); rec1);
         rec2).
  Proof.
    intros.
    rew denesting.
    rel_congruence.
    rewrite <- ?bind_assoc.
    rel_congruence; norm.
    rewrite seq_unit_sliding_equiv.
    norm.
  Qed.

  Theorem exec_recover_append
          `(rec1: rec_seq)
          `(rec2: rec_seq) :
    exec_recover (rec_seq_append rec1 rec2) <--->
                 (exec_recover rec1;;
                  seq_star (rexec_seq rec2 rec1);;
                  exec_seq (rec2)).
  Proof.
    unfold exec_recover, rexec, rexec_seq; simpl; norm.
    rewrite exec_seq_partial_append.
    rewrite ?bind_dist_r.
    unfold exec_recover.
    setoid_rewrite exec_seq_append.
    apply exec_recover_append_helper.
  Qed.

  Opaque lifted_crash_step.

  Theorem exec_recover_partial_append
          `(rec1: rec_seq)
          `(rec2: rec_seq) :
    exec_recover_partial (rec_seq_append rec1 rec2) --->
                 (exec_recover_partial rec1) +
                 (exec_recover rec1;;
                  seq_star (rexec_seq rec2 rec1);;
                  rexec_seq_partial rec2 rec1) +
                 (exec_recover rec1;;
                  seq_star (rexec_seq rec2 rec1);;
                  exec_seq_partial (rec2)).
  Proof.
    unfold exec_recover, exec_recover_partial, rexec, rexec_seq, rexec_seq_partial; simpl; norm.
    rewrite exec_seq_partial_append.
    rewrite ?bind_dist_r.
    setoid_rewrite exec_seq_partial_append.
    rewrite ?bind_dist_l.
    assert (Hcase2:
            (exec_recover rec1;;
            seq_star (rexec_seq rec2 rec1);;
            rexec_seq_partial rec2 rec1) <--->
           _ <- seq_star (_ <- exec_seq_partial rec1; crash_step);
           _ <- seq_star
                  (_ <- exec_seq rec1; _ <- exec_seq_partial rec2; _ <- crash_step;
                   seq_star (_ <- exec_seq_partial rec1; crash_step));
           _ <- exec_seq rec1;
           _ <- exec_seq_partial rec2;
           _ <- crash_step;
           exec_recover_partial rec1).
    {
      unfold exec_recover.
      setoid_rewrite bind_assoc.
      setoid_rewrite <-bind_assoc at 2.
      setoid_rewrite <-bind_assoc at 3.
      setoid_rewrite <-bind_assoc at 3.
      setoid_rewrite <-(seq_unit_sliding_equiv (exec_seq rec1)).
      norm.
    }

    assert(Hcase3:
           (exec_recover rec1;;
           seq_star (rexec_seq rec2 rec1);;
           exec_seq_partial (rec2)) <--->
           _ <- seq_star (_ <- exec_seq_partial rec1; crash_step);
           _ <- seq_star
                  (_ <- exec_seq rec1; _ <- exec_seq_partial rec2; _ <- crash_step;
                   seq_star (_ <- exec_seq_partial rec1; crash_step));
           _ <- exec_seq rec1;
           exec_seq_partial rec2).
    {
      unfold rexec_seq, exec_recover.
      setoid_rewrite bind_assoc at 1.
      setoid_rewrite <-bind_assoc at 2.
      setoid_rewrite <-bind_assoc at 2.
      setoid_rewrite <-bind_assoc at 2.
      setoid_rewrite <-(seq_unit_sliding_equiv (exec_seq rec1)).
      norm.
    }

    Split.
    - rew denesting.
      setoid_rewrite star_expand_r at 2.
      Split.
      * do 2 Left.
      * Left. Right.
        unfold exec_recover, rexec_seq, rexec_seq_partial in Hcase2.
        left_assoc rew Hcase2.
    - rew denesting.
      Right.
      unfold exec_recover, rexec_seq, rexec_seq_partial in Hcase3.
      left_assoc rew Hcase3.
  Qed.

  Theorem exec_recover_partial_noop (p: rec_seq) :
    pure tt ---> exec_recover_partial p.
  Proof.
    unfold exec_recover_partial.
    rew<- seq_star_none.
    apply exec_seq_partial_noop.
  Qed.

  Lemma exec_partial_err_exec_err T (p: proc T) s:
    exec_partial p s Err <-> exec p s Err.
  Proof.
    split.
    - econstructor; eauto.
    - destruct 1 as [?|(a&b&Hpart&Hbad)]; auto.
      destruct a as [|(?&[])]; inversion Hbad.
  Qed.

  Lemma exec_seq_partial_err_exec_seq_err (rec: rec_seq) s:
    exec_seq_partial rec s Err -> exec_seq rec s Err.
  Proof.
    revert s. induction rec; auto; intros s.
    unfold exec_seq_partial.
    intros [?|Hhd].
    - eapply and_then_err_cancel; eauto.
    - apply bind_pure_no_err in Hhd. left. apply exec_partial_err_exec_err; auto.
  Qed.

  Lemma rexec_partial_err_rexec_err T `(p: proc T) (rec: rec_seq) s:
    rexec_partial p rec s Err -> rexec p rec s Err.
  Proof.
    unfold rexec_partial, rexec, exec_recover, exec_recover_partial.
    intros H.
    eapply requiv_err_elim in H; swap 1 2.
    { repeat setoid_rewrite <-bind_assoc. reflexivity. }
    eapply requiv_err_elim; swap 1 2.
    { repeat setoid_rewrite <-bind_assoc. reflexivity. }
    eapply and_then_err_cancel; eauto.
    simpl. intros. apply exec_seq_partial_err_exec_seq_err; auto.
  Qed.

  Lemma exec_err_rexec_err T (p: proc T) rec s:
    exec p s Err -> rexec p rec s Err.
  Proof.
    intros Herr. apply exec_partial_err_exec_err in Herr.
    unfold rexec. left; eauto.
  Qed.

  Lemma rexec_singleton_ret_intro T (p: proc T) σ1 σ2 σ2' tp:
    exec_partial p σ1 (Val σ2 tp) ->
    crash_step σ2 (Val σ2' tt) ->
    rexec p (rec_singleton (Ret tt)) σ1 (Val σ2' tt).
  Proof.
    intros.
    do 2 eexists; split; eauto.
    do 2 eexists; split; eauto.
    do 2 eexists; split; simpl; eauto.
    { eapply seq_star_refl. }
    do 2 eexists; split; simpl; [| econstructor].
    do 2 eexists; split; eauto.
    econstructor.
    simpl. econstructor.
    Unshelve. exact tt.
  Qed.

  Inductive seq_star_exec_steps {R} (rec: proc R) : nat -> relation State State unit :=
    | sses_nil σ o :
        seq_star_exec_steps rec O σ (Val σ o)
    | sses_cons_val σ1 σ1' σ2 ret σ3 k n :
        crash_step σ1 (Val σ1' tt) ->
        bind_rep_n n (exec_pool) (existT _ R rec :: nil) σ1' (Val σ2 ret) ->
        seq_star_exec_steps rec k σ2 σ3 ->
        seq_star_exec_steps rec (S n + S k) σ1 σ3
    | sses_cons_err σ1 σ1' n :
        crash_step σ1 (Val σ1' tt) ->
        bind_rep_n n (exec_pool) (existT _ R rec :: nil) σ1' Err ->
        seq_star_exec_steps rec (S n) σ1 Err .

  Context (crash_non_err: forall s1 ret, (crash_step) s1 ret -> ret <> Err).

  Lemma seq_star_exec_steps_intro {R} (rec: proc R) σhalt ret:
    seq_star (_ <- crash_step; exec_halt rec) σhalt ret ->
    exists k, seq_star_exec_steps rec k σhalt ret.
  Proof.
    intros Hstar.
    induction Hstar as [|??? [] Hstep|? Hstep]; subst.
    - exists O. econstructor.
    - destruct Hstep as ([]&σ'&Hcrash&Hexec).
      edestruct IHHstar as (k&Hrest); auto.
      destruct Hexec as (?&?&Hpartial&Hpure).
      inversion Hpure; subst.
      apply bind_star_inv_rep_n in Hpartial as (n&Hbind).
      exists (S n + S k)%nat; econstructor; eauto.
    - destruct Hstep as [Hcrash|([]&σ'&Hcrash&Hexec)].
      { exfalso. eapply crash_non_err in Hcrash. eauto. }
      apply bind_pure_no_err in Hexec.
      apply exec_partial_equiv_exec_partial_n in Hexec as (n&?).
      eexists. eapply sses_cons_err; eauto.
  Qed.

  Lemma seq_star_exec_steps_elim {R} (rec: proc R) σhalt ret k:
    seq_star_exec_steps rec k σhalt ret ->
    seq_star (_ <- crash_step; exec_halt rec) σhalt ret.
  Proof.
    intros Hstar.
    induction Hstar as [|??? ? ? k n| ???]; subst.
    - econstructor.
    - econstructor; eauto.
      do 2 eexists; split; eauto.
      do 2 eexists; split; [| econstructor].
      apply exec_partial_equiv_exec_partial_n; eexists; eauto.
    - eapply seq_star_one_more_err.
      right.
      do 2 eexists; split; eauto.
      left.
      apply exec_partial_equiv_exec_partial_n; eexists; eauto.
  Qed.

  Inductive rexec_n {T R} (e: proc T) (rec: proc R) (n : nat) : relation State State unit :=
    | rexec_n_intro σ1 ret n1 n2 n3:
        (n1 + n2 + n3 = n)%nat ->
        (_ <- exec_partial_n e n1;
         _ <- seq_star_exec_steps rec n2;
         _ <- crash_step; _ <- exec_n rec n3; pure tt) σ1 ret ->
        rexec_n e rec n σ1 ret.

  Lemma rexec_equiv_rexec_n {T R} (e: proc T) (rec: proc R) σ1 ret:
    (_ <- exec_partial e; _ <- seq_star (_ <- (crash_step); exec_halt rec);
       _ <- crash_step; _ <- exec rec; pure tt) σ1 ret <->
    exists n, rexec_n e rec n σ1 ret.
  Proof.
    split.
    - destruct ret as [σ2 tt|].
      * intros (tp&σ1a&Hpartial&([]&?&Hstar&([]&?&?&Hexec))).
        apply exec_partial_equiv_exec_partial_n in Hpartial as (n1&?).
        apply seq_star_exec_steps_intro in Hstar as (n2&?); eauto.
        destruct Hexec as (?&?&Hexec&Hpure); inversion Hpure; subst.
        apply exec_equiv_exec_n in Hexec as (n3&?).
        exists (n1 + n2 + n3)%nat; econstructor; eauto.
        repeat (do 2 eexists; split; eauto).
      * intros [Hpartial|(tp&σ1a&Hpartial&Hrest)]. 
        { apply exec_partial_equiv_exec_partial_n in Hpartial as (n1&?).
          exists n1. exists n1 O O.
          ** do 2 rewrite <-plus_n_O. auto.
          ** left; eauto.
        }
        apply exec_partial_equiv_exec_partial_n in Hpartial as (n1&?).
        destruct Hrest as [Hstar|([]&?&Hstar&Hexec)].
        { apply seq_star_exec_steps_intro in Hstar as (n2&?); eauto.
          exists (n1 + n2)%nat. exists n1 n2 O.
          ** rewrite <-plus_n_O. auto.
          ** right. do 2 eexists; split; eauto. left; eauto.
        }
        apply seq_star_exec_steps_intro in Hstar as (n2&?); eauto.
        destruct Hexec as [|([]&?&?&Hexec)].
        { exfalso. eapply crash_non_err; eauto. }
        apply bind_pure_no_err, exec_equiv_exec_n in Hexec as (n3&?).
        exists (n1 + n2 + n3)%nat. exists n1 n2 n3; auto.
        right. do 2 eexists; split; eauto. right. do 2 eexists; split; eauto.
        right. do 2 eexists; split; eauto. left; eauto.
    - intros (n&H). inversion H as [?? n1 n2 n3 Heq Hstep]; subst.
      destruct ret as [σ2 tt|].
      * destruct Hstep as (tp&σ1a&Hpartial&([]&?&Hstar&([]&?&?&Hexec))).
        destruct Hexec as (?&?&?&Hpure). inversion Hpure; subst.
        do 2 eexists; split; eauto.
        { eapply exec_partial_equiv_exec_partial_n; eexists; eauto. }
        do 2 eexists; split; eauto.
        { eapply seq_star_exec_steps_elim; eauto. }
        do 2 eexists; split; eauto.
        do 2 eexists; split; eauto.
        { eapply exec_equiv_exec_n; eexists; eauto. }
      * destruct Hstep as [Hpartial|(tp&σ1a&Hpartial&Hrest)]. 
        { left. eapply exec_partial_equiv_exec_partial_n; eexists; eauto. }
        destruct Hrest as [Hstar|([]&?&Hstar&Hexec)].
        { right. do 2 eexists; split.
          { eapply exec_partial_equiv_exec_partial_n; eexists; eauto. }
          { left. eapply seq_star_exec_steps_elim; eauto. }
        }
        right. do 2 eexists; split; eauto.
        { eapply exec_partial_equiv_exec_partial_n; eexists; eauto. }
        right. do 2 eexists; split; eauto.
        { eapply seq_star_exec_steps_elim; eauto. }
        destruct Hexec as [|([]&?&?&Hexec)].
        { exfalso. eapply crash_non_err; eauto. }
        right. do 2 eexists; split; eauto.
        apply bind_pure_no_err in Hexec.
        left. 
        eapply exec_equiv_exec_n; eauto.
  Qed.


  Lemma rexec_equiv_rexec_n'_val {T R} (e: proc T) (rec: proc R) σ1 σ2:
    ~ rexec e (rec_singleton rec) σ1 Err -> 
    (rexec e (rec_singleton rec) σ1 (Val σ2 tt) <->
    exists n, rexec_n e rec n σ1 (Val σ2 tt)).
  Proof.
    intros Hnoerr.
    split.
    - intros Hrexec; apply rexec_equiv_rexec_n; eauto.
      eapply requiv_no_err_elim in Hrexec; swap 1 3.
      { eassumption. }
      { unfold rexec, exec_recover.
        setoid_rewrite exec_seq_partial_singleton.
        setoid_rewrite <-bind_assoc at 2.
        setoid_rewrite <-seq_unit_sliding_equiv.
        setoid_rewrite bind_assoc.
        reflexivity.
      }
      eauto.
    - intros (n&Hrexec_n).
      eapply requiv_no_err_elim'; swap 1 3.
      { eassumption. }
      { unfold rexec, exec_recover.
        setoid_rewrite exec_seq_partial_singleton.
        setoid_rewrite <-bind_assoc at 2.
        setoid_rewrite <-seq_unit_sliding_equiv.
        setoid_rewrite bind_assoc.
        reflexivity.
      }
      eapply rexec_equiv_rexec_n; eauto.
  Qed.

  Lemma rexec_equiv_rexec_n'_err {T R} (e: proc T) (rec: proc R) σ1:
    (rexec e (rec_singleton rec) σ1 Err <->
    exists n, rexec_n e rec n σ1 Err).
  Proof.
    split.
    - intros Hrexec; apply rexec_equiv_rexec_n; eauto.
      eapply requiv_err_elim in Hrexec.
      { eassumption. }
      { unfold rexec, exec_recover.
        setoid_rewrite exec_seq_partial_singleton.
        setoid_rewrite <-bind_assoc at 2.
        setoid_rewrite <-seq_unit_sliding_equiv.
        setoid_rewrite bind_assoc.
        reflexivity.
      }
    - intros (n&Hrexec_n).
      eapply requiv_err_elim.
      { eapply rexec_equiv_rexec_n; eauto. }
      { symmetry. unfold rexec, exec_recover.
        setoid_rewrite exec_seq_partial_singleton.
        setoid_rewrite <-bind_assoc at 2.
        setoid_rewrite <-seq_unit_sliding_equiv.
        setoid_rewrite bind_assoc.
        reflexivity.
      }
  Qed.

  Definition exec_or_rexec_n {T R} (p : proc T) (rec: proc R) n :=
    (v <- exec_n p n;
     _ <- finish_step;
     pure (Normal v))
    +
    (v <- rexec_n p rec n;
     _ <- fst_lift (puts (fun _ => 1));
     pure (Recovered (existT (fun T => T) _ v))).
  
  Lemma exec_or_rexec_equiv_exec_or_rexec_n {T R} (e: proc T) (rec: proc R) σ1 σ2 out:
    ~ (exec_or_rexec e (rec_singleton rec) σ1 Err) -> 
    (exec_or_rexec e (rec_singleton rec) σ1 (Val σ2 out) <->
    exists n, exec_or_rexec_n e rec n σ1 (Val σ2 out)).
  Proof.
    intros Hno_err. split.
    - intros [Hexec|Hrexec].
      * destruct Hexec as ([]&?&Hexec&Hpure). inversion Hpure; subst.
        eapply exec_equiv_exec_n in Hexec as (n&?).
        exists n. left. do 2 eexists; split; eauto.
      * destruct Hrexec as ([]&?&Hexec&Hpure). inversion Hpure; subst.
        eapply rexec_equiv_rexec_n'_val in Hexec as (n&?).
        { exists n. right. do 2 eexists; split; eauto. }
        { intros Herr. eapply Hno_err. right. econstructor; eauto. }
    - intros (n&[Hexec|Hrexec]).
      * destruct Hexec as ([]&?&Hexec&Hpure). inversion Hpure; subst.
        left. do 2 eexists; split; eauto. eapply exec_equiv_exec_n. eexists; eauto.
      * destruct Hrexec as ([]&?&Hexec&Hpure). inversion Hpure; subst.
        right. do 2 eexists; split; eauto.
        eapply rexec_equiv_rexec_n'_val. 
        { intros Herr. eapply Hno_err. right. econstructor; eauto. }
        { eexists; eauto. }
  Qed.
  
  Fixpoint proc_exec_seq_n {T R} (p: proc_seq T) (rec: proc R) n :=
    match p with
    | Proc_Seq_Nil v =>
      fun s1 ret => n = 5 /\ (pure v) s1 ret
    | Proc_Seq_Bind p f =>
      fun s1 ret =>
        exists n1 n2, (n = (5 + n1) + S n2)%nat /\
        (v <- exec_or_rexec_n p rec n1;
        proc_exec_seq_n (f v) rec n2) s1 ret
    end.

  Lemma proc_exec_seq_equiv_proc_exec_seq_n {T R} (p: proc_seq T) (rec: proc R) σ1 σ2 out:
    ~ (proc_exec_seq p (rec_singleton rec) σ1 Err) -> 
    (proc_exec_seq p (rec_singleton rec) σ1 (Val σ2 out) <->
    exists n, proc_exec_seq_n p rec n σ1 (Val σ2 out)).
  Proof.
    revert σ1. induction p as [| ??? IH]; intros σ1 Hno_err.
    * split; simpl.
      ** intuition eauto.
      ** intros (?&[]); eauto.
    * split.
      ** intros (?&?&Hhd&Htl).
         eapply IH in Htl as (n2&?).
         { eapply exec_or_rexec_equiv_exec_or_rexec_n in Hhd as (n1&?).
           { exists ((5 + n1) + S n2)%nat.
             do 2 eexists; split; eauto.
             do 2 eexists; split; eauto.
           }
           { intros Herr.  eapply Hno_err. left; eauto. }
         }
         { intros Herr. eapply Hno_err. right.
           do 2 eexists; split; eauto.
         }
      ** intros (n&(?&?&?&(?&?&Hhd&Htl))).
         subst.
         do 2 eexists; split.
         { eapply exec_or_rexec_equiv_exec_or_rexec_n; eauto. intros Herr.
           eapply Hno_err. left; eauto. }
         {
           eapply IH; eauto. intros Herr.
           eapply Hno_err. right; eauto.
           do 2 eexists; split; eauto.
           eapply exec_or_rexec_equiv_exec_or_rexec_n; eauto. intros Herr'.
           eapply Hno_err. left; eauto.
         }
  Qed.

End Dynamics.

Arguments exec_halt_noop [Op OpState sem T].
Arguments exec_halt_finish [Op OpState sem T].
Arguments exec_halt_ret [Op OpState sem T].
