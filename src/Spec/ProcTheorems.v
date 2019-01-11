Require Import Setoid.
Require Import Morphisms.
Require Import Proc.
From Classes Require Import Classes.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import Helpers.RelationTheorems.
Require Import Tactical.ProofAutomation.

Import RelationNotations.

Section Dynamics.
  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation rec_seq := (rec_seq Op).
  Notation step := sem.(step).
  Notation crash_step := sem.(crash_step).
  Notation exec_halt := sem.(exec_halt).
  Notation exec_partial := sem.(exec_partial).
  Notation exec := sem.(exec).
  Notation exec_seq_partial := sem.(exec_seq_partial).
  Notation exec_seq := sem.(exec_seq).
  Notation rexec_seq := sem.(rexec_seq).
  Notation exec_recover1 := sem.(exec_recover1).
  Notation exec_recover := sem.(exec_recover).
  Notation exec_recover_partial := sem.(exec_recover_partial).
  Notation rexec := sem.(rexec).
  Notation rexec_partial := sem.(rexec_partial).
  Notation rexec_seq_partial := sem.(rexec_seq_partial).

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
      rew none_plus_r.
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

  (*
  Theorem exec_recover_bind
          `(rec1: proc unit)
          `(rec2: proc unit) :
    exec_recover (Bind rec1 (fun _ => rec2)) <--->
                 (v <- exec_recover rec1;
                    v' <- bind_star (fun v => rexec rec2 rec1) v;
                    exec (rec2)).
  Proof.
    repeat unfold exec_recover, rexec; simpl; norm.
    rew denesting.

    rewrite exec_halt_idem.
    rewrite ?bind_dist_r; norm.

    (* a few abstractions *)
    gen (exec rec1) (exec_halt rec1) crash_step;
      clear rec1;
      intros rec1 rec1_crash crash.

    rew denesting.
    rel_congruence.
    rewrite <- ?bind_assoc.
    rel_congruence; norm.
    rew bind_sliding.
  Qed.
   *)

  (*
  Theorem rexec_to_exec_recover
          `(rec: rec_seq) :
    rexec rec rec ---> exec_recover rec.
  Proof.
    unfold rexec, exec_recover.
    setoid_rewrite <- bind_assoc at 1.
    setoid_rewrite <- bind_assoc at 1.
    rew seq_star1.
  Qed.

  Lemma exec_halt_ret_proc `(rec: proc R):
    exec_halt (Ret tt) ---> exec_halt rec.
  Proof.
    rew exec_halt_ret.
    unfold exec_halt, exec_partial.
    rew<- bind_star_expand.
    Left.
  Qed.

  Lemma exec_halt_ret_recover_fold `(rec: proc R):
    _ <- exec_halt (Ret tt); _ <- crash_step; exec_recover rec ---> exec_recover rec.
  Proof.
    setoid_rewrite (exec_halt_ret_proc rec).
    unfold exec_recover.
    setoid_rewrite <-bind_assoc at 1.
    setoid_rewrite <-bind_assoc at 1.
    rewrite seq_star_fold; eauto.
  Qed.
   *)

End Dynamics.

Arguments exec_halt_noop [Op State sem T].
Arguments exec_halt_finish [Op State sem T].
Arguments exec_halt_ret [Op State sem T].
