Require Import POCS.

Require Import OneDiskAPI.
Require Import TwoDiskAPI.
Require Import TwoDiskTheorems.
Require Import HoareTactics.

(**
ReplicatedDisk provides a single-disk API on top of two disks, handling disk
failures with replication.
*)


Module ReplicatedDisk.

  Import TwoDiskAPI.TwoDisk.

  (* We will be defining procedures called 'read', 'write', etc., so it's
     useful to introduce a shorthand for TwoDiskAPI to be able to refer back
     to the TwoDisk primitive definitions *)
  Module td := TwoDiskAPI.

  Import ProcNotations EqualDecNotation.
  Open Scope proc_scope.

  Definition read (a:addr) : proc Op block :=
    mv0 <- td.read d0 a;
    match mv0 with
    | Working v => Ret v
    | Failed =>
      mv2 <- td.read d1 a;
      match mv2 with
      | Working v => Ret v
      | Failed => Ret block0
      end
    end.

  Definition write (a:addr) (b:block) : proc Op unit :=
    _ <- td.write d0 a b;
    _ <- td.write d1 a b;
    Ret tt.

  Definition size : proc Op nat :=
    msz <- td.size d0;
    match msz with
    | Working sz => Ret sz
    | Failed =>
      msz <- td.size d1;
      match msz with
      | Working sz => Ret sz
      | Failed => Ret 0
      end
    end.

  (** [sizeInit] computes the size during initialization; it may return None if
  the sizes of the underlying disks differ. *)
  Definition sizeInit : proc Op (option nat) :=
    sz1 <- td.size d0;
    sz2 <- td.size d1;
    match sz1 with
    | Working sz1 =>
      match sz2 with
      | Working sz2 =>
        if sz1 == sz2 then Ret (Some sz1) else Ret None
      | Failed => Ret (Some sz1)
      end
    | Failed =>
      match sz2 with
      | Working sz2 => Ret (Some sz2)
      | Failed => Ret None
      end
    end.

  (* Recursively initialize block a and below. For simplicity, we make the disks
  match by setting every block to [block0]. *)
  Fixpoint init_at (a:nat) : proc Op unit :=
    match a with
    | 0 => Ret tt
    | S a =>
      _ <- td.write d0 a block0;
      _ <- td.write d1 a block0;
      init_at a
    end.

  (* Initialize every disk block *)
  Definition init' : proc Op InitStatus :=
    size <- sizeInit;
    match size with
    | Some sz =>
      _ <- init_at sz;
      Ret Initialized
    | None =>
      Ret InitFailed
    end.

  (**
   * Helper theorems and tactics for proofs.
   *)

  Tactic Notation "evar_tuple" ident(a) ident(b) :=
    match goal with
    | [ |- ?aT * ?bT ] =>
      let a := fresh a in
      let b := fresh b in
      evar (a : aT);
      evar (b : bT);
      exact (a, b)
    end.

  Ltac simplify :=
    repeat match goal with
           | |- forall _, _ => intros
           | _ => deex
           | _ => destruct_tuple
           | [ u: unit |- _ ] => destruct u
           | |- _ /\ _ => split; [ solve [auto] | ]
           | |- _ /\ _ => split; [ | solve [auto] ]
           | |- list block => shelve
           | |- disk => shelve
           | |- disk*(disk -> Prop) => evar_tuple d F
           | |- list block*(list block -> Prop) => evar_tuple d F
           | _ => progress simpl in *
           | _ => progress safe_intuition
           | _ => progress subst
           | _ => progress autorewrite with length array in *
           end.

  (* The [finish] tactic tries a number of techniques to solve the goal. *)
  Ltac finish :=
    repeat match goal with
           | _ => solve_false
           | _ => congruence
           | _ => solve [ intuition (subst; eauto; try congruence) ]
           | _ =>
             (* if we can solve all the side conditions automatically, then it's
             safe to run descend and create existential variables *)
             descend; (intuition eauto);
             lazymatch goal with
             | |- proc_hspec _ _ _ => idtac
             | |- proc_rspec _ _ _ _ => idtac
             | _ => fail
             end
           end.

  Ltac step :=
    unshelve (step_proc); simplify; finish.

  (**
   * Specifications and proofs about our implementation of the replicated disk API,
   * without considering our recovery.
   *
   * These intermediate specifications separate reasoning about the
   * implementations from recovery behavior.
   *)

  Theorem both_disks_not_missing : forall (state: State),
      disk0 state ?|= missing ->
      disk1 state ?|= missing ->
      False.
  Proof.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Hint Resolve both_disks_not_missing : false.

  Theorem missing0_implies_any : forall (state: State) P,
      disk0 state ?|= missing ->
      disk0 state ?|= P.
  Proof.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Theorem missing1_implies_any : forall (state: State) P,
      disk1 state ?|= missing ->
      disk1 state ?|= P.
  Proof.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Hint Resolve missing0_implies_any.
  Hint Resolve missing1_implies_any.
  Hint Resolve read_ok write_ok size_ok.

  Theorem read_int_ok : forall a d,
      proc_hspec TDLayer
        (read a)
        (fun state =>
           {|
             pre := disk0 state ?|= eq d /\
                    disk1 state ?|= eq d;
             post :=
               fun state' r =>
                 index d a ?|= eq r /\
                 disk0 state' ?|= eq d /\
                 disk1 state' ?|= eq d;
             alternate :=
               fun state' _ =>
                 disk0 state' ?|= eq d /\
                 disk1 state' ?|= eq d;
           |}).
  Proof.
    unfold read.
    repeat (step; destruct r).
  Qed.

  Hint Resolve read_int_ok.

  Theorem write_int_ok : forall a b d,
      proc_hspec TDLayer
        (write a b)
        (fun state =>
           {|
             pre :=
               disk0 state ?|= eq d /\
               disk1 state ?|= eq d;
             post :=
               fun state' r =>
                 r = tt /\
                 disk0 state' ?|= eq (assign d a b) /\
                 disk1 state' ?|= eq (assign d a b);
             alternate :=
               fun state' _ =>
                 (disk0 state' ?|= eq d /\
                  disk1 state' ?|= eq d) \/
                  ((disk0 state' ?|= eq (assign d a b) /\
                  disk1 state' ?|= eq d)) \/
                 (disk0 state' ?|= eq (assign d a b) /\
                  disk1 state' ?|= eq (assign d a b));
           |}).
  Proof.
    unfold write.
    step.

    destruct r; step.
    descend; intuition eauto.

    step.
    destruct r; (intuition eauto); simplify.
    destruct (lt_dec a (length d)).
    eauto.
    simplify.

    destruct r; step.
    destruct r; step.
  Qed.

  Hint Resolve write_int_ok.

  Theorem size_int_ok d_0 d_1:
    proc_hspec TDLayer
      (size)
      (fun state =>
         {|
           pre :=
             disk0 state ?|= eq d_0 /\
             disk1 state ?|= eq d_1 /\
             length d_0 = length d_1;
           post :=
             fun state' r =>
               r = length d_0 /\
               r = length d_1 /\
               disk0 state' ?|= eq d_0 /\
               disk1 state' ?|= eq d_1;
           alternate :=
             fun state' _ =>
               disk0 state' ?|= eq d_0 /\
               disk1 state' ?|= eq d_1;
         |}).
  Proof.
    unfold size.
    step.
    destruct r; step.
    destruct r; step.
  Qed.

  Hint Resolve size_int_ok.

  Definition equal_after a (d_0 d_1: disk) :=
    length d_0 = length d_1 /\
    forall a', a <= a' -> index d_0 a' = index d_1 a'.

  Theorem le_eq_or_S_le : forall n m,
      n <= m ->
      n = m \/
      S n <= m /\ n <> m.
  Proof.
    intros.
    omega.
  Qed.

  Theorem equal_after_assign : forall a d_0 d_1 b,
      equal_after (S a) d_0 d_1 ->
      equal_after a (assign d_0 a b) (assign d_1 a b).
  Proof.
    unfold equal_after; intuition.
    autorewrite with length; eauto.
    apply le_eq_or_S_le in H; intuition subst.
    destruct (lt_dec a' (length d_0)); autorewrite with array; auto.
    autorewrite with array; auto.
  Qed.

  Hint Resolve equal_after_assign.

  Theorem init_at_ok : forall a d_0 d_1,
      proc_hspec TDLayer
        (init_at a)
        (fun state =>
           {| pre :=
                disk0 state ?|= eq d_0 /\
                disk1 state ?|= eq d_1 /\
                equal_after a d_0 d_1;
              post :=
                fun state' _ =>
                  exists d_0' d_1': disk,
                    disk0 state' ?|= eq d_0' /\
                    disk1 state' ?|= eq d_1' /\
                    equal_after 0 d_0' d_1';
              alternate :=
                fun state' _ => True;
           |}).
  Proof.
    induction a; simpl; intros.
    - step.
    - step.

      step. do 2 especialize IHa.
      destruct r; finish.
      + step; destruct r; simplify; finish.
      + step; destruct r; finish.
  Qed.

  Hint Resolve init_at_ok.

  Theorem sizeInit_ok d_0 d_1 :
    proc_hspec TDLayer
      (sizeInit)
      (fun state =>
         {| pre :=
              disk0 state ?|= eq d_0 /\
              disk1 state ?|= eq d_1;
            post :=
              fun state' r =>
                exists d_0' d_1',
                  disk0 state' ?|= eq d_0' /\
                  disk1 state' ?|= eq d_1' /\
                  match r with
                  | Some sz => length d_0' = sz /\ length d_1' = sz
                  | None => True
                  end;
            alternate :=
              fun state' _ => True;
         |}).
  Proof.
    unfold sizeInit.
    step.
    destruct r.
    step.
    - destruct r.
      + destruct (length d_0 == v).
        * step.
        * step.
      + step.
    - step.
      destruct r.
      + step.
      + step.
  Qed.

  Hint Resolve sizeInit_ok.


  Theorem equal_after_0_to_eq : forall d_0 d_1,
      equal_after 0 d_0 d_1 ->
      d_0 = d_1.
  Proof.
    unfold equal_after; intuition.
    eapply index_ext_eq; intros.
    eapply H1; omega.
  Qed.

  Theorem equal_after_size : forall d_0 d_1,
      length d_0 = length d_1 ->
      equal_after (length d_0) d_0 d_1.
  Proof.
    unfold equal_after; intuition.
    assert (~a' < length d_0) by omega.
    assert (~a' < length d_1) by congruence.
    autorewrite with array; eauto.
  Qed.

  Hint Resolve equal_after_size.
  Hint Resolve equal_after_0_to_eq.

  Theorem init'_ok d_0 d_1:
    proc_hspec TDLayer
      (init')
      (fun state =>
         {| pre :=
              disk0 state ?|= eq d_0 /\
              disk1 state ?|= eq d_1;
            post :=
              fun state' r =>
                match r with
                | Initialized =>
                  exists d_0' d_1',
                  disk0 state' ?|= eq d_0' /\
                  disk1 state' ?|= eq d_1' /\
                  d_0' = d_1'
                | InitFailed =>
                  True
                end;
            alternate :=
              fun state' _ => True;
         |}).
  Proof.
    step.
    spec_intros.
    simpl in H1. repeat deex.
    destruct r; step.
    step.
  Qed.

  Theorem init'_ok_closed:
    proc_hspec TDLayer
      (init')
      (fun state =>
         {| pre := True;
            post :=
              fun state' r =>
                match r with
                | Initialized =>
                  exists d_0' d_1',
                  disk0 state' ?|= eq d_0' /\
                  disk1 state' ?|= eq d_1' /\
                  d_0' = d_1'
                | InitFailed =>
                  True
                end;
            alternate :=
              fun state' _ => True;
         |}).
  Proof.
    spec_intros.
    destruct state0; simplify.
    - eapply proc_hspec_impl; unfold spec_impl; [| eapply (init'_ok d_0)]; simplify.
    - eapply proc_hspec_impl; unfold spec_impl; [| eapply (init'_ok d_0 d_0)]; simplify.
    - eapply proc_hspec_impl; unfold spec_impl; [| eapply (init'_ok d_1)]; simplify.
  Qed.

  (**
   * Recovery implementation.
   *
   * General structure for recovery: essentially, it consists of
   * a loop around [fixup] that terminates after either fixing an out-of-sync
   * disk block or when a disk has failed.
  *)

  (* [fixup] returns a [RecStatus] to implement early termination in [recovery_at]. *)
  Inductive RecStatus :=
  (* continue working, nothing interesting has happened *)
  | Continue
  (* some address has been repaired (or the recovery has exhausted the
     addresses) - only one address can be out of sync and thus only it must be
     recovered. *)
  (* OR, one of the disks has failed, so don't bother continuing recovery since
     the invariant is now trivially satisfied *)
  | RepairDoneOrFailed.

  Definition fixup (a:addr) : proc Op RecStatus :=
    mv0 <- td.read d0 a;
    match mv0 with
    | Working v =>
      mv2 <- td.read d1 a;
      match mv2 with
      | Working v' =>
        if v == v' then
          Ret Continue
        else
          mu <- td.write d1 a v;
          Ret RepairDoneOrFailed
      | Failed => Ret RepairDoneOrFailed
      end
    | Failed => Ret RepairDoneOrFailed
    end.

  (* recursively performs recovery at [a-1], [a-2], down to 0 *)
  Fixpoint recover_at (a:addr) : proc Op unit :=
    match a with
    | 0 => Ret tt
    | S n =>
      s <- fixup n;
      match s with
      | Continue => recover_at n
      | RepairDoneOrFailed => Ret tt
      end
    end.

  Definition Recover : proc Op unit :=
    sz <- size;
    _ <- recover_at sz;
    Ret tt.


  (**
   * Theorems and recovery proofs.
   *)

  Theorem if_lt_dec : forall A n m (a a':A),
      n < m ->
      (if lt_dec n m then a else a') = a.
  Proof.
    intros.
    destruct (lt_dec n m); auto.
    contradiction.
  Qed.

  Theorem disks_eq_inbounds : forall (d: disk) a v v',
      a < length d ->
      index d a ?|= eq v ->
      index d a ?|= eq v' ->
      v = v'.
  Proof.
    intros.
    case_eq (index d a); intros.
    - rewrite H2 in *. simpl in *. congruence.
    - exfalso.
      apply index_not_none in H2; eauto.
  Qed.

  (* To make these specifications precise while also covering both the already
   * synced and diverged disks cases, we keep track of which input state we're
   * in from the input and use it to give an exact postcondition. *)
  Inductive DiskStatus :=
  | FullySynced
  | OutOfSync (a:addr) (b:block).

  Theorem assign_maybe_same : forall (d:disk) a b,
      index d a ?|= eq b ->
      assign d a b = d.
  Proof.
    intros.
    destruct (lt_dec a (length d));
      autorewrite with array;
      auto.
    destruct_with_eqn (index d a); simpl in *; subst; eauto.
    apply index_ext_eq; intros i.
    destruct (lt_dec i (length d)), (a == i);
      subst;
      autorewrite with array;
      auto.
    exfalso; apply index_not_none in Heqo; auto.
  Qed.

  Hint Rewrite assign_maybe_same using (solve [ auto ]) : array.
  Hint Resolve PeanoNat.Nat.lt_neq.
  Hint Resolve disks_eq_inbounds.

  (* we will show that fixup does nothing once the disks are the same *)
  Theorem fixup_equal_ok : forall a d,
      proc_hspec TDLayer
        (fixup a)
        (fun state =>
           {|
             pre :=
               (* for simplicity we only consider in-bounds addresses, though
                  if a is out-of-bounds fixup just might uselessly write to
                  disk and not do anything *)
               a < length d /\
               disk0 state ?|= eq d /\
               disk1 state ?|= eq d;
             post :=
               fun state' r =>
                 disk0 state' ?|= eq d /\
                 disk1 state' ?|= eq d;
             alternate :=
               fun state' _ =>
                 disk0 state' ?|= eq d /\
                 disk1 state' ?|= eq d;
           |}).
  Proof.
    unfold fixup.
    step.

    destruct r; step.

    destruct r; try step.
    destruct (v == v0); subst; try step.

    Unshelve.
    auto.
    exact (fun _ => True).
  Qed.

  Theorem fixup_correct_addr_ok : forall a d b,
      proc_hspec TDLayer
        (fixup a)
        (fun state =>
           {|
             pre :=
               a < length d /\
               disk0 state ?|= eq (assign d a b) /\
               disk1 state ?|= eq d;
             post :=
               fun state' r =>
                 match r with
                 | Continue =>
                   (* could happen if b already happened to be value *)
                   disk0 state' ?|= eq (assign d a b) /\
                   disk1 state' ?|= eq (assign d a b)
                 | RepairDoneOrFailed =>
                   (disk0 state' ?|= eq (assign d a b) /\
                    disk1 state' ?|= eq (assign d a b)) \/
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d)
                 end;
             alternate :=
               fun state' _ =>
                 (disk0 state' ?|= eq (assign d a b) /\
                  disk1 state' ?|= eq (assign d a b)) \/
                 (disk0 state' ?|= eq (assign d a b) /\
                  disk1 state' ?|= eq d) \/
                 (disk0 state' ?|= eq d /\
                  disk1 state' ?|= eq d);
           |}).
  Proof.
    unfold fixup; intros.
    step.

    destruct r; try step.

    destruct r; try step.
    destruct (b == v); subst; try step.

    step.
    destruct r; simplify; finish.
  Qed.

  Theorem fixup_wrong_addr_ok : forall a d b a',
      proc_hspec TDLayer
        (fixup a)
        (fun state =>
           {|
             pre :=
               a < length d /\
               (* recovery, working from end of disk, has not yet reached the
                  correct address *)
               a' < a /\
               disk0 state ?|= eq (assign d a' b) /\
               disk1 state ?|= eq d;
             post :=
               fun state' r =>
                 match r with
                 | Continue =>
                   disk0 state' ?|= eq (assign d a' b) /\
                   disk1 state' ?|= eq d
                 | RepairDoneOrFailed =>
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq (assign d a' b) /\
                    disk1 state' ?|= eq (assign d a' b))
                 end;
             alternate :=
               fun state' _ =>
                 (disk0 state' ?|= eq (assign d a' b) /\
                  disk1 state' ?|= eq d) \/
                 (disk0 state' ?|= eq d /\
                  disk1 state' ?|= eq d);
           |}).
  Proof.
    unfold fixup; intros.
    step.

    destruct r; try step.
    destruct r; try step.

    destruct (v == v0); subst.
    step.

    step.
    Unshelve.
    auto.
    exact (fun _ => True).
  Qed.

  Ltac spec_case pf :=
    eapply proc_hspec_impl; [ unfold spec_impl | solve [ apply pf ] ].


  Theorem fixup_ok : forall a d s,
      proc_hspec TDLayer
        (fixup a)
        (fun state =>
           {|
             pre :=
               a < length d /\
               match s with
               | FullySynced => disk0 state ?|= eq d /\
                               disk1 state ?|= eq d
               | OutOfSync a' b => a' <= a /\
                                  disk0 state ?|= eq (assign d a' b) /\
                                  disk1 state ?|= eq d
               end;
             post :=
               fun state' r =>
                 match s with
                 | FullySynced => disk0 state' ?|= eq d /\
                                 disk1 state' ?|= eq d
                 | OutOfSync a' b =>
                   match r with
                   | Continue =>
                     (a' < a /\
                      disk0 state' ?|= eq (assign d a' b) /\
                      disk1 state' ?|= eq d) \/
                     (disk0 state' ?|= eq (assign d a' b) /\
                      disk1 state' ?|= eq (assign d a' b))
                   | RepairDoneOrFailed =>
                     (disk0 state' ?|= eq d /\
                      disk1 state' ?|= eq d) \/
                     (disk0 state' ?|= eq (assign d a' b) /\
                      disk1 state' ?|= eq (assign d a' b))
                   end
                 end;
             alternate :=
               fun state' _ =>
                 match s with
                 | FullySynced => disk0 state' ?|= eq d /\
                                 disk1 state' ?|= eq d
                 | OutOfSync a' b =>
                   (disk0 state' ?|= eq (assign d a' b) /\
                    disk1 state' ?|= eq (assign d a' b)) \/
                   (disk0 state' ?|= eq (assign d a' b) /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d)
                 end;
           |}).
  Proof.
    spec_intros; simplify.
    destruct s; intuition eauto.
    - spec_case fixup_equal_ok; simplify; finish.
    - apply PeanoNat.Nat.lt_eq_cases in H1; intuition.
      + spec_case (fixup_wrong_addr_ok a d b a0); simplify; finish.
        destruct v; finish.
      + spec_case fixup_correct_addr_ok; simplify; finish.
        split. intuition eauto.
        simplify; finish.
        destruct v; finish.
  Qed.

  Hint Resolve fixup_ok.

  (* Hint Resolve Lt.lt_n_Sm_le. *)

  Theorem recover_at_ok : forall a d s,
      proc_hspec TDLayer
        (recover_at a)
        (fun state =>
           {|
             pre :=
               a <= length d /\
               match s with
               | FullySynced => disk0 state ?|= eq d /\
                               disk1 state ?|= eq d
               | OutOfSync a' b => a' < a /\
                                  disk0 state ?|= eq (assign d a' b) /\
                                  disk1 state ?|= eq d
               end;
             post :=
               fun state' r =>
                 match s with
                 | FullySynced =>
                   disk0 state' ?|= eq d /\
                   disk1 state' ?|= eq d
                 | OutOfSync a' b =>
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq (assign d a' b) /\
                    disk1 state' ?|= eq (assign d a' b))
                 end;
             alternate :=
               fun state' _ =>
                 match s with
                 | FullySynced => disk0 state' ?|= eq d /\
                                 disk1 state' ?|= eq d
                 | OutOfSync a' b =>
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq (assign d a' b) /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq (assign d a' b) /\
                    disk1 state' ?|= eq (assign d a' b))
                 end;
           |}).
  Proof.
    induction a; simpl; intros.
    - step.
      destruct s; simplify.
    - step.
      destruct s; simplify.
      * specialize (IHa d FullySynced).
        simplify; finish.
        destruct r; step.
        omega.
      * split; [intuition; eauto; try omega|].
        simplify; finish.
        destruct r.
        ** spec_intros. simpl in H3. destruct H3.
           *** specialize (IHa d (OutOfSync a0 b)).
               step. omega.
           *** specialize (IHa (assign d a0 b) FullySynced).
               step. autorewrite with length in *; omega.
        ** step.
  Qed.

  Hint Resolve recover_at_ok.

  Definition Recover_spec : _ -> _ -> Specification unit unit State :=
    fun d s state =>
      {|
        pre :=
          match s with
          | FullySynced => disk0 state ?|= eq d /\
                          disk1 state ?|= eq d
          | OutOfSync a b => disk0 state ?|= eq (assign d a b) /\
                             disk1 state ?|= eq d
          end;
        post :=
          fun state' (_:unit) =>
            match s with
            | FullySynced => disk0 state' ?|= eq d /\
                            disk1 state' ?|= eq d
            | OutOfSync a b =>
              (disk0 state' ?|= eq d /\
               disk1 state' ?|= eq d) \/
              (disk0 state' ?|= eq (assign d a b) /\
               disk1 state' ?|= eq (assign d a b))
            end;
        alternate :=
          fun state' (_:unit) =>
            match s with
            | FullySynced => disk0 state' ?|= eq d /\
                            disk1 state' ?|= eq d
            | OutOfSync a b =>
              (disk0 state' ?|= eq d /\
               disk1 state' ?|= eq d) \/
              (disk0 state' ?|= eq (assign d a b) /\
               disk1 state' ?|= eq d) \/
              (disk0 state' ?|= eq (assign d a b) /\
               disk1 state' ?|= eq (assign d a b))
            end;
      |}.

  Inductive rec_prot : Type :=
    | prot_sync1 : rec_prot
    | prot_out : rec_prot
    | prot_sync2 : rec_prot.

  Theorem Recover_rok1 d s :
    proc_hspec TDLayer
      (Recover)
      (Recover_spec d s).
  Proof.
    unfold Recover, Recover_spec; intros.
    spec_intros; simplify.
    destruct s; simplify.
    + step.
      unshelve (step).
      exact d. exact FullySynced. simplify; finish.
      step.
    + step.
      intuition eauto.
      simplify.
      destruct (lt_dec a (length d)).
      * unshelve (step).
        exact d. exact (OutOfSync a b). simplify; finish.
        step.
      * unshelve (step).
        exact d. exact FullySynced. simplify.
        step.
  Qed.

  Theorem Recover_rok2 d a b rp:
    proc_hspec TDLayer
      (Recover)
      (match rp with
       | prot_sync1 => Recover_spec d (FullySynced)
       | prot_out => Recover_spec d (OutOfSync a b)
       | prot_sync2 => Recover_spec (assign d a b) (FullySynced)
       end).
  Proof.
    unfold Recover, Recover_spec; intros.
    spec_intros; simplify.
    destruct rp; simplify.
    + step.
        unshelve (step).
        exact d. exact FullySynced. simplify; finish.
        step.
    + step.
      intuition eauto.
      simplify.
      destruct (lt_dec a (length d)).
      * unshelve (step).
        exact d. exact (OutOfSync a b). simplify; finish.
        step.
      * unshelve (step).
        exact d. exact FullySynced. simplify.
        step.
    + step.
      intuition eauto.
      simplify.
      destruct (lt_dec a (length d)).
      * unshelve (step).
        exact (assign d a b). exact (OutOfSync a b). simplify; finish.
        step.
      * unshelve (step).
        exact (assign d a b). exact (FullySynced). simplify; finish.
        step.
  Qed.

  Theorem Recover_spec_idempotent_crash_step1 d :
    idempotent_crash_step (TDBaseDynamics) (fun (t : unit) => Recover_spec d (FullySynced)).
  Proof.
    unfold idempotent_crash_step; intuition; simplify.
    exists tt; finish.
  Qed.

  Theorem Recover_spec_idempotent_crash_step2 d a b :
    idempotent_crash_step (TDBaseDynamics)
                          (fun rp : rec_prot =>
                             match rp with
                             | prot_sync1 => Recover_spec d (FullySynced)
                             | prot_out => Recover_spec d (OutOfSync a b)
                             | prot_sync2 => Recover_spec (assign d a b) (FullySynced)
                             end).
  Proof.
    unfold idempotent_crash_step; intuition; simplify.
    unfold identity in *; subst.
    destruct a0.
    - exists prot_sync1; simplify; finish.
    - destruct H0; [| destruct H0].
        ** exists (prot_sync1); simplify; finish.
        ** exists (prot_out); simplify; finish.
        ** exists (prot_sync2); simplify; finish.
    - exists prot_sync2; simplify; finish.
  Qed.

  (* As the final step in giving the correctness of the replicated disk
  operations, we prove recovery specs that include the replicated disk Recover
  function. *)

  Definition rd_abstraction (d:OneDisk.State) (state: State) (u: unit) : Prop :=
    disk0 state ?|= eq d /\
    disk1 state ?|= eq d.

  Theorem read_rec_ok :
    forall a d, proc_rspec TDLayer (read a) Recover
                           (refine_spec rd_abstraction (OneDiskAPI.read_spec a) d).
  Proof.
    intros a d.
    eapply proc_hspec_to_rspec; eauto using Recover_spec_idempotent_crash_step1;
      unfold refine_spec, rd_abstraction in *.
    - intros []. eapply Recover_rok1.
    - descend; simplify; intuition eauto.
    - descend; simplify; intuition eauto.
      exists tt. inversion H1. subst; intuition eauto.
    - simplify. exists d; split; eauto.
  Qed.

  Theorem write_rec_ok :
    forall a b d, proc_rspec TDLayer (write a b) Recover
                             (refine_spec rd_abstraction (OneDiskAPI.write_spec a b) d).
  Proof.
    intros a b d.
    eapply proc_hspec_to_rspec; eauto using Recover_spec_idempotent_crash_step2;
      unfold refine_spec, rd_abstraction in *.
    - intros. eapply Recover_rok2.
    - descend; simplify; intuition eauto.
    - intros.
      simpl in *.
      (intuition eauto);
        repeat match goal with
               | [ H: identity _ _ _ |- _ ] => inv_clear H
               end.
      * exists (prot_sync1); simplify; finish.
      * exists (prot_out); simpl.
        intuition eauto.
      * assert (a < length d \/ a >= length d) as [Hlt|Hoob] by omega.
        ** exists (prot_sync2); simplify; finish.
        ** exists (prot_sync1); simplify; finish.
    - unfold rd_abstraction in *; simplify. destruct a0, H0.
      * exists d. simplify; finish.
      * exists d. simplify; finish.
      * exists (assign d a b); simplify; finish.
      * exists (assign d a b); simplify; finish.
  Qed.

  Theorem size_rec_ok :
    forall d, proc_rspec TDLayer (size) Recover
                         (refine_spec rd_abstraction (OneDiskAPI.size_spec) d).
  Proof.
    intros d.
    eapply proc_hspec_to_rspec; eauto using Recover_spec_idempotent_crash_step1;
      unfold refine_spec, rd_abstraction in *.
    - intros. eapply Recover_rok1.
    - descend; simplify; intuition eauto.
    - descend; simplify; intuition eauto.
      exists tt. inv_clear H1. intuition eauto.
    - simplify. exists d; split; eauto.
  Qed.

  Hint Resolve read_rec_ok size_rec_ok write_rec_ok.

  Import Helpers.RelationAlgebra.
  Import RelationNotations.

  Definition Impl_TD_OD: LayerImpl Op OneDisk.Op :=
    {| compile_op := fun (T : Type) (op : OneDisk.Op T) =>
                       match op in (OneDisk.Op T0) return (proc Op T0) with
                       | OneDisk.op_read a => read a
                       | OneDisk.op_write a b => write a b
                       | OneDisk.op_size => size
                       end;
       init := init';
       Layer.recover := Recover |}.


  Lemma one_disk_failure_id x:
    OneDisk.one_disk_failure x x tt.
  Proof. econstructor. Qed.

  Lemma one_disk_failure_id_l r x:
    (OneDisk.one_disk_failure + r)%rel x x tt.
  Proof. left. econstructor. Qed.

  Hint Resolve one_disk_failure_id one_disk_failure_id_l.
  Hint Constructors OneDisk.op_step.

  Lemma compile_refine_TD_OD:
    compile_op_refines_step TDLayer OneDisk.ODLayer Impl_TD_OD rd_abstraction.
  Proof.
    unfold compile_op_refines_step.
    intros T op. destruct op.
    * eapply proc_rspec_crash_refines_op; [ intros; eapply read_rec_ok |..]; simplify; eauto.
      econstructor; destruct (index _ _); eauto.
    * eapply proc_rspec_crash_refines_op; [ intros; eapply write_rec_ok |..]; simplify; eauto.
      intuition; subst; intuition eauto.
    * eapply proc_rspec_crash_refines_op; [ intros; eapply size_rec_ok |..]; simplify; eauto.
  Qed.

  Theorem Recover_noop d :
    proc_rspec TDLayer
      (Recover)
      (Recover)
      (Recover_spec d (FullySynced)).
  Proof.
    eapply proc_hspec_to_rspec; eauto using Recover_spec_idempotent_crash_step1.
    { eapply Recover_rok1. }
    { intros []. eapply Recover_rok1. }
    { simplify. exists tt. inv_clear H1; eauto. }
    { simplify. }
  Qed.

  Lemma recovery_refines_TD_OD:
    recovery_refines_crash_step TDLayer OneDisk.ODLayer Impl_TD_OD rd_abstraction.
  Proof.
    unfold recovery_refines_crash_step.
    eapply proc_rspec_recovery_refines_crash_step; [ eapply Recover_noop|..];
      unfold rd_abstraction; simplify; inversion H0; subst; finish.
  Qed.

  Lemma Refinement_TD_OD: LayerRefinement TDLayer OneDisk.ODLayer.
  Proof.
    unshelve (econstructor).
    - apply Impl_TD_OD.
    - exact rd_abstraction.
    - exact compile_refine_TD_OD.
    - exact recovery_refines_TD_OD.
    - eapply proc_hspec_init_ok; unfold rd_abstraction.
      { eapply init'_ok_closed. }
      { simplify. }
      { simplify; firstorder. }
  Qed.

End ReplicatedDisk.

(*
Print Assumptions ReplicatedDisk.Refinement_TD_OD.
*)
