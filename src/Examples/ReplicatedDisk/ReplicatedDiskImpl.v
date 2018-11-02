Require Import POCS.

Require Import TwoDiskAPI.
Require Import OneDiskAPI.

(**
ReplicatedDisk provides a single-disk API on top of two disks, handling disk
failures with replication.
*)


Module ReplicatedDisk (td : TwoDiskAPI). (* <: OneDiskAPI. *)

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

  (*
  Definition init := then_init td.init init'.
   *)


  (**
   * Helper theorems and tactics for proofs.
   *)

  Theorem exists_tuple2 : forall A B (P: A * B -> Prop),
      (exists a b, P (a, b)) ->
      (exists p, P p).
  Proof.
    intros.
    repeat deex; eauto.
  Qed.

  Tactic Notation "eexist_tuple" ident(a) ident(b) :=
    match goal with
    | [ |- exists (_:?aT * ?bT), _ ] =>
      let a := fresh a in
      let b := fresh b in
      evar (a : aT);
      evar (b : bT);
      exists (a, b);
      subst a;
      subst b
    end.

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
           | |- disk => shelve
           | |- disk*(disk -> Prop) => evar_tuple d F
           | |- exists (_: disk*(disk -> Prop)), _ => eexist_tuple d F
           | |- exists (_: disk*disk), _ => eexist_tuple d_0 d_1
           | |- exists (_: disk*_), _ => apply exists_tuple2
           | _ => progress simpl in *
           | _ => progress safe_intuition
           | _ => progress subst
           | _ => progress autorewrite with upd in *
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
             | |- proc_cspec _ _ _ => idtac
             | _ => fail
             end
           end.
  
  Ltac monad_simpl :=
    repeat match goal with
           | |- proc_cspec _ (Bind (Ret _) _) _ =>
             eapply proc_cspec_expand; [ apply monad_left_id | ]
           | |- proc_cspec _ (Bind (Bind _ _) _) _ =>
             eapply proc_cspec_expand; [ apply monad_assoc | ]
           end.
  
  Ltac step_proc :=
    intros;
    match goal with
    | |- proc_cspec _ (Ret _) _ =>
      eapply ret_cspec
    | |- proc_cspec _ _ _ =>
      monad_simpl;
      eapply proc_cspec_rx; [ solve [ eauto ] | ]
    | [ H: proc_cspec _ ?p _
        |- proc_cspec _ ?p _ ] =>
      eapply proc_cspec_impl; [ unfold spec_impl | eapply H ]
    end;
    intros; simpl;
    cbn [pre post alternate] in *;
    repeat match goal with
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ |- rec_noop _ _ _ ] => eauto
           | [ |- forall _, _ ] => intros
           | [ |- exists (_:unit), _ ] => exists tt
           | [ |- _ /\ _ ] => split; [ solve [ trivial ] | ]
           | [ |- _ /\ _ ] => split; [ | solve [ trivial ] ]
           | _ => solve [ trivial ]
           | _ => progress subst
           | _ => progress autounfold in *
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

  Theorem both_disks_not_missing : forall (state: TwoDiskBaseAPI.State),
      disk0 state ?|= missing ->
      disk1 state ?|= missing ->
      False.
  Proof.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Hint Resolve both_disks_not_missing : false.

  Theorem missing0_implies_any : forall (state: TwoDiskBaseAPI.State) P,
      disk0 state ?|= missing ->
      disk0 state ?|= P.
  Proof.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Theorem missing1_implies_any : forall (state: TwoDiskBaseAPI.State) P,
      disk1 state ?|= missing ->
      disk1 state ?|= P.
  Proof.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Hint Resolve missing0_implies_any.
  Hint Resolve missing1_implies_any.

  Theorem read_int_ok : forall a d,
      proc_cspec TDLayer
        (read a)
        (fun state =>
           {|
             pre := disk0 state ?|= eq d /\
                    disk1 state ?|= eq d;
             post :=
               fun state' r =>
                 diskGet d a ?|= eq r /\
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
      proc_cspec TDLayer
        (write a b)
        (fun state =>
           {|
             pre :=
               disk0 state ?|= eq d /\
               disk1 state ?|= eq d;
             post :=
               fun state' r =>
                 r = tt /\
                 disk0 state' ?|= eq (diskUpd d a b) /\
                 disk1 state' ?|= eq (diskUpd d a b);
             alternate :=
               fun state' _ =>
                 (disk0 state' ?|= eq d /\
                  disk1 state' ?|= eq d) \/
                 (a < diskSize d /\
                  disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq d) \/
                 (disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq (diskUpd d a b));
           |}).
  Proof.
    unfold write.
    step.

    destruct r; step.
    descend; intuition eauto.

    step.
    destruct r; (intuition eauto); simplify.
    destruct (lt_dec a (diskSize d)).
    eauto.
    simplify.

    destruct r; step.
  Qed.

  Hint Resolve write_int_ok.

  Theorem size_int_ok d_0 d_1:
    proc_cspec TDLayer
      (size)
      (fun state =>
         {|
           pre :=
             disk0 state ?|= eq d_0 /\
             disk1 state ?|= eq d_1 /\
             diskSize d_0 = diskSize d_1;
           post :=
             fun state' r =>
               r = diskSize d_0 /\
               r = diskSize d_1 /\
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
    diskSize d_0 = diskSize d_1 /\
    forall a', a <= a' -> diskGet d_0 a' = diskGet d_1 a'.

  Theorem le_eq_or_S_le : forall n m,
      n <= m ->
      n = m \/
      S n <= m /\ n <> m.
  Proof.
    intros.
    omega.
  Qed.

  Theorem equal_after_diskUpd : forall a d_0 d_1 b,
      equal_after (S a) d_0 d_1 ->
      equal_after a (diskUpd d_0 a b) (diskUpd d_1 a b).
  Proof.
    unfold equal_after; intuition.
    autorewrite with upd; eauto.
    apply le_eq_or_S_le in H; intuition subst.
    destruct (lt_dec a' (diskSize d_0)); autorewrite with upd.
    assert (a' < diskSize d_1) by congruence; autorewrite with upd; auto.
    assert (~a' < diskSize d_1) by congruence; autorewrite with upd; auto.
    autorewrite with upd; eauto.
  Qed.

  Hint Resolve equal_after_diskUpd.

  Ltac especialize H :=
    match type of H with
     |  forall (_ : ?T), _  =>
        let a := fresh "esp" in
        evar (a: T);
        let a' := eval unfold a in a in
            clear a; specialize (H a')
    end.
            

  Theorem init_at_ok : forall a d_0 d_1,
      proc_cspec TDLayer
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
    proc_cspec TDLayer
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
                  | Some sz => diskSize d_0' = sz /\ diskSize d_1' = sz
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
      + destruct (diskSize d_0 == v).
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
    eapply disk_ext_eq; intros.
    eapply H1; omega.
  Qed.

  Theorem equal_after_size : forall d_0 d_1,
      diskSize d_0 = diskSize d_1 ->
      equal_after (diskSize d_0) d_0 d_1.
  Proof.
    unfold equal_after; intuition.
    assert (~a' < diskSize d_0) by omega.
    assert (~a' < diskSize d_1) by congruence.
    autorewrite with upd; eauto.
  Qed.

  Hint Resolve equal_after_size.
  Hint Resolve equal_after_0_to_eq.

  Theorem init'_ok d_0 d_1:
    proc_cspec TDLayer
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
    unfold init.
    step.
    spec_intros.
    simpl in H1. repeat deex.
    destruct r; step.
    step.
  Qed.

  Hint Resolve init'_ok.

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
      a < diskSize d ->
      diskGet d a ?|= eq v ->
      diskGet d a ?|= eq v' ->
      v = v'.
  Proof.
    intros.
    case_eq (diskGet d a); intros.
    - rewrite H2 in *. simpl in *. congruence.
    - exfalso.
      eapply disk_inbounds_not_none; eauto.
  Qed.

  (* To make these specifications precise while also covering both the already
   * synced and diverged disks cases, we keep track of which input state we're
   * in from the input and use it to give an exact postcondition. *)
  Inductive DiskStatus :=
  | FullySynced
  | OutOfSync (a:addr) (b:block).

  Theorem diskUpd_maybe_same : forall (d:disk) a b,
      diskGet d a ?|= eq b ->
      diskUpd d a b = d.
  Proof.
    intros.
    destruct (diskGet d a) eqn:?; simpl in *; subst;
      autorewrite with upd;
      auto.
  Qed.

  Hint Rewrite diskUpd_maybe_same using (solve [ auto ]) : upd.
  Hint Resolve PeanoNat.Nat.lt_neq.
  Hint Resolve disks_eq_inbounds.

  (* we will show that fixup does nothing once the disks are the same *)
  Theorem fixup_equal_ok : forall a d,
      proc_cspec TDLayer
        (fixup a)
        (fun state =>
           {|
             pre :=
               (* for simplicity we only consider in-bounds addresses, though
                  if a is out-of-bounds fixup just might uselessly write to
                  disk and not do anything *)
               a < diskSize d /\
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
      proc_cspec TDLayer
        (fixup a)
        (fun state =>
           {|
             pre :=
               a < diskSize d /\
               disk0 state ?|= eq (diskUpd d a b) /\
               disk1 state ?|= eq d;
             post :=
               fun state' r =>
                 match r with
                 | Continue =>
                   (* could happen if b already happened to be value *)
                   disk0 state' ?|= eq (diskUpd d a b) /\
                   disk1 state' ?|= eq (diskUpd d a b)
                 | RepairDoneOrFailed =>
                   (disk0 state' ?|= eq (diskUpd d a b) /\
                    disk1 state' ?|= eq (diskUpd d a b)) \/
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d)
                 end;
             alternate :=
               fun state' _ =>
                 (disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq (diskUpd d a b)) \/
                 (disk0 state' ?|= eq (diskUpd d a b) /\
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
      proc_cspec TDLayer
        (fixup a)
        (fun state =>
           {|
             pre :=
               a < diskSize d /\
               (* recovery, working from end of disk, has not yet reached the
                  correct address *)
               a' < a /\
               disk0 state ?|= eq (diskUpd d a' b) /\
               disk1 state ?|= eq d;
             post :=
               fun state' r =>
                 match r with
                 | Continue =>
                   disk0 state' ?|= eq (diskUpd d a' b) /\
                   disk1 state' ?|= eq d
                 | RepairDoneOrFailed =>
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
                    disk1 state' ?|= eq (diskUpd d a' b))
                 end;
             alternate :=
               fun state' _ =>
                 (disk0 state' ?|= eq (diskUpd d a' b) /\
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
    eapply proc_cspec_impl; [ unfold spec_impl | solve [ apply pf ] ].


  Theorem fixup_ok : forall a d s,
      proc_cspec TDLayer
        (fixup a)
        (fun state =>
           {|
             pre :=
               a < diskSize d /\
               match s with
               | FullySynced => disk0 state ?|= eq d /\
                               disk1 state ?|= eq d
               | OutOfSync a' b => a' <= a /\
                                  disk0 state ?|= eq (diskUpd d a' b) /\
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
                      disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq d) \/
                     (disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq (diskUpd d a' b))
                   | RepairDoneOrFailed =>
                     (disk0 state' ?|= eq d /\
                      disk1 state' ?|= eq d) \/
                     (disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq (diskUpd d a' b))
                   end
                 end;
             alternate :=
               fun state' _ =>
                 match s with
                 | FullySynced => disk0 state' ?|= eq d /\
                                 disk1 state' ?|= eq d
                 | OutOfSync a' b =>
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
                    disk1 state' ?|= eq (diskUpd d a' b)) \/
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
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
      + spec_case fixup_wrong_addr_ok; simplify; finish.
        split. intuition eauto.
        simplify; finish.
        destruct v; finish.
      + spec_case fixup_correct_addr_ok; simplify; finish.
        split. intuition eauto.
        simplify; finish.
        destruct v; finish.
  Qed.

  Hint Resolve fixup_ok.

  (* Hint Resolve Lt.lt_n_Sm_le. *)

  Theorem recover_at_ok : forall a d s,
      proc_cspec TDLayer
        (recover_at a)
        (fun state =>
           {|
             pre :=
               a <= diskSize d /\
               match s with
               | FullySynced => disk0 state ?|= eq d /\
                               disk1 state ?|= eq d
               | OutOfSync a' b => a' < a /\
                                  disk0 state ?|= eq (diskUpd d a' b) /\
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
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
                    disk1 state' ?|= eq (diskUpd d a' b))
                 end;
             alternate :=
               fun state' _ =>
                 match s with
                 | FullySynced => disk0 state' ?|= eq d /\
                                 disk1 state' ?|= eq d
                 | OutOfSync a' b =>
                   (disk0 state' ?|= eq d /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
                    disk1 state' ?|= eq d) \/
                   (disk0 state' ?|= eq (diskUpd d a' b) /\
                    disk1 state' ?|= eq (diskUpd d a' b))
                 end;
           |}).
  Proof.
    induction a; simpl; intros.
    - step.
      destruct s; simplify.
    - step.
      destruct s; simplify.
      * specialize (IHa d FullySynced).
        split; intuition eauto.
        destruct r; step.
        omega.
      * split; [intuition; eauto; try omega|].
        simplify; finish.
        destruct r.
        ** spec_intros. simpl in H3. destruct H3.
           *** specialize (IHa d (OutOfSync a0 b)).
               step. omega.
           *** specialize (IHa (diskUpd d a0 b) FullySynced).
               step. intuition.
        ** step.
  Qed.

  Hint Resolve recover_at_ok.

  Definition Recover_spec : _ -> _ -> Specification unit unit TwoDiskBaseAPI.State :=
    fun d s state =>
      {|
        pre :=
          match s with
          | FullySynced => disk0 state ?|= eq d /\
                          disk1 state ?|= eq d
          | OutOfSync a b => a < diskSize d /\
                            disk0 state ?|= eq (diskUpd d a b) /\
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
              (disk0 state' ?|= eq (diskUpd d a b) /\
               disk1 state' ?|= eq (diskUpd d a b))
            end;
        alternate :=
          fun state' (_:unit) =>
            match s with
            | FullySynced => disk0 state' ?|= eq d /\
                            disk1 state' ?|= eq d
            | OutOfSync a b =>
              (disk0 state' ?|= eq d /\
               disk1 state' ?|= eq d) \/
              (disk0 state' ?|= eq (diskUpd d a b) /\
               disk1 state' ?|= eq d) \/
              (disk0 state' ?|= eq (diskUpd d a b) /\
               disk1 state' ?|= eq (diskUpd d a b))
            end;
      |}.

  Inductive rec_prot : Type :=
    | stable_sync : rec_prot
    | stable_out : rec_prot
    | try_recv : rec_prot.

  Theorem Recover_rok1 d s :
    proc_cspec TDLayer
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
      unshelve (step).
      exact d. exact (OutOfSync a b). simplify; finish.
      step.
  Qed.

  Theorem Recover_rok2 d a b rp:
    proc_cspec TDLayer
      (Recover)
      (match rp with
       | stable_sync => Recover_spec d (FullySynced)
       | stable_out => Recover_spec d (OutOfSync a b)
       | try_recv => Recover_spec (diskUpd d a b) (OutOfSync a b)
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
      unshelve (step).
      exact d. exact (OutOfSync a b). simplify; finish.
      step.
    + step.
      intuition eauto.
      simplify.
      unshelve (step).
      exact (diskUpd d a b). exact (OutOfSync a b). simplify; finish.
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
                             | stable_sync => Recover_spec d (FullySynced)
                             | stable_out => Recover_spec d (OutOfSync a b)
                             | try_recv => Recover_spec (diskUpd d a b) (OutOfSync a b)
                             end).
  Proof.
    unfold idempotent_crash_step; intuition; simplify.
    destruct a0.
    - exists stable_sync; simplify; finish.
    - destruct H0; [| destruct H0].
        ** exists (stable_sync); simplify; finish.
        ** exists (stable_out); simplify; finish.
        ** exists (try_recv); simplify; finish.
    - destruct H0; [| destruct H0].
      ** exists (try_recv). simplify; finish.
      ** simplify. exists (try_recv). simplify; finish.
      ** simplify. exists (try_recv). simplify; finish.
  Qed.

  (*
  Hint Resolve Recover_spec_idempotent_crash_step2.
   *)

  (* TODO: not sure this is the right level to prove this looping lemma *)
  (* This proof combines your proof that recovery is correct and that its
  specification is idempotent to show recovery is correct even if re-run on
  every crash. *)
  (*
  Theorem Recover_ok :
    proc_loopspec
      Recover_spec
      (Recover)
      td.recover
      td.abstr.
  Proof.
    eapply idempotent_loopspec; simpl.
    - apply Recover_rok.
    - apply Recover_spec_idempotent.
  Qed.
   *)

  (*
  Hint Resolve Recover_rok.
   *)


  (* As the final step in giving the correctness of the replicated disk
  operations, we prove recovery specs that include the replicated disk Recover
  function. *)

  Definition rd_abstraction (d:OneDiskAPI.State) (state: TwoDiskBaseAPI.State)  (_ :unit) : Prop :=
    disk0 state ?|= eq d /\
    disk1 state ?|= eq d.

  Theorem read_rec_ok :
    forall a du, proc_rspec TDLayer (read a) Recover (refine_spec rd_abstraction (read_spec a) du).
  Proof.
    intros a (d&[]).
    eapply proc_cspec_to_rspec; eauto using Recover_spec_idempotent_crash_step1. 
    - intros []. eapply Recover_rok1.
    - unfold refine_spec, rd_abstraction in *; descend; simplify; intuition eauto.
    - unfold refine_spec, rd_abstraction in *; descend; simplify; intuition eauto.
      exists tt. inversion H0. subst; intuition eauto.
    - simplify. exists d; split; eauto.
      unfold rd_abstraction in *; descend; simplify; intuition eauto.
  Qed.

  Theorem write_rec_ok :
    forall a b du, proc_rspec TDLayer (write a b)
                              Recover (refine_spec rd_abstraction (write_spec a b) du).
  Proof.
    intros a b (d&[]).
    eapply proc_cspec_to_rspec; eauto using Recover_spec_idempotent_crash_step2. 
    - intros. eapply Recover_rok2.
    - unfold refine_spec, rd_abstraction in *; descend; simplify; intuition eauto.
    - unfold refine_spec, rd_abstraction in *; descend; simplify; intuition eauto;
       inversion H0; subst.
      * exists (stable_sync); simplify; finish.
      * exists (stable_out); simplify; finish.
      * assert (a < diskSize d \/ a >= diskSize d) as [Hlt|Hoob] by omega.
        ** exists (try_recv); simplify; finish.
        ** exists (stable_sync); simplify; finish.
    - unfold rd_abstraction in *; simplify. destruct a0.
      * destruct H0. exists d. simplify; finish.
      * destruct H0.
           *** exists d. simplify; finish.
           *** exists (diskUpd d a b); simplify; finish.
      * destruct H0; exists (diskUpd d a b); simplify; finish.
  Qed.

  Theorem size_rec_ok :
    forall du, proc_rspec TDLayer (size) Recover (refine_spec rd_abstraction (size_spec) du).
  Proof.
    intros (d&[]).
    eapply proc_cspec_to_rspec; eauto using Recover_spec_idempotent_crash_step1.
    - intros. eapply Recover_rok1.
    - unfold refine_spec, rd_abstraction in *; descend; simplify; intuition eauto.
    - unfold refine_spec, rd_abstraction in *; descend; simplify; intuition eauto.
      exists tt. inversion H0. subst; intuition eauto.
    - simplify. exists d; split; eauto.
      unfold rd_abstraction in *; descend; simplify; intuition eauto.
  Qed.

  Hint Resolve read_rec_ok size_rec_ok write_rec_ok.

  Import Helpers.RelationAlgebra.
  Import RelationNotations.

  (*
  Theorem recover_noop : rec_noop TDLayer recover eq.
  Proof.
    unfold rec_noop. intros T v.
    split.
    - firstorder.
    - unfold rexec. unfold exec_crash. rewrite bind_left_id.
      unfold spec_rexec. simpl. rewrite bind_identity1.
      unfold exec_recover.
  _ <- seq_star (_ <- exec_crash TDBaseDynamics recover; TDBaseDynamics.(crash_step));
      intros s s' []. unfold rex simpl.
    eapply spec_impl_relations.
    2:{ idtac. unfold recover.
        split.
        simpl. eauto. auto.
        step_proc.
    Focus 2.

    [| apply Recover_spec]. proc_ok_impl.
    simpl.
    eapply rec_noop_compose; eauto; simpl.
    autounfold; unfold rd_abstraction, Recover_spec; simplify.
    exists state0', FullySynced; intuition eauto.
  Qed.
   *)

  Definition Impl_TD_OD: LayerImpl Op OneDiskOp :=
    {| compile_op := fun (T : Type) (op : OneDiskOp T) =>
                       match op in (OneDiskOp T0) return (proc Op T0) with
                       | op_read a => read a
                       | op_write a b => write a b
                       | op_size => size
                       end;
       init := init';
       Layer.recover := Recover |}.

  Lemma proc_rspec_refine_exec Op (L: Layer Op) AState A T R (p: proc Op T) (rec: proc Op R)
        spec abstr x:
    (forall (t: AState * A), proc_rspec L p rec (refine_spec abstr spec t)) ->
    (forall sO sT, abstr sO sT tt -> (spec x sO).(pre)) ->
    _ <- abstr; exec L p ---> v <- spec_exec (spec x); _ <- abstr; pure v.
  Proof.
    intros Hprspec Habstr_pre.
    intros sO sT b ([]&sTstart&Hrd&Hexec).
    destruct (Hprspec (sO, x)).
    eapply H in Hexec. simpl in Hexec.
    clear -Hrd Hexec Habstr_pre.
    edestruct Hexec; eauto. simpl. intuition; eauto.
    do 2 eexists; intuition.
    simplify. intros ?. simplify. finish.
    do 2 eexists. split; eauto. finish. unfold pure; auto.
  Qed.

  Lemma proc_rspec_refine_rec Op (L: Layer Op) AState A T R (p: proc Op T) (rec: proc Op R)
        spec abstr x:
    (forall (t: AState * A), proc_rspec L p rec (refine_spec abstr spec t)) ->
    (forall sO sT, abstr sO sT tt -> (spec x sO).(pre)) ->
    _ <- abstr; rexec L p rec ---> v <- spec_aexec (spec x); _ <- abstr; pure v.
  Proof.
    intros Hprspec Habstr_pre.
    intros sO sT b ([]&sTstart&Hrd&Hexec).
    destruct (Hprspec (sO, x)).
    eapply H0 in Hexec. simpl in Hexec.
    clear -Hrd Hexec Habstr_pre.
    edestruct Hexec; eauto. simpl. intuition; eauto.
    do 2 eexists; intuition.
    simplify. intros ?. simplify. finish.
    do 2 eexists. split; eauto. finish. unfold pure; auto.
  Qed.

  Lemma proc_rspec_crash_refines Op1 Op2 (L: Layer Op1) (O: Layer Op2)
            A T (p: proc Op1 T) (rec: proc Op1 unit)
        spec abstr x op:
    (forall (t: _ * A), proc_rspec L p rec (refine_spec abstr spec t)) ->
    (forall sO sT, abstr sO sT tt -> (spec x sO).(pre)) ->
    (spec_exec (spec x) ---> exec O (Prim op)) ->
    (spec_aexec (spec x) ---> O.(crash_step) + (_ <- O.(step) op; O.(crash_step))) ->
    crash_refines abstr L p rec (O.(step) op)
                  (O.(crash_step) + (_ <- O.(step) op; O.(crash_step))).
  Proof.
    intros ?? He Ha. unfold crash_refines, refines. split.
    - setoid_rewrite <-He. eapply proc_rspec_refine_exec; eauto.
    - setoid_rewrite <-Ha. eapply proc_rspec_refine_rec; eauto.
  Qed.

  Lemma one_disk_failure_id_l r x:
    (one_disk_failure + r)%rel x x tt.
  Proof. left. econstructor. Qed.

  Hint Resolve one_disk_failure_id_l.

  Lemma compile_refine_TD_OD:
    compile_op_refines_step TDLayer ODLayer Impl_TD_OD rd_abstraction.
  Proof.
    unfold compile_op_refines_step.
    intros T op. destruct op;
    unshelve (eapply proc_rspec_crash_refines; simpl; eauto); eauto using tt;
      simplify; unfold spec_exec, spec_aexec; intros ????; simplify.
    * econstructor; destruct (diskGet _ _); eauto.
    * do 2 econstructor.
    * intuition; subst; eauto.
      right. econstructor. subst. eexists. split; [| econstructor]. econstructor; auto.
    * econstructor.
  Qed.

  (*
  Lemma Refinement_TD_OD: LayerRefinement TDLayer ODLayer.
  Proof.
    unshelve (econstructor).
    - apply Impl_TD_OD. 
    - exact rd_abstraction.
    refine {| impl := Impl_TD_OD;
              absr := rd_abstraction
           |}.
    - 
    econstructor.
    split.
   *)

(*
  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    intros.
    eapply then_init_compose; eauto.
    eapply proc_spec_weaken; eauto.
    unfold spec_impl; intros.
    destruct state; simpl in *.

    - exists (d_0, d_1); simpl; intuition eauto.
      unfold rd_abstraction.
      destruct v; repeat deex; eauto.
    - exists (d_0, d_0); simpl; intuition eauto.
      unfold rd_abstraction.
      destruct v; repeat deex; eauto.
    - exists (d_1, d_1); simpl; intuition eauto.
      unfold rd_abstraction.
      destruct v; repeat deex; eauto.
  Qed.
*)


  (*
  Theorem read_ok : forall a, proc_ok TDLayer (read a) recover (read_spec a).
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    eapply compose_recovery; eauto; simplify.
    unfold rd_abstraction in *; descend; intuition eauto.
    exists (state2, FullySynced); simplify; finish.
  Qed.

  Theorem write_ok : forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    eapply compose_recovery; eauto; simplify.
    rename state2 into d.
    unfold rd_abstraction in *; descend; intuition eauto.
    - exists (d, FullySynced); simplify; intuition eauto.
    - exists (d, OutOfSync a v); simplify; intuition eauto.
    - exists (diskUpd d a v, FullySynced); simplify; intuition eauto.
  Qed.

  Theorem size_ok : proc_spec size_spec size recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    (* simplify is a bit too aggressive about existential variables here, so we
    provide some manual simplification here *)
    eapply compose_recovery; eauto.
    intros; apply exists_tuple2.
    destruct a; simpl in *.
    rename s into d.
    unfold rd_abstraction in *; simplify.
    exists d, d; intuition eauto.
    simplify.
    exists d, FullySynced; simplify; finish.
  Qed.
   *)


End ReplicatedDisk.
