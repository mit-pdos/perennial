(*
From RecoveryRefinement Require Import Lib.

Require Import OneDiskAPI.
Require Import TwoDiskAPI.

(**
ReplicatedDisk provides a single-disk API on top of two disks, handling disk
failures with replication.
*)


Module ReplicatedDisk.

  Import TwoDiskAPI.TwoDisk.

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


  Definition equal_after a (d_0 d_1: disk) :=
    length d_0 = length d_1 /\
    forall a', a <= a' -> index d_0 a' = index d_1 a'.

  Theorem le_eq_or_S_le : forall n m,
      n <= m ->
      n = m \/
      S n <= m /\ n <> m.
  Proof.
    intros.
    lia.
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

  Theorem equal_after_0_to_eq : forall d_0 d_1,
      equal_after 0 d_0 d_1 ->
      d_0 = d_1.
  Proof.
    unfold equal_after; intuition.
    eapply index_ext_eq; intros.
    eapply H1; lia.
  Qed.

  Theorem equal_after_size : forall d_0 d_1,
      length d_0 = length d_1 ->
      equal_after (length d_0) d_0 d_1.
  Proof.
    unfold equal_after; intuition.
    assert (~a' < length d_0) by lia.
    assert (~a' < length d_1) by congruence.
    autorewrite with array; eauto.
  Qed.

  Hint Resolve equal_after_size.
  Hint Resolve equal_after_0_to_eq.

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
    intros d a v v' Hlt Hm1 Hm2.
    case_eq (index d a); intros.
    - rewrite H in Hm1 Hm2. simpl in *. congruence.
    - exfalso.
      apply index_not_none in H; eauto.
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

  (* As the final step in giving the correctness of the replicated disk
  operations, we prove recovery specs that include the replicated disk Recover
  function. *)

  Definition rd_abstraction (d:D.State) (state: State) (u: unit) : Prop :=
    disk0 state ?|= eq d /\
    disk1 state ?|= eq d.

  Import Helpers.RelationAlgebra.
  Import RelationNotations.

  Definition Impl_TD_OD: LayerImpl Op D.Op :=
    {| compile_op := fun (T : Type) (op : D.Op T) =>
                       match op in (D.Op T0) return (proc Op T0) with
                       | D.op_read a => read a
                       | D.op_write a b => write a b
                       | D.op_size => size
                       end;
       Layer.recover := Seq_Cons (Recover) (Seq_Nil) |}.

  (*
  Lemma Refinement_TD_OD: LayerRefinement TDLayer D.ODLayer.
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
  Defined.
   *)

End ReplicatedDisk.
*)