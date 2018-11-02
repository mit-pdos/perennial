Require Import POCS.
Require Import TwoDiskAPI.
Require Import TwoDiskBaseAPI.


Module TwoDisk (b : TwoDiskBaseAPI) <: TwoDiskAPI.

  (*
  Definition init := b.init.
  *)
  Definition read := b.read.
  Definition write := b.write.
  Definition size := b.size.
  Definition recover:= b.recover.

  (*
  Definition abstr := b.abstr.
   *)

  Ltac inv_step :=
    match goal with
    | [ H: op_step _ _ _ _ |- _ ] =>
      inversion H; subst; clear H;
      repeat sigT_eq;
      safe_intuition
    end.

  Ltac inv_bg :=
    match goal with
    | [ H: bg_failure _ _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

  Theorem maybe_holds_stable : forall state state' F0 F1 i,
    get_disk (other i) state ?|= F0 ->
    get_disk i state ?|= F1 ->
    bg_failure state state' tt ->
    get_disk (other i) state' ?|= F0 /\
    get_disk i state' ?|= F1.
  Proof.
    intros.
    destruct i; inv_bg; simpl in *; eauto.
  Qed.

  (* FIXME: this should be in tactical but was deleted by accident *)
  Ltac destruct_tuple :=
    match goal with
    | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
      let a := fresh a in
      let b := fresh b in
      destruct p as [a b]
    | [ |- context[let '(a, b) := ?p in _] ] =>
      let a := fresh a in
      let b := fresh b in
      destruct p as [a b]
    end.

  Ltac cleanup :=
    repeat match goal with
           | [ |- forall _, _ ] => intros
           | |- _ /\ _ => split; [ solve [ eauto || congruence ] | ]
           | |- _ /\ _ => split; [ | solve [ eauto || congruence ] ]
           | [ H: Working _ = Working _ |- _ ] => inversion H; subst; clear H
           | [ H: bg_failure _ _ _ |- _ ] =>
             eapply maybe_holds_stable in H;
             [ | solve [ eauto ] | solve [ eauto ] ]; destruct_ands
           | [ H: _ ?|= eq _, H': _ = Some _ |- _ ] =>
                    pose proof (holds_some_inv_eq _ H' H); clear H
           | [ H: ?A * ?B |- _ ] => destruct H
           | [ H: DiskResult _ |- _ ] => destruct H
           | _ => deex
           | _ => destruct_tuple
           | _ => progress autounfold in *
           | _ => progress simpl in *
           | _ => progress subst
           | _ => progress safe_intuition
           | _ => solve [ eauto ]
           | _ => congruence
           | _ => inv_step
           | H: context[match ?expr with _ => _ end] |- _ =>
             destruct expr eqn:?; [ | solve [ repeat cleanup ] ]
           | H: context[match ?expr with _ => _ end] |- _ =>
             destruct expr eqn:?; [ solve [ repeat cleanup ] | ]
           end.

  Ltac prim :=
    intros;
    eapply proc_cspec_impl; [ unfold spec_impl | eauto ]; eexists;
    intuition eauto; cleanup;
    intuition eauto; cleanup.

  Hint Resolve holds_in_some_eq.
  Hint Resolve holds_in_none_eq.
  Hint Resolve pred_missing.

  (*
  Hint Unfold combined_step.
   *)


  (*
  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eauto.
  Qed.
   *)

  Hint Resolve tt.

  Theorem read_ok : forall i a dF, proc_cspec TDBaseDynamics (read i a) (read_spec i a dF).
  Proof.
    unshelve prim; eauto.
  Qed.

  Ltac destruct_all :=
    repeat match goal with
           | _ => solve [ auto ]
           | [ i: diskId |- _ ] => destruct i
           | [ |- context[match ?s with
                         | BothDisks _ _ => _
                         | OnlyDisk0 _ => _
                         | OnlyDisk1 _ => _
                         end] ] => destruct s
           | _ => simpl in *
           end.


  Theorem write_ok : forall i a v dF, proc_cspec TDBaseDynamics (write i a v) (write_spec i a v dF).
  Proof.
    unshelve prim; eauto;
      try solve [ destruct_all ].
    destruct (le_dec (S a) (diskSize d0)).
    destruct_all.
    rewrite diskUpd_oob_noop by omega.
    destruct_all.
  Qed.

  Theorem size_ok : forall i dF, proc_cspec TDBaseDynamics (size i) (size_spec i dF).
  Proof.
    unshelve prim.
  Qed.

  Theorem recover_noop : rec_noop TDBaseDynamics recover eq.
  Proof.
    eauto.
  Qed.

End TwoDisk.
