(* TODO: figure out a way to make this mix-in-able for anything building on Heap *)

From iris.algebra Require Import auth gmap frac agree.
Require Import Helpers.RelationTheorems.
From iris.algebra Require Export functions csum.
From iris.base_logic.lib Require Export invariants.
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting Count_Heap CSL.ThreadReg.
From iris.proofmode Require Export tactics.

From RecoveryRefinement.Goose Require Import Machine GoZeroValues Heap GoLayer.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.

Set Default Proof Using "Type".

Import Data.
Import Filesys.FS.

Notation heap_inG := (gen_heapG (sigT Ptr) (sigT ptrRawModel)).

Class gooseG Σ :=
  GooseG {
      go_invG : invG Σ;
      model :> GoModel;
      model_wf :> GoModelWf model;
      go_heap_inG :> heap_inG Σ;
      (* Maybe actually we do want a gmap version for these *)
      go_fs_inG :> gen_heapG string (List.list byte) Σ;
      go_fds_inG :> gen_heapG File (List.list byte) Σ;
      go_treg_inG :> tregG Σ;
    }.

Definition pull_lock :=
    (λ v : option {x : Ptr.ty & ptrModel x},
       match v with
       | Some v =>
           let (x, p) := v in
           match x as t return (ptrModel t → option (LockStatus * {x : Ptr.ty & ptrRawModel x})) with
           | Ptr.Heap T => λ p0 : ptrModel (Ptr.Heap T), Some (p0.1, existT (Ptr.Heap T) p0.2)
           | Ptr.Map V => λ p0 : ptrModel (Ptr.Map V), Some (p0.1, existT (Ptr.Map V) p0.2)
           | Ptr.Lock => λ p0 : ptrModel Ptr.Lock, Some (p0, existT Ptr.Lock ())
           end p
       | None => None
       end).

(*
Lemma pull_lock_insert_heap {T} p v (σ: sigT (Ptr.t) → option (sigT ptrModel)):
        <[existT (Ptr.Heap T) p:=(Locked, existT (Ptr.Heap T) v)]>
         (λ k, pull_lock (σ k)) ≡
        (λ k, pull_lock (<[existT (Ptr.Heap T) p := existT (ptrModel _) (Locked, v)]>σ k)).
*)

Definition heap_interp {Σ} `{model_wf:GoModelWf} (hM: heap_inG Σ) : State → iProp Σ :=
  (λ s, (gen_heap_ctx (λ k, pull_lock (SemanticsHelpers.dynMap (allocs s.(heap)) k)))).

Definition goose_interp {Σ} `{model_wf:GoModelWf} {hM: heap_inG Σ} {tr: tregG Σ} :=
  (λ s, thread_count_interp (fst s) ∗ heap_interp hM (snd s))%I.

Instance gooseG_irisG `{gooseG Σ} : irisG GoLayer.Op GoLayer.Go.l Σ :=
  {
    iris_invG := go_invG;
    state_interp := goose_interp
  }.

Class GenericMapsTo `{gooseG Σ} (Addr:Type) :=
  { ValTy : Type;
    generic_mapsto : Addr -> Z → ValTy -> iProp Σ; }.

Notation "l ↦{ q } v" := (generic_mapsto l q v)
                      (at level 20) : bi_scope.
Notation "l ↦ v" := (generic_mapsto l 0 v)
                      (at level 20) : bi_scope.


(* TODO: should we also push through here that this means p must be non-null?
   nullptr never gets added to heap mapping so it would also be derivable
   if we enforced that as a property of the heap  *)
Definition ptr_mapsto `{gooseG Σ} {T} (l: ptr T) q (v: Datatypes.list T) : iProp Σ :=
   mapsto (existT (Ptr.Heap T) l) q Unlocked (existT (Ptr.Heap T) v).

(*
Definition path_mapsto `{baseG Σ} (p: Path) (bs: ByteString) : iProp Σ.
Admitted.

Definition fd_mapsto `{baseG Σ} (fh: Fd) (s:Path * FS.OpenMode) : iProp Σ.
Admitted.
*)

Instance ptr_gen_mapsto `{gooseG Σ} T : GenericMapsTo (ptr T)
  := {| generic_mapsto := ptr_mapsto; |}.

Definition slice_mapsto `{gooseG Σ} {T} (l: slice.t T) q (vs: Datatypes.list T) : iProp Σ :=
  (∃ vs', ⌜ getSliceModel l vs' = Some vs ⌝ ∗ l.(slice.ptr) ↦{q} vs')%I.

Instance slice_gen_mapsto `{gooseG Σ} T : GenericMapsTo (slice.t T)
  := {| generic_mapsto := slice_mapsto; |}.

Import Reg_wp.
Section lifting.
Context `{gooseG Σ}.

Lemma thread_reg1:
  ∀ n σ, state_interp (n, σ)
                      -∗ thread_count_interp n ∗ heap_interp (go_heap_inG) σ.
Proof. auto. Qed.
Lemma thread_reg2:
  ∀ n σ, thread_count_interp n ∗ heap_interp (go_heap_inG) σ
                             -∗ state_interp (n, σ).
Proof. auto. Qed.

Lemma wp_spawn {T} s E (e: proc _ T) Φ :
  ▷ Registered
    -∗ ▷ (Registered -∗ WP (let! _ <- e; Unregister)%proc @ s; ⊤ {{ _, True }})
    -∗ ▷ ( Registered -∗ Φ tt)
    -∗ WP Spawn e @ s; E {{ Φ }}.
Proof. eapply wp_spawn; eauto using thread_reg1, thread_reg2. Qed.

Lemma wp_unregister s E :
  {{{ ▷ Registered }}} Unregister @ s; E {{{ RET tt; True }}}.
Proof. eapply wp_unregister; eauto using thread_reg1, thread_reg2. Qed.

Lemma wp_wait s E :
  {{{ ▷ Registered }}} Wait @ s; E {{{ RET tt; AllDone }}}.
Proof. eapply wp_wait; eauto using thread_reg1, thread_reg2. Qed.

Lemma readSome_Err_inv {A T : Type} (f : A → option T) (s : A) :
  readSome f s Err → f s = None.
Proof. rewrite /readSome. destruct (f s); auto; congruence. Qed.

Lemma readSome_Some_inv {A T : Type} (f : A → option T) (s : A) s' t :
  readSome f s (Val s' t) → s = s' ∧ f s = Some t.
Proof. rewrite /readSome. destruct (f s); auto; try inversion 1; subst; split; congruence. Qed.

Ltac inj_pair2 :=
  repeat match goal with
         | [ H: existT ?x ?o1 = existT ?x ?o2 |- _ ] =>
           apply Eqdep.EqdepTheory.inj_pair2 in H; subst
         end.

Ltac trans_elim P :=
  match goal with
  |[ H1 : P = ?y, H2 : P = ?z |- _ ] => rewrite H1 in H2
  end.

Ltac inv_step :=
  repeat match goal with
         | [ H : Data.step _ _ Err  |- _ ] =>
           let Hhd_err := fresh "Hhd_err" in
           let Hhd := fresh "Hhd" in
           let Htl_err := fresh "Htl_err" in
           inversion H as [Hhd_err|(?&?&Hhd&Htl_err)]; clear H
         | [ H : and_then _ _ _ Err  |- _ ] =>
           let Hhd_err := fresh "Hhd_err" in
           let Hhd := fresh "Hhd" in
           let Htl_err := fresh "Htl_err" in
           inversion H as [Hhd_err|(?&?&Hhd&Htl_err)]; clear H
         | [ H : Data.step _ _ (Val _ _)  |- _ ] =>
           let Hhd := fresh "Hhd" in
           let Htl := fresh "Htl" in
           destruct H as (?&?&Hhd&Htl)
         | [ H : and_then _ _ _ (Val _ _)  |- _ ] =>
           let Hhd := fresh "Hhd" in
           let Htl := fresh "Htl" in
           destruct H as (?&?&Hhd&Htl)
         | [ H : readSome _ _ Err |- _ ] =>
           apply readSome_Err_inv in H
         | [ H : readSome _ _ (Val _ _) |- _ ] =>
           apply readSome_Some_inv in H as (?&?); subst
         | [ H : context[getAlloc ?p ?σ] |- _ ] =>
           unfold getAlloc in H; try erewrite (SemanticsHelpers.getDyn_lookup1) in H; eauto; []
         | [ H : context[let '(s, alloc) := ?x in _] |- _] => destruct x
         | [ H : lock_acquire _ Unlocked = Some _ |- _ ] => inversion H; subst; clear H
         | [ H : Some ?x = Some ?x |- _] => clear H
         | [ H : Some _ = Some _ |- _] => inversion H; subst
         end.

Lemma wp_ptrStore_start {T} s E (p: ptr T) off l l' v :
  list_nth_upd l off v = Some l' →
  {{{ ▷ p ↦ l }}}
   Call (InjectOp.inject (PtrStore p off v SemanticsHelpers.Begin)) @ s ; E
   {{{ RET tt; mapsto (existT (Ptr.Heap T) p) 0 Locked (existT (Ptr.Heap T) l) }}}.
Proof.
  intros Hupd.
  iIntros (Φ) ">Hi HΦ". rewrite /ptrStore/nonAtomicWriteOp.
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ)".
  iDestruct (@gen_heap_valid1 with "Hσ Hi") as %?.
  simpl in H0.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    apply snd_lift_non_err => Herr.
    rewrite /pull_lock in H0.
    match goal with
    | [ H: context [match ?σ.(heap).(allocs).(SemanticsHelpers.dynMap) ?p with
                    | _ => _  end ] |- _ ] =>
      destruct (σ.(heap).(allocs).(SemanticsHelpers.dynMap) p) as [([]&?)|] eqn:Heqσ
    end; inversion H0; subst; destruct p0.
    simpl in *. subst.
    clear H0.
    inversion Herr; inj_pair2; subst;
    inv_step; try congruence.
    rewrite //= in Hhd_err.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inversion H1. subst.
  inj_pair2.
  inv_step.
  inversion Htl0; subst.
  simpl. iFrame.
  unshelve (iMod (gen_heap_update with "Hσ Hi") as "[Hheap Hi]"); simpl.
  { exact (Locked). }
  { exists (Ptr.Heap T). eauto. }
  iSplitL "Hheap".
  iModIntro. iApply gen_heap_ctx_proper; last eauto.
  intros k. destruct k.
  rewrite /insert/partial_fn_insert/pull_lock.  rewrite //=.
  destruct equal => //=. inversion e. subst. inj_pair2; eauto.
  subst. eauto.
  rewrite //= in H4. destruct l0; inversion H4. subst. eauto.
  iApply "HΦ"; eauto.
  rewrite //= in H4. destruct l0; inversion H4. subst. eauto.
  rewrite /pull_lock in H0.
    match goal with
    | [ H: context [match ?σ.(heap).(allocs).(SemanticsHelpers.dynMap) ?p with
                    | _ => _  end ] |- _ ] =>
      destruct (σ.(heap).(allocs).(SemanticsHelpers.dynMap) p) as [([]&?)|] eqn:Heqσ
    end; inversion H0; subst; destruct p0.
    simpl in H0.
      apply Some_inj in H0.
      apply (f_equal snd) in H0. simpl in H0.
      inj_pair2. subst.
    inv_step. auto.
Qed.

Lemma wp_ptrStore {T} s E (p: ptr T) off l l' v :
  list_nth_upd l off v = Some l' →
  {{{ ▷ p ↦ l }}} ptrStore p off v @ s; E {{{ RET tt; p ↦ l' }}}.
Proof.
  intros Hupd.
  iIntros (Φ) ">Hi HΦ". rewrite /ptrStore/nonAtomicWriteOp.
  wp_bind. iApply (wp_ptrStore_start with "Hi"); eauto.
  iNext. iIntros "Hi".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ)".
  iDestruct (@gen_heap_valid1 with "Hσ Hi") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    apply snd_lift_non_err => Herr.
    rewrite /pull_lock in H0.
    match goal with
    | [ H: context [match ?σ.(heap).(allocs).(SemanticsHelpers.dynMap) ?p with
                    | _ => _  end ] |- _ ] =>
      destruct (σ.(heap).(allocs).(SemanticsHelpers.dynMap) p) as [([]&?)|] eqn:Heqσ
    end; inversion H0; subst; destruct p0.
    simpl in *. subst.
      apply Some_inj in H0.
      apply (f_equal snd) in H0. simpl in H0.
    inversion Herr; inj_pair2; subst;
    inv_step; try congruence.
    rewrite //= in Hhd_err.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inversion H1. subst.
  inj_pair2.
  inv_step.
  inversion Htl; subst; simpl in *.
  unshelve (iMod (@gen_heap_update with "Hσ Hi") as "[Hσ Hi]").
  { exact (Unlocked). }
  { exists (Ptr.Heap T). exact x1. }
  iModIntro. iFrame.
  iSplitL "Hσ".
  iApply gen_heap_ctx_proper; last eauto.
  intros k. destruct k.
  rewrite /insert/partial_fn_insert/pull_lock.  rewrite //=.
  destruct equal => //=. inversion e. subst. inj_pair2; eauto.
  unfold pull_lock in H0.
  destruct l0; try congruence.

  iApply "HΦ".
  inversion H5; subst.
  unfold pull_lock in H0.
    match goal with
    | [ H: context [match ?σ.(heap).(allocs).(SemanticsHelpers.dynMap) ?p with
                    | _ => _  end ] |- _ ] =>
      destruct (σ.(heap).(allocs).(SemanticsHelpers.dynMap) p) as [([]&?)|] eqn:Heqσ
    end; inversion H0; subst; destruct p0.
    simpl in H0.
      apply Some_inj in H0.
      apply (f_equal snd) in H0. simpl in H0.
      inj_pair2. simpl in *. subst.
      inv_step.
      trans_elim (list_nth_upd l1 off v).
      inv_step. eauto.
Qed.

Lemma wp_writePtr {T} s E (p: ptr T) v' l v :
  {{{ ▷ p ↦ (v' :: l) }}} writePtr p v @ s; E {{{ RET tt; p ↦ (v :: l) }}}.
Proof. iIntros (Φ) ">Hi HΦ". iApply (wp_ptrStore with "Hi"); eauto. Qed.

(*
Lemma wp_ptrDeref {T} s E (p: ptr T) q off l v :
  List.nth_error l off = Some v →
  {{{ ▷ p ↦{q} l }}} ptrDeref p off @ s; E {{{ RET v; p ↦{q} l }}}.
Proof.
  intros Hupd.
  iIntros (Φ) ">Hi HΦ". rewrite /ptrDeref.
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ)".
  iDestruct (@gen_heap_valid with "Hσ Hi") as %?.
  simpl in H0.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    apply snd_lift_non_err => Herr.
    inversion Herr; inj_pair2; subst.
    inv_step; try congruence.
    rewrite //= in Hhd_err.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inversion H1. subst.
  inj_pair2.
  inv_step.
  inversion Htl; subst.
  iFrame.
  trans_elim (nth_error l1 off). inv_step.
    by iApply "HΦ".
Qed.

Lemma wp_readPtr {T} s E (p: ptr T) q v l :
  {{{ ▷ p ↦{q} (v :: l) }}} readPtr p @ s; E {{{ RET v; p ↦{q} (v :: l) }}}.
Proof. iIntros (Φ) ">Hi HΦ". iApply (wp_ptrDeref with "Hi"); eauto. Qed.

Lemma nth_error_lookup {A :Type} (l: Datatypes.list A) (i: nat) :
  nth_error l i = l !! i.
Proof.
  revert l.
  induction i => l.
  * destruct l; auto.
  * move: IHi. simpl. destruct l => //=.
Qed.

Lemma wp_sliceRead {T} s E (p: slice.t T) q off l v :
  List.nth_error l off = Some v →
  {{{ ▷ p ↦{q} l }}} sliceRead p off @ s; E {{{ RET v; p ↦{q} l }}}.
Proof.
  iIntros (Hnth Φ) ">Hp HΦ".
  iDestruct "Hp" as (vs Heq) "Hp".
  rewrite /getSliceModel/sublist_lookup/mguard/option_guard in Heq.
  destruct (decide_rel); last by congruence.
  inversion Heq. subst.
  iApply (wp_ptrDeref with "Hp").
  rewrite nth_error_lookup in Hnth *.
  assert (Hlen: off < length (take p.(slice.length) (drop p.(slice.offset) vs))).
  { eapply lookup_lt_is_Some_1. eauto. }
  rewrite lookup_take in Hnth. rewrite lookup_drop in Hnth.
  rewrite nth_error_lookup. eauto.
  { rewrite take_length in Hlen. lia. }
  iIntros "!> ?".
  iApply "HΦ". iExists _; iFrame.
  rewrite /getSliceModel/sublist_lookup/mguard/option_guard.
  destruct (decide_rel); last by congruence.
  eauto.
Qed.
*)

Lemma getSliceModel_len_inv {T} (p: slice.t T) l l':
  getSliceModel p l = Some l' →
  length l' = p.(slice.length).
Proof.
  rewrite /getSliceModel. apply sublist_lookup_length.
Qed.

(*
Lemma wp_sliceAppend {T} s E (p: slice.t T) l v :
  {{{ ▷ p ↦ l }}} sliceAppend p v @ s; E {{{ p', RET p'; p' ↦ (l ++ [v]) }}}.
Proof.
  iIntros (Φ) ">Hp HΦ".
  iDestruct "Hp" as (vs Heq) "Hp".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ)".
  iDestruct (@gen_heap_valid with "Hσ Hp") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    apply snd_lift_non_err => Herr.
    inversion Herr; inj_pair2; subst.
    inv_step; try congruence; inversion Hhd_err.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inversion H1. subst.
  inj_pair2.
  inv_step.
  inversion Hhd1; subst.
  inversion Hhd2; subst.
  inversion Hhd3; subst.
  inversion Htl0. subst.
  intuition.
  simpl. iFrame.
  unshelve (iMod (@gen_heap_dealloc with "Hσ Hp") as "Hσ").
  unshelve (iMod (@gen_heap_alloc with "Hσ") as "[$ Hp]").
  { rewrite /base.delete/partial_fn_delete.
    destruct equal; subst; auto.
    match goal with
    | [ H: getAlloc ?x _ = None |- _ ] => rename H into Hlookup
    end.
    eapply SemanticsHelpers.getDyn_lookup_none; eauto.
    rewrite /getAlloc//= in Hlookup.
    rewrite SemanticsHelpers.getDyn_deleteDyn_ne in Hlookup; eauto.
    intros Heq'. subst. congruence.
  }
  iModIntro.
  iApply "HΦ".
  iExists _. iFrame. iPureIntro.
  trans_elim (getSliceModel p l1). inv_step.
  rewrite /getSliceModel//=.
  apply getSliceModel_len_inv in Heq.
  rewrite sublist_lookup_all //=.
  rewrite app_length //=. lia.
Qed.
*)

(*
Lemma wp_sliceAppendSlice {T} s E (p1 p2: slice.t T) q l1 l2 :
  {{{ ▷ p1 ↦ l1 ∗ ▷ p2 ↦{q} l2 }}}
    sliceAppendSlice p1 p2 @ s; E
  {{{ p', RET p'; p' ↦ (l1 ++ l2) ∗ p2 ↦{q} l2 }}}.
Proof.
  iIntros (Φ) "(>Hp1&>Hp2) HΦ".
  iDestruct "Hp1" as (vs1 Heq1) "Hp1".
  iDestruct "Hp2" as (vs2 Heq2) "Hp2".
  rewrite /sliceAppendSlice.
  rewrite /nonAtomicOp.
  wp_bind.
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ)".
  iDestruct (@gen_heap_valid with "Hσ Hp1") as %?.
  iDestruct (@gen_heap_valid with "Hσ Hp2") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    apply snd_lift_non_err => Herr.
    inversion Herr; inj_pair2; subst.
    inv_step; try congruence; inversion Hhd_err.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inversion H2. subst.
  inj_pair2.
  inv_step.
  inversion Htl; subst.
  simpl. iFrame.
  unshelve (iMod (@gen_heap_update with "Hσ Hp2") as "[$ Hp2]").
  { rewrite /base.delete/partial_fn_delete.
    destruct equal; subst; auto.
    match goal with
    | [ H: getAlloc ?x _ = None |- _ ] => rename H into Hlookup
    end.
    eapply SemanticsHelpers.getDyn_lookup_none; eauto.
    rewrite /getAlloc//= in Hlookup.
    rewrite SemanticsHelpers.getDyn_deleteDyn_ne in Hlookup; eauto.
    intros Heq'. subst. congruence.
  }
  iModIntro.
  iApply "HΦ".
  iExists _. iFrame. iPureIntro.
  trans_elim (getSliceModel p l1). inv_step.
  rewrite /getSliceModel//=.
  apply getSliceModel_len_inv in Heq.
  rewrite sublist_lookup_all //=.
  rewrite app_length //=. lia.
Qed.
*)

End lifting.
