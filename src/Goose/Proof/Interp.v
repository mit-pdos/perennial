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
         | [ H: existT ?x _ = existT ?y _ |- _ ] => inversion H; subst
         end.

Ltac trans_elim P :=
  match goal with
  |[ H1 : P = ?y, H2 : P = ?z |- _ ] => rewrite H1 in H2
  end.

Lemma lock_acquire_writer_inv l0 l1:
  lock_acquire Writer l0 = Some l1 →
  l0 = Unlocked ∧ l1 = Locked.
Proof. destruct l0 => //=; inversion 1; auto. Qed.

Lemma lock_available_reader_fail_inv l:
  lock_available Reader l = None →
  l = Locked.
Proof. destruct l => //=. Qed.

Ltac inv_step :=
  repeat (inj_pair2; match goal with
         | [ H : unit |- _ ] => destruct H
         | [ H : Data.step _ _ Err  |- _ ] =>
           let Hhd_err := fresh "Hhd_err" in
           let Hhd := fresh "Hhd" in
           let Htl_err := fresh "Htl_err" in
           inversion H as [Hhd_err|(?&?&Hhd&Htl_err)]; clear H
         | [ |- ¬ Go.step _ _ Err ] => let Herr := fresh "Herr" in
                                    intros Herr
         | [ |- ¬ snd_lift _ _ Err ] => apply snd_lift_non_err;
                                        let Herr := fresh "Herr" in
                                        intros Herr
         | [ H : and_then _ _ _ Err  |- _ ] =>
           let Hhd_err := fresh "Hhd_err" in
           let Hhd := fresh "Hhd" in
           let Htl_err := fresh "Htl_err" in
           inversion H as [Hhd_err|(?&?&Hhd&Htl_err)]; clear H
         | [ H : such_that _ _ _ |- _ ] => inversion H; subst; clear H
         | [ H : pure _ _ _ |- _ ] => inversion H; subst; clear H
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
         | [ H : context[pull_lock _] |- _ ] =>
           unfold pull_lock in H
         | [ H : context[getAlloc ?p ?σ] |- _ ] =>
           unfold getAlloc in H; try erewrite (SemanticsHelpers.getDyn_lookup1) in H; eauto; []
         | [ H : context[let '(s, alloc) := ?x in _] |- _] => destruct x
         | [ H : lock_acquire _ Unlocked = Some _ |- _ ] => inversion H; subst; clear H
         | [ H : lock_acquire Writer _ = Some _ |- _ ] =>
           apply lock_acquire_writer_inv in H as (?&?)
         | [ H : lock_available Reader _ = None |- _ ] =>
           apply lock_available_reader_fail_inv in H
         | [ H : delAllocs _ _ (Val _ _) |- _ ] =>
           inversion H; subst; clear H
         | [ H : updAllocs _ _ _ (Val _ _) |- _ ] =>
           inversion H; subst; clear H
         | [ H : Some _ = Some _ |- _] => apply Some_inj in H; subst
         | [ H : (?a, ?b) = (?c, ?d) |- _] => apply pair_inj in H as (?&?); subst
         | [ H : Go.step _ _ Err |- _ ] => inversion H; clear H; subst
         | [ H : Go.step _ _ (Val _ _) |- _ ] => inversion H; clear H; subst
         | [ H: context [match ?σ.(heap).(allocs).(SemanticsHelpers.dynMap) ?p with
                         | _ => _  end ] |- _ ] =>
           let pfresh := fresh "p" in
           destruct (σ.(heap).(allocs).(SemanticsHelpers.dynMap) p) as [([]&pfresh)|] eqn:Heqσ;
           inversion H; subst; destruct pfresh
         end); inj_pair2.

Ltac unfoldpull := rewrite /insert/partial_fn_insert/base.delete/partial_fn_delete/pull_lock.

Lemma wp_newAlloc {T} s E (v: T) len :
  {{{ True }}}
    newAlloc v len @ s ; E
  {{{ (p: ptr T) , RET p; p ↦ (List.repeat v len) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ)".
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    simpl. inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  simpl in *. do 2 (inv_step; intuition).
  eapply SemanticsHelpers.getDyn_lookup_none in H0.
  unshelve (iMod (@gen_heap_alloc with "Hσ") as "(Hσ&Hp)").
  { exists (Ptr.Heap T). eauto. }
  { exists (Ptr.Heap T). exact (List.repeat v len). }
  { unfoldpull => //=. by rewrite H0. }
  iFrame.
  iSplitL "Hσ".
  { iModIntro. iApply @gen_heap_ctx_proper; last eauto; intros (?&?).
    unfoldpull => //=.
    destruct equal; auto.
  }
  iApply "HΦ"; eauto.
Qed.

Lemma wp_ptrStore_start {T} s E (p: ptr T) off l l' v :
  list_nth_upd l off v = Some l' →
  {{{ ▷ p ↦ l }}}
   Call (InjectOp.inject (PtrStore p off v SemanticsHelpers.Begin)) @ s ; E
   {{{ RET tt; mapsto (existT (Ptr.Heap T) p) 0 Locked (existT (Ptr.Heap T) l) }}}.
Proof.
  intros Hupd.
  iIntros (Φ) ">Hi HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ)".
  iDestruct (@gen_heap_valid1 with "Hσ Hi") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    simpl. inv_step; simpl in *; subst; congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  simpl in *. inv_step.
  simpl. iFrame.
  unshelve (iMod (@gen_heap_update with "Hσ Hi") as "[Hheap Hi]"); simpl.
  { exact (Locked). }
  { exists (Ptr.Heap T). eauto. }
  iSplitL "Hheap".
  { iModIntro. iApply @gen_heap_ctx_proper; last eauto; intros (?&?).
    unfoldpull => //=. destruct matches. }
  iApply "HΦ"; eauto.
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
    simpl. inv_step; simpl in *; subst; congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  simpl in *. inv_step. subst; simpl in *.
  unshelve (iMod (@gen_heap_update with "Hσ Hi") as "[Hσ Hi]").
  { exact (Unlocked). }
  { exists (Ptr.Heap T). eauto. }
  iModIntro. iFrame.
  iSplitL "Hσ".
  { iApply @gen_heap_ctx_proper; last eauto; intros (?&?).
    unfoldpull => //=. destruct matches. inv_step; eauto.
  }
  iApply "HΦ".
  trans_elim (list_nth_upd l1 off v).
  inv_step. eauto.
Qed.

Lemma wp_writePtr {T} s E (p: ptr T) v' l v :
  {{{ ▷ p ↦ (v' :: l) }}} writePtr p v @ s; E {{{ RET tt; p ↦ (v :: l) }}}.
Proof. iIntros (Φ) ">Hi HΦ". iApply (wp_ptrStore with "Hi"); eauto. Qed.

Lemma wp_ptrDeref {T} s E (p: ptr T) q off l v :
  List.nth_error l off = Some v →
  {{{ ▷ p ↦{q} l }}} ptrDeref p off @ s; E {{{ RET v; p ↦{q} l }}}.
Proof.
  intros Hupd.
  iIntros (Φ) ">Hi HΦ". rewrite /ptrDeref.
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ)".
  iDestruct (@gen_heap_valid with "Hσ Hi") as %[s' [? ?]].
  simpl in H0.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    simpl. inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  simpl in *. inv_step.
  iFrame. simpl in *.
  trans_elim (nth_error l1 off). inv_step.
    by iApply "HΦ".
Qed.

Lemma wp_readPtr {T} s E (p: ptr T) q v l :
  {{{ ▷ p ↦{q} (v :: l) }}} readPtr p @ s; E {{{ RET v; p ↦{q} (v :: l) }}}.
Proof. iIntros (Φ) ">Hi HΦ". iApply (wp_ptrDeref with "Hi"); eauto. Qed.

Lemma nth_error_lookup {A :Type} (l: Datatypes.list A) (i: nat) :
  nth_error l i = l !! i.
Proof. revert l; induction i => l; destruct l; eauto. Qed.

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

Lemma getSliceModel_len_inv {T} (p: slice.t T) l l':
  getSliceModel p l = Some l' →
  length l' = p.(slice.length).
Proof.
  rewrite /getSliceModel. apply sublist_lookup_length.
Qed.

Lemma wp_sliceAppend {T} s E (p: slice.t T) l v :
  {{{ ▷ p ↦ l }}} sliceAppend p v @ s; E {{{ p', RET p'; p' ↦ (l ++ [v]) }}}.
Proof.
  iIntros (Φ) ">Hp HΦ".
  iDestruct "Hp" as (vs Heq) "Hp".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ)".
  iDestruct (@gen_heap_valid1 with "Hσ Hp") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    simpl. inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  simpl in *. inv_step. simpl in *.
  intuition. subst.
  iFrame.
  unshelve (iMod (@gen_heap_dealloc with "Hσ Hp") as "Hσ").
  unshelve (iMod (@gen_heap_alloc with "Hσ") as "[Hσ Hp]").
  { exists (Ptr.Heap T).
    match goal with
    | [H : getAlloc ?x _ = None |- _ ] => exact x
    end.
  }
  { eexists (Ptr.Heap T). shelve. }  (* eapply (x ++ [v]). } *)
  { rewrite /base.delete/partial_fn_delete.
    destruct equal; subst; auto.
    match goal with
    | [ H: getAlloc ?x _ = None |- _ ] => rename H into Hlookup
    end.
    rewrite /getAlloc SemanticsHelpers.getDyn_deleteDyn_ne in Hlookup; eauto.
    rewrite SemanticsHelpers.getDyn_lookup_none2 => //=.
    intros Hfalse. subst. congruence.
  }
  iSplitL "Hσ".
  { iApply @gen_heap_ctx_proper; last eauto; intros (?&?).
    unfoldpull => //=. destruct matches. }
  iModIntro.
  iApply "HΦ".
  iExists _. iFrame. iPureIntro.
  simpl in *.
  trans_elim (getSliceModel p l1). inv_step.
  apply getSliceModel_len_inv in Heq.
  rewrite /getSliceModel sublist_lookup_all //= app_length //=. lia.
Qed.

Lemma take_1_drop {T} (x: T) n l:
  nth_error l n = Some x →
  take 1 (drop n l) = [x].
Proof. revert l. induction n => l; destruct l; inversion 1; eauto. Qed.

Lemma wp_sliceAppendSlice_aux {T} s E (p1 p2: slice.t T) q l1 l2 rem off :
  rem + off <= length l2 →
  {{{ ▷ p1 ↦ l1 ∗ ▷ p2 ↦{q} l2 }}}
    sliceAppendSlice_aux p1 p2 rem off @ s; E
  {{{ p', RET p'; p' ↦ (l1 ++ (firstn rem (skipn off l2))) ∗ p2 ↦{q} l2 }}}.
Proof.
  iIntros (Hlen Φ) "(>Hp1&>Hp2) HΦ".
  iInduction rem as [| rem] "IH" forall (off Hlen l1 p1).
  - simpl. rewrite firstn_O app_nil_r -wp_bind_proc_val.
    iNext; wp_ret; iApply "HΦ"; iFrame.
  - simpl.
    destruct (nth_error l2 off) as [x|] eqn:Hnth; last first.
    { apply nth_error_None in Hnth. lia. }
    wp_bind. iApply (wp_sliceRead with "Hp2"); eauto.
    iIntros "!> Hp2".
    wp_bind. iApply (wp_sliceAppend with "Hp1"); eauto.
    iIntros "!>". iIntros (p1') "Hp1".
    rewrite -Nat.add_1_l -take_take_drop drop_drop assoc Nat.add_1_r.
    erewrite take_1_drop; eauto.
    iApply ("IH" with "[] Hp1 Hp2"); eauto.
    iPureIntro; lia.
Qed.

Lemma wp_sliceAppendSlice {T} s E (p1 p2: slice.t T) q l1 l2 :
  {{{ ▷ p1 ↦ l1 ∗ ▷ p2 ↦{q} l2 }}}
    sliceAppendSlice p1 p2 @ s; E
  {{{ p', RET p'; p' ↦ (l1 ++ l2) ∗ p2 ↦{q} l2 }}}.
Proof.
  rewrite /sliceAppendSlice.
  iIntros (Φ) "(>Hp1&>Hp2) HΦ".
  iAssert (⌜ p2.(slice.length) = length l2 ⌝)%I with "[-]" as %->.
  { iDestruct "Hp2" as (vs2 Heq2) "Hp2".
    iPureIntro. symmetry.
    eapply sublist_lookup_length; eauto.
  }
  iApply (wp_sliceAppendSlice_aux with "[$]"); first by lia.
  rewrite drop_0 firstn_all.
  iApply "HΦ".
Qed.

End lifting.
