(* TODO: figure out a way to make this mix-in-able for anything building on Heap *)

From iris.algebra Require Import auth gmap frac agree.
Require Import Helpers.RelationTheorems.
From iris.algebra Require Export functions csum.
From iris.base_logic.lib Require Export invariants.
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting Count_Typed_Heap CSL.ThreadReg CSL.Count_GHeap.
From iris.proofmode Require Export tactics.

From RecoveryRefinement.Goose Require Import Machine GoZeroValues Heap GoLayer.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.

Set Default Proof Using "Type".

Import Data.
Import Filesys.FS.

Notation heap_inG := (@gen_typed_heapG Ptr.ty Ptr ptrRawModel).

Class fsG (m: GoModel) {wf: GoModelWf m} Σ :=
   FsG {
      (* todo -- I would like to re-use some of the LockStatus reasoning but right now will need some duplication *)
      go_fs_dlocks_inG :> gen_heapG string (LockStatus * unit) Σ;
      go_fs_dirs_inG :> gen_heapG string (gset string) Σ;
      go_fs_paths_inG :> gen_heapG path.t (Inode) Σ;
      go_fs_inodes_inG :> gen_heapG Inode (List.list byte) Σ;
      go_fs_fds_inG :> gen_heapG File (Inode * OpenMode) Σ;
     }.

Class gooseG Σ :=
  GooseG {
      go_invG : invG Σ;
      model :> GoModel;
      model_wf :> GoModelWf model;
      go_heap_inG :> (@gen_typed_heapG Ptr.ty Ptr ptrRawModel Σ _);
      go_fs_inG :> fsG model Σ;
      go_treg_inG :> tregG Σ;
    }.

Definition heap_interp {Σ} `{model_wf:GoModelWf} (hM: heap_inG Σ) : State → iProp Σ :=
  (λ s, (gen_typed_heap_ctx s.(heap).(allocs))).

Definition dirent_insert (m: gmap path.t Inode) (d: string) (md: gmap string Inode) :=
  map_fold (λ f inode m', <[ {| path.dir := d; path.fname := f |} := inode]> m') m md.

Definition dirent_flatten (m: gmap string (gmap string Inode)) : gmap path.t Inode :=
  map_fold (λ dir filemap m', dirent_insert m' dir filemap) ∅ m.

Definition fs_interp {Σ model hwf} (F: @fsG model hwf Σ) : State → iProp Σ :=
  (λ s, (gen_heap_ctx (hG := go_fs_dirs_inG)
                      (fmap (dom (gset string) (Dom := gset_dom)) s.(dirents)))
   ∗ (gen_heap_ctx (hG := go_fs_dlocks_inG) (s.(dirlocks)))
   ∗ (gen_heap_ctx (hG := go_fs_paths_inG) (dirent_flatten s.(dirents)))
   ∗ (gen_heap_ctx (hG := go_fs_inodes_inG) s.(inodes))
   ∗ (gen_heap_ctx (hG := go_fs_fds_inG) s.(fds)))%I.

Definition goose_interp {Σ} `{model_wf:GoModelWf} {G: gooseG Σ} {tr: tregG Σ} :=
  (λ s, heap_interp (go_heap_inG) s ∗ fs_interp (go_fs_inG) s)%I.

Instance gooseG_irisG `{gooseG Σ} : irisG GoLayer.Op GoLayer.Go.l Σ :=
  {
    iris_invG := go_invG;
    state_interp := (λ s, thread_count_interp (fst s) ∗ goose_interp (snd s))%I
  }.

Class GenericMapsTo `{gooseG Σ} (Addr:Type) (ValTy: Type) :=
  { generic_mapsto : Addr -> Z → ValTy -> iProp Σ; }.

Notation "l ↦{ q } v" := (generic_mapsto l q v)
                      (at level 20) : bi_scope.
Notation "l ↦ v" := (generic_mapsto l 0 v)
                      (at level 20) : bi_scope.


(* TODO: should we also push through here that this means p must be non-null?
   nullptr never gets added to heap mapping so it would also be derivable
   if we enforced that as a property of the heap  *)

Definition ptr_mapsto `{gooseG Σ} {T} (l: ptr T) q (v: Datatypes.list T) : iProp Σ
  := Count_Typed_Heap.mapsto (hG := go_heap_inG)  l q Unlocked v.

Definition map_mapsto `{gooseG Σ} {T} (l: Map T) q v : iProp Σ
  := Count_Typed_Heap.mapsto (hG := go_heap_inG) l q Unlocked v.

Instance ptr_gen_mapsto `{gooseG Σ} T : GenericMapsTo (ptr T) _
  := {| generic_mapsto := ptr_mapsto; |}.

Instance map_gen_mapsto `{gooseG Σ} T : GenericMapsTo (Map T) _
  := {| generic_mapsto := map_mapsto; |}.

Definition slice_mapsto `{gooseG Σ} {T} (l: slice.t T) q (vs: Datatypes.list T) : iProp Σ :=
  (∃ vs', ⌜ getSliceModel l vs' = Some vs ⌝ ∗ l.(slice.ptr) ↦{q} vs')%I.

Instance slice_gen_mapsto `{gooseG Σ} T : GenericMapsTo (slice.t T) _
  := {| generic_mapsto := slice_mapsto; |}.

Definition dir_mapsto `{gooseG Σ} (d: string) q (fs: gset string) : iProp Σ
  := mapsto (hG := go_fs_dirs_inG) d q fs.

Definition dirlock_mapsto `{gooseG Σ} (d: string) q (s: LockStatus) : iProp Σ
  := mapsto (hG := go_fs_dlocks_inG) d q (s, tt).

Definition path_mapsto `{gooseG Σ} (p: path.t) q (i: Inode) : iProp Σ
  := mapsto (hG := go_fs_paths_inG) p q i.

Definition inode_mapsto `{gooseG Σ} (i: Inode) q (bs: List.list byte) : iProp Σ
  := mapsto (hG := go_fs_inodes_inG) i q bs.

Definition fd_mapsto `{gooseG Σ} (fd: File) q (v: Inode * OpenMode) : iProp Σ
  := mapsto (hG := go_fs_fds_inG) fd q v.

Instance dir_gen_mapsto `{gooseG Σ} : GenericMapsTo (string) (gset string)
  := {| generic_mapsto := dir_mapsto; |}.

Instance dirlock_gen_mapsto `{gooseG Σ} : GenericMapsTo (string) LockStatus
  := {| generic_mapsto := dirlock_mapsto; |}.

Instance path_gen_mapsto `{gooseG Σ} : GenericMapsTo (path.t) _
  := {| generic_mapsto := path_mapsto; |}.

Instance inode_gen_mapsto `{gooseG Σ} : GenericMapsTo (Inode) _
  := {| generic_mapsto := inode_mapsto; |}.

Instance fd_gen_mapsto `{gooseG Σ} : GenericMapsTo File _
  := {| generic_mapsto := fd_mapsto; |}.

Import Reg_wp.
Section lifting.
Context `{gooseG Σ}.

Lemma thread_reg1:
  ∀ n σ, state_interp (n, σ) -∗ thread_count_interp n ∗ goose_interp σ.
Proof. auto. Qed.
Lemma thread_reg2:
  ∀ n σ, thread_count_interp n ∗ goose_interp σ -∗ state_interp (n, σ).
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

Import SemanticsHelpers.

Lemma zoom_non_err {A C} (proj : A → C) (inj : C → A → A) {T} (r : relation C C T) (s : A):
  ¬ r (proj s) Err → ¬ zoom proj inj r s Err.
Proof. firstorder. Qed.

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
         | [ |- ¬ snd_lift _ _ Err ] => apply snd_lift_non_err; try (apply zoom_non_err);
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
           unfold getAlloc in H
         | [ H : ?x = Some ?y,
             H': ?x = _ |- _] =>
             rewrite H in H'
         | [ H : ?σ2 = RecordSet.set heap (λ _ : Data.State, ?σ2.(heap)) ?σ |- _ ] =>
           let Heq := fresh "Heq" in
           let heapName := fresh "heap" in
           remember (σ2.(heap)) as heapName eqn:Heq; clear Heq; subst
         | [ H: Go.l.(sem).(Proc.step) _ _ _ |- _] =>
           destruct H as (?&?)
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
         | [ H : Cinl _ = Cinl _ |- _] => inversion H; clear H; subst
         | [ H : ReadLocked _ = ReadLocked _ |- _] => inversion H; clear H; subst
         | [ H : (?a, ?b) = (?c, ?d) |- _] => apply pair_inj in H as (?&?); subst
         | [ H : Go.step _ _ Err |- _ ] => inversion H; clear H; subst
         | [ H : Go.step _ _ (Val _ _) |- _ ] => inversion H; clear H; subst
         | [ H: context [match ?σ.(heap).(allocs).(SemanticsHelpers.dynMap) ?p with
                         | _ => _  end ] |- _ ] =>
           let pfresh := fresh "p" in
           destruct (σ.(heap).(allocs).(SemanticsHelpers.dynMap) p) as [([]&pfresh)|] eqn:Heqσ;
           inversion H; subst; try destruct pfresh
         end); inj_pair2.

Lemma wp_newAlloc {T} s E (v: T) len :
  {{{ True }}}
    newAlloc v len @ s ; E
  {{{ (p: ptr T) , RET p; p ↦ (List.repeat v len) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step. simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  do 2 (inv_step; intuition).
  iMod (gen_typed_heap_alloc with "Hσ") as "(Hσ&Hp)"; eauto.
  iFrame. iApply "HΦ"; eauto.
Qed.

Lemma wp_ptrStore_start {T} s E (p: ptr T) off l l' v :
  list_nth_upd l off v = Some l' →
  {{{ ▷ p ↦ l }}}
   Call (InjectOp.inject (PtrStore p off v SemanticsHelpers.Begin)) @ s ; E
   {{{ RET tt; Count_Typed_Heap.mapsto p 0 Locked l }}}.
Proof.
  intros Hupd.
  iIntros (Φ) ">Hi HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid1 (Ptr.Heap T) with "Hσ Hi") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; simpl in *; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iMod (@gen_typed_heap_update with "Hσ Hi") as "[$ Hi]".
  iFrame. iApply "HΦ"; eauto.
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
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid1 (Ptr.Heap T) with "Hσ Hi") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. subst; simpl in *.
  iMod (gen_typed_heap_update (Ptr.Heap T) with "Hσ Hi") as "[$ Hi]".
  iFrame. iApply "HΦ". inv_step; eauto.
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
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid (Ptr.Heap T) with "Hσ Hi") as %[s' [? ?]].
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iFrame. by iApply "HΦ".
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
  {{{ ▷ p ↦ l }}} sliceAppend p v @ s; E {{{ (p': slice.t T), RET p'; p' ↦ (l ++ [v]) }}}.
Proof.
  iIntros (Φ) ">Hp HΦ".
  iDestruct "Hp" as (vs Heq) "Hp".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid1 (Ptr.Heap T) with "Hσ Hp") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. simpl in *.
  intuition. subst.
  iFrame.
  iMod (gen_typed_heap_dealloc (Ptr.Heap T) with "Hσ Hp") as "Hσ".
  iMod (gen_typed_heap_alloc with "Hσ") as "[Hσ Hp]"; first by eauto.
  iFrame.
  iModIntro.
  iApply "HΦ".
  iExists _. iFrame. iPureIntro.
  simpl in *. inv_step.
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
  {{{ (p': slice.t T), RET p'; p' ↦ (l1 ++ (firstn rem (skipn off l2))) ∗ p2 ↦{q} l2 }}}.
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
  {{{ (p': slice.t T), RET p'; p' ↦ (l1 ++ l2) ∗ p2 ↦{q} l2 }}}.
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

Definition lock_mapsto `{gooseG Σ} (l: LockRef) q mode : iProp Σ :=
   Count_Typed_Heap.mapsto l q mode tt.

Definition lock_inv (l: LockRef) (P : nat → iProp Σ) (Q: iProp Σ) : iProp Σ :=
  (∃ (n: nat) stat, lock_mapsto l n stat ∗
    match stat with
      | Unlocked => ⌜ n = O ⌝ ∗ P O
      | ReadLocked n' => ⌜ n = S n' ⌝ ∗ P (S n')
      | Locked => ⌜ n = 1 ⌝
    end)%I.

(*
Definition lock_inv (l: LockRef) (P : nat → iProp Σ) (Q: iProp Σ) : iProp Σ :=
  ((lock_mapsto l O Unlocked ∗ P O) ∨
   (∃ n : nat, lock_mapsto l (S n) (ReadLocked n) ∗ P (S n)) ∨
   (lock_mapsto l 1 Locked))%I.
*)

Definition is_lock (N: namespace) (l: LockRef) (P: nat → iProp Σ) (Q: iProp Σ) : iProp Σ :=
  (□ (∀ n, P n ==∗ P (S n) ∗ Q) ∗
   □ (∀ n, Q ∗ P (S n) ==∗ P n) ∗
   inv N (lock_inv l P Q))%I.

Definition wlocked (l: LockRef) : iProp Σ :=
  lock_mapsto l (-1) Locked.

Definition rlocked (l: LockRef) : iProp Σ :=
  lock_mapsto l (-1) Unlocked.

Global Instance inhabited_LockStatus: Inhabited LockStatus.
Proof. eexists. exact Unlocked. Qed.

Global Instance inhabited_LockMode: Inhabited LockMode.
Proof. eexists. exact Reader. Qed.

Lemma wp_newLock N s E (P: nat → iProp Σ) (Q: iProp Σ) :
  {{{ □ (∀ n, P n ==∗ P (S n) ∗ Q) ∗
      □ (∀ n, Q ∗ P (S n) ==∗ P n) ∗
      P O
  }}}
    newLock @ s ; E
  {{{ (l: LockRef), RET l; is_lock N l P Q }}}.
Proof.
  iIntros (Φ) "(#HPQ1&#HPQ2&HP) HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  do 2 (inv_step; intuition).
  iMod (gen_typed_heap_alloc with "Hσ") as "(Hσ&Hl)"; first by eauto.
  iFrame.
  iApply "HΦ"; eauto.
  iMod (inv_alloc N _ (lock_inv e2 P Q) with "[HP Hl]").
  { iNext. iExists O, Unlocked. by iFrame. }
  iModIntro. iFrame "# ∗".
Qed.

Lemma lock_acquire_Reader_success_inv (l: LockRef) s σ h':
  match lock_acquire Reader s with
  | Some s' => updAllocs l (s', ())
  | None => none
  end σ.(heap) (Val h' ()) →
  lock_acquire Reader s = Some (force_read_lock s) ∧
  h' = {| allocs := updDyn l (force_read_lock s, ()) σ.(heap).(allocs) |}.
Proof. destruct s => //=; inversion 1; subst; eauto. Qed.

Lemma wp_lockAcquire_read N l P Q :
  {{{ is_lock N l P Q }}}
    lockAcquire l Reader
  {{{ RET tt; Q ∗ rlocked l }}}.
Proof.
  iIntros (Φ) "(#HPQ1&#HPQ2&#Hinv) HΦ".
  iInv N as (k stat) "(>H&Hstat)".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid2 (Ptr.Lock) with "Hσ H") as %[s' [? Hlock]].
  iModIntro. iSplit.
  { iPureIntro.
    inv_step; simpl in *; subst; try congruence.
    destruct l0; inversion Htl_err.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  edestruct (lock_acquire_Reader_success_inv) as (?&?); first by eauto.
  destruct stat.
  { apply Count_Heap.Cinr_included_excl' in Hlock; subst. simpl in *; congruence. }
  {
    iMod (gen_typed_heap_readlock' (Ptr.Lock) with "Hσ H") as (s Heq) "(Hσ&Hl)".
    simpl; inv_step. iFrame.
    iDestruct "Hstat" as "(%&HP)".
    iMod ("HPQ1" with "HP") as "(HP&HQ)".
    do 2 iModIntro.
    iDestruct (read_split_join2 (T := Ptr.Lock) with "Hl") as "(Hl&?)".
    iSplitL "Hl HP".
    { iNext. iExists (S k), (ReadLocked (S num)). subst. by iFrame. }
    iApply "HΦ"; iFrame.
  }
  {
    iMod (gen_typed_heap_readlock (Ptr.Lock) with "Hσ H") as (s Heq) "(Hσ&Hl)".
    simpl; inv_step. iFrame.
    iDestruct "Hstat" as "(%&HP)".
    iMod ("HPQ1" with "HP") as "(HP&HQ)".
    do 2 iModIntro.
    iDestruct (read_split_join2 (T := Ptr.Lock) with "Hl") as "(Hl&?)".
    iSplitL "Hl HP".
    { iNext. iExists (S O), (ReadLocked O). subst. by iFrame. }
    iApply "HΦ"; iFrame.
  }
Qed.

Lemma wp_lockRelease_read N l P Q :
  {{{ is_lock N l P Q ∗ Q ∗ rlocked l }}}
    lockRelease l Reader
  {{{ RET tt; True }}}.
Proof.
  iIntros (Φ) "((#HPQ1&#HPQ2&#Hinv)&HQ&Hrlocked) HΦ".
  iInv N as (k stat) "(>H&Hstat)".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid2 (Ptr.Lock) with "Hσ H") as %[s' [? Hlock]].
  iDestruct (gen_typed_heap_valid2 (Ptr.Lock) with "Hσ Hrlocked") as %[s'' [? Hrlock]].
  apply Count_Heap.Cinl_included_nat' in Hrlock as (m&?&?); subst.
  destruct stat; swap 2 3.
  { (* Write locked -- impossible *)
    apply Count_Heap.Cinr_included_excl' in Hlock; subst.
    inv_step. simpl in *. congruence.
  }
  { (* Unlocked -- impossible *)
    iDestruct "Hstat" as "(>%&HP)"; subst.
    iDestruct (mapsto_valid' (T := Ptr.Lock) with "H Hrlocked") as %[].
  }
  iModIntro. iSplit.
  { iPureIntro.
    inv_step; simpl in *; subst; try congruence.
    destruct l0; try destruct num0; try inversion Htl_err; simpl in *; try congruence.
    apply Count_Heap.Cinl_included_nat in Hlock. lia.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iDestruct "Hstat" as "(%&HP)"; subst.
  iMod (gen_typed_heap_readunlock (Ptr.Lock) with "Hσ H") as (s Heq) "(Hσ&Hl)".
  simpl; inv_step. iFrame.
  iMod ("HPQ2" with "[$]") as "HP".
  iModIntro.
  unfold rlocked.
  destruct num.
  * iDestruct (Count_Typed_Heap.read_split_join (T := Ptr.Lock) with "[$]") as "H".
    iSplitL "Hσ".
    { destruct s; inversion Htl; subst; iFrame. }
    iModIntro.
    iSplitL "H HP".
    { iNext. iExists O, Unlocked. by iFrame. }
      by iApply "HΦ"; iFrame.
  * iDestruct (Count_Typed_Heap.read_split_join2 (T := Ptr.Lock) with "[$]") as "H".
    iSplitL "Hσ".
    { destruct s; inversion Htl; subst; iFrame. }
    iModIntro.
    iSplitL "H HP".
    { iNext. iExists (S num), (ReadLocked num). by iFrame. }
      by iApply "HΦ"; iFrame.
Qed.

Lemma lock_acquire_Writer_success_inv (l: LockRef) s σ h':
  match lock_acquire Writer s with
  | Some s' => updAllocs l (s', ())
  | None => none
  end σ.(heap) (Val h' ()) →
  s = Unlocked ∧
  lock_acquire Writer s = Some Locked ∧
  h' = {| allocs := updDyn l (Locked, ()) σ.(heap).(allocs) |}.
Proof. destruct s => //=; inversion 1; subst; eauto. Qed.

Lemma wp_lockAcquire_writer N l P Q :
  {{{ is_lock N l P Q }}}
    lockAcquire l Writer
  {{{ RET tt; P O ∗ wlocked l }}}.
Proof.
  iIntros (Φ) "(#HPQ1&#HPQ2&#Hinv) HΦ".
  iInv N as (k stat) "(>H&Hstat)".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid2 (Ptr.Lock) with "Hσ H") as %[s' [? Hlock]].
  iModIntro. iSplit.
  { iPureIntro.
    inv_step; simpl in *; subst; try congruence.
    destruct l0; inversion Htl_err.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  edestruct (lock_acquire_Writer_success_inv) as (?&?&?); first by eauto; subst.
  destruct stat.
  { (* Writelocked -- impossible *)
    apply Count_Heap.Cinr_included_excl' in Hlock; subst. simpl in *; congruence. }
  { (* Readlocked -- impossible *)
    subst. simpl in *.
    apply Count_Heap.Cinl_included_nat in Hlock. lia.
  }
  iDestruct "Hstat" as "(%&HP)"; subst.
  iMod (gen_typed_heap_update (Ptr.Lock) with "Hσ H") as "($&Hl)".
  simpl; inv_step. iFrame.
  do 2 iModIntro.
  iDestruct (read_split_join3 (T := Ptr.Lock) l O with "Hl") as "(Hl&?)".
  iSplitL "Hl".
  { iNext. iExists 1, Locked. by iFrame. }
  iApply "HΦ"; iFrame.
Qed.

Lemma wp_lockRelease_writer N l P Q :
  {{{ is_lock N l P Q ∗ P O ∗ wlocked l }}}
    lockRelease l Writer
  {{{ RET tt; True }}}.
Proof.
  iIntros (Φ) "((#HPQ1&#HPQ2&#Hinv)&HQ&Hrlocked) HΦ".
  iInv N as (k stat) "(>H&Hstat)".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid2 (Ptr.Lock) with "Hσ H") as %[s' [? Hlock]].
  iDestruct (gen_typed_heap_valid2 (Ptr.Lock) with "Hσ Hrlocked") as %[s'' [? Hrlock]].
  apply Count_Heap.Cinr_included_excl' in Hrlock; subst.
  iModIntro. iSplit.
  { iPureIntro.
    inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iFrame.
  destruct stat.
  {
    iDestruct "Hstat" as "%"; subst.
    iDestruct (read_split_join3 (T := Ptr.Lock) l O with "[$]") as "H".
    simpl in Htl. inv_step.
    iMod (gen_typed_heap_update (Ptr.Lock) with "Hσ H") as "($&Hl)".
    do 2 iModIntro.
    iSplitL "Hl HQ".
    { iNext. iExists O, Unlocked. by iFrame. }
    iApply "HΦ"; by iFrame.
  }
  { apply Count_Heap.Cinl_included_nat' in Hlock as (?&?&?); subst. simpl in *; congruence. }
  { apply Count_Heap.Cinl_included_nat' in Hlock as (?&?&?); subst. simpl in *; congruence. }
Qed.

(* TODO: Some redundancy between the map/ptr triples could be cut *)
Lemma wp_newMap T s E :
  {{{ True }}}
    newMap T @ s ; E
  {{{ (p: Map T) , RET p; p ↦ (∅ : gmap uint64 T) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  do 2 (inv_step; intuition).
  iMod (gen_typed_heap_alloc with "Hσ") as "(Hσ&Hp)"; eauto.
  iFrame. iApply "HΦ"; eauto.
Qed.

Lemma wp_mapAlter_start {T} s E (p: Map T) (m: gmap uint64 T) k f :
  {{{ ▷ p ↦ m }}}
   Call (InjectOp.inject (MapAlter p k f SemanticsHelpers.Begin)) @ s ; E
   {{{ RET tt; Count_Typed_Heap.mapsto p 0 Locked m }}}.
Proof.
  iIntros (Φ) ">Hi HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid1 (Ptr.Map T) with "Hσ Hi") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; simpl in *; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iMod (@gen_typed_heap_update with "Hσ Hi") as "[$ Hi]".
  iFrame. iApply "HΦ"; eauto.
Qed.

Lemma wp_mapAlter {T} s E (p: Map T) (m: gmap uint64 T) k f :
  {{{ ▷ p ↦ m }}} mapAlter p k f @ s; E {{{ RET tt; p ↦ (partial_alter f k m) }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". rewrite /mapAlter/nonAtomicWriteOp.
  wp_bind. iApply (wp_mapAlter_start with "Hi"); eauto.
  iNext. iIntros "Hi".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid1 (Ptr.Map T) with "Hσ Hi") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. subst; simpl in *.
  iMod (gen_typed_heap_update (Ptr.Map T) with "Hσ Hi") as "[$ Hi]".
  iFrame. iApply "HΦ". inv_step; eauto.
Qed.

Lemma wp_mapLookup {T} s E (p: Map T) (m: gmap uint64 T) q k:
  {{{ ▷ p ↦{q} m }}} mapLookup p k @ s; E {{{ RET (m !! k); p ↦{q} m }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". rewrite /mapLookup.
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid (Ptr.Map T) with "Hσ Hi") as %[s' [? ?]].
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iFrame. by iApply "HΦ".
Qed.

Lemma wp_MapStartIter {T} s E (p: Map T) (m: gmap uint64 T) q:
  {{{ ▷ p ↦{q} m }}}
    (Call (InjectOp.inject (@MapStartIter _ T p)))%proc @ s; E
  {{{ l, RET l; ⌜ Permutation.Permutation l (fin_maps.map_to_list m) ⌝
                  ∗ Count_Typed_Heap.mapsto p q (ReadLocked O) m }}}.
Proof.
  iIntros (Φ) ">Hi HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid (Ptr.Map T) with "Hσ Hi") as %?.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    destruct H0 as (?&?&?). inv_step; simpl in *; subst; try congruence.
    destruct l; eauto; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. subst; simpl in *.
  iMod (gen_typed_heap_readlock (Ptr.Map T) with "Hσ Hi") as (s' Heq) "(Hσ&Hl)".
  iFrame.
  destruct l; simpl in *; try congruence;
    inv_step; simpl; iFrame; iApply "HΦ"; iFrame; iModIntro; eauto.
Qed.

Lemma wp_MapEndIter {T} s E (p: Map T) (m: gmap uint64 T) q:
  {{{ ▷ Count_Typed_Heap.mapsto p q (ReadLocked O) m }}}
    (Call (InjectOp.inject (@MapEndIter _ T p)))%proc @ s; E
  {{{ RET tt; p ↦{q} m }}}.
Proof.
  iIntros (Φ) ">Hi HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&?)".
  iDestruct (gen_typed_heap_valid2 (Ptr.Map T) with "Hσ Hi") as %[s' [? Hlock]].
  apply Count_Heap.Cinl_included_nat' in Hlock as (?&?&?); subst.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    destruct s';
    inv_step; simpl in *; inv_step; subst; try congruence; try lia;
    destruct num; congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. subst; simpl in *.
  iMod (gen_typed_heap_readunlock (Ptr.Map T) with "Hσ Hi") as (s' Heq) "(Hσ&Hl)".
  iFrame.
  destruct l; simpl in *; try congruence;
    inv_step; simpl; iFrame.
  destruct s'; inv_step; iFrame; iApply "HΦ"; iFrame; iModIntro; eauto.
Qed.

Lemma wp_mapIter {T} s E (p: Map T) (m: gmap uint64 T) q body Φ:
  ▷ p ↦{q} m -∗
  ▷ (∀ l, ⌜ Permutation.Permutation l (fin_maps.map_to_list m) ⌝
          -∗ WP (mapIterLoop l body) @ s; E {{ Φ }}) -∗
  WP mapIter p body @ s; E {{ v, p ↦{q} m ∗ Φ v }}.
Proof.
  iIntros "Hp Hloop".
  rewrite /mapIter.
  wp_bind. iApply (wp_MapStartIter with "Hp").
  iNext. iIntros (l) "(%&Hp)".
  wp_bind. iApply (wp_wand with "[Hloop]").
  { iApply "Hloop"; eauto. }
  iIntros ([]) "HΦ".
  iApply (wp_MapEndIter with "Hp").
  iFrame. eauto.
Qed.

End lifting.
