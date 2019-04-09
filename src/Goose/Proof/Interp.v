(* TODO: figure out a way to make this mix-in-able for anything building on Heap *)

From iris.algebra Require Import auth gmap frac agree.
Require Import Helpers.RelationTheorems.
From iris.algebra Require Export functions csum.
From iris.base_logic.lib Require Export invariants.
Require CSL.Count_Heap.
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting CSL.Count_Ghost
               CSL.Count_Typed_Heap CSL.ThreadReg CSL.Count_Double_Heap CSL.Count_GHeap.
From iris.proofmode Require Export tactics.

From RecoveryRefinement.Goose Require Import Machine GoZeroValues Heap GoLayer.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.

Set Default Proof Using "Type".

Import Data.
Import Filesys.FS.
Import GoLayer.Go.

Notation heap_inG := (@gen_typed_heapG Ptr.ty Ptr ptrRawModel).

Class fsG (m: GoModel) {wf: GoModelWf m} Σ :=
   FsG {
      go_fs_dlocks_inG :> Count_Heap.gen_heapG string unit Σ;
      go_fs_dirs_inG :> gen_heapG string (gset string) Σ;
      go_fs_paths_inG :> gen_dirG string string (Inode) Σ;
      go_fs_inodes_inG :> gen_heapG Inode (List.list byte) Σ;
      go_fs_fds_inG :> gen_heapG File (Inode * OpenMode) Σ;
      go_fs_domalg_inG :> ghost_mapG (discreteC (gset string)) Σ;
      go_fs_dom_name : gname;
     }.

Canonical Structure sliceLockC {m: GoModel} {wf: GoModelWf m} := leibnizC (option (slice.t LockRef)).

Class globalG (m: GoModel) {wf: GoModelWf m} Σ :=
  GlobalG {
      go_global_alg_inG :> ghost_mapG (discreteC sliceLockC) Σ;
      go_global_name : gname;
    }.

Class gooseG (m: GoModel) {model_wf: GoModelWf m} Σ :=
  GooseG {
      go_invG : invG Σ;
      go_heap_inG :> (@gen_typed_heapG Ptr.ty Ptr ptrRawModel Σ _);
      go_fs_inG :> fsG m Σ;
      go_global_inG :> globalG m Σ;
      go_treg_inG :> tregG Σ;
    }.

Definition heap_interp {Σ} `{model_wf:GoModelWf} (hM: heap_inG Σ) : FS.State → iProp Σ :=
  (λ (s: FS.State), (gen_typed_heap_ctx s.(heap).(allocs))).

Definition fs_interp {Σ model hwf} (F: @fsG model hwf Σ) : FS.State → iProp Σ :=
  (λ s, (gen_heap_ctx (hG := go_fs_dirs_inG)
                      (fmap (dom (gset string) (Dom := gset_dom)) s.(dirents)))
   ∗ (Count_Heap.gen_heap_ctx (hG := go_fs_dlocks_inG) (λ l, s.(dirlocks) !! l))
   ∗ (gen_dir_ctx (hG := go_fs_paths_inG) s.(dirents))
   ∗ (gen_heap_ctx (hG := go_fs_inodes_inG) s.(inodes))
   ∗ (gen_heap_ctx (hG := go_fs_fds_inG) s.(fds))
   ∗ (∃ n: nat, ghost_mapsto (A := discreteC (gset string))
                             (go_fs_dom_name) n (dom (gset string) s.(dirents)))
   ∗ ⌜ dom (gset string) s.(dirents) = dom (gset string) s.(dirlocks) ⌝)%I.

Definition global_interp {m Hwf Σ} (G: @globalG m Hwf Σ) :
  Globals.State (slice.t LockRef) → iProp Σ :=
  λ s, ghost_mapsto_auth (A := discreteC (@sliceLockC m Hwf)) (go_global_name) s.

Definition goose_interp {m Hwf Σ} {G: @gooseG m Hwf Σ} :=
  (λ (s: State), heap_interp (go_heap_inG) (fs s) ∗ fs_interp (go_fs_inG) (fs s)
                 ∗ global_interp (go_global_inG) (maillocks s))%I.

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

Definition dirlock_mapsto `{gooseG Σ} (d: string) q s : iProp Σ
  := Count_Heap.mapsto (hG := go_fs_dlocks_inG) d q s tt.

Definition path_mapsto `{gooseG Σ} (p: path.t) q (i: Inode) : iProp Σ
  := Count_Double_Heap.mapsto (hG := go_fs_paths_inG) (path.dir p) (path.fname p) q i.

Definition inode_mapsto `{gooseG Σ} (i: Inode) q (bs: List.list byte) : iProp Σ
  := mapsto (hG := go_fs_inodes_inG) i q bs.

Definition fd_mapsto `{gooseG Σ} (fd: File) q (v: Inode * OpenMode) : iProp Σ
  := mapsto (hG := go_fs_fds_inG) fd q v.

(*
Definition ghost_gen_mapsto' {A} `{gooseG Σ} (γ: gname) q (v: A) : iProp Σ
  := ghost_mapsto γ q v.
*)

Inductive GLOBAL : Set := global.
Inductive ROOTDIR : Set := rootdir.

(*
Instance ghost_gen_mapsto {A} `{gooseG Σ} : GenericMapsTo gname A
  := {| generic_mapsto := ghost_mapsto |}.
*)

Program Instance global_gen_mapsto `{gooseG Σ} : GenericMapsTo GLOBAL (option (slice.t LockRef))
  := {| generic_mapsto := λ _ q v,
                          (ghost_mapsto (A := discreteC (@sliceLockC _ _)) (go_global_name) q v)|}.

Program Instance rootdir_gen_mapsto `{gooseG Σ} : GenericMapsTo ROOTDIR (gset string)
  := {| generic_mapsto := λ _ q v,
                          (ghost_mapsto (A := discreteC (gset string)) (go_fs_dom_name) q v)|}.

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
Proof. clear. firstorder. Qed.

Lemma zoom2_non_err {A B C} (proj: A → B) (proj2: B → C) (inj2: C → B → B) (inj: B → A → A) {T} (r : relation C C T) (s : A):
  ¬ r (proj2 (proj s)) Err → ¬ zoom proj inj (zoom proj2 inj2 r) s Err.
Proof. clear. firstorder. Qed.

Lemma readSome_Err_inv {A T : Type} (f : A → option T) (s : A) :
  readSome f s Err → f s = None.
Proof. rewrite /readSome. destruct (f s); auto; congruence. Qed.

Lemma readSome_Some_inv {A T : Type} (f : A → option T) (s : A) s' t :
  readSome f s (Val s' t) → s = s' ∧ f s = Some t.
Proof. rewrite /readSome. destruct (f s); auto; try inversion 1; subst; split; congruence. Qed.

Ltac inv_step :=
  repeat (inj_pair2; match goal with
         | [ H : unit |- _ ] => destruct H
         | [ H: l.(Layer.sem).(Proc.step) ?op _ (Val _ _) |- _] =>
           let op := eval compute in op in
           match op with
           | FilesysOp _ => destruct H as (?&?)
                                            (*
           | FilesysOp _ =>
             let Hhd := fresh "Hhd" in
             let Htl := fresh "Htl" in
             destruct H as (?&?&Hhd&Htl)
                                             *)
           | LockGlobalOp _ => destruct H as (?&?)
           | DataOp _ => destruct H as ((?&?)&?)
           end
         | [ H: (sem Go.l).(Proc.step) ?op _ Err |- _] =>
           let op := eval compute in op in
           match op with
           | FilesysOp _ =>
                                  let Hhd_err := fresh "Hhd_err" in
                                  let Hhd := fresh "Hhd" in
                                  let Htl_err := fresh "Htl_err" in
                                  inversion H as [Hhd_err|(?&?&Hhd&Htl_err)]; clear H
           | LockGlobalOp _ =>
                                  let Hhd_err := fresh "Hhd_err" in
                                  let Hhd := fresh "Hhd" in
                                  let Htl_err := fresh "Htl_err" in
                                  inversion H as [Hhd_err|(?&?&Hhd&Htl_err)]; clear H
           | DataOp _ => destruct H as ((?&?)&?)
           end
         | [ H : FS.step _ _ Err  |- _ ] =>
           let Hhd_err := fresh "Hhd_err" in
           let Hhd := fresh "Hhd" in
           let Htl_err := fresh "Htl_err" in
           inversion H as [Hhd_err|(?&?&Hhd&Htl_err)]; clear H
         | [ H : Globals.step _ _ Err  |- _ ] =>
           let Hhd_err := fresh "Hhd_err" in
           let Hhd := fresh "Hhd" in
           let Htl_err := fresh "Htl_err" in
           inversion H as [Hhd_err|(?&?&Hhd&Htl_err)]; clear H
         | [ H : Data.step _ _ Err  |- _ ] =>
           let Hhd_err := fresh "Hhd_err" in
           let Hhd := fresh "Hhd" in
           let Htl_err := fresh "Htl_err" in
           inversion H as [Hhd_err|(?&?&Hhd&Htl_err)]; clear H
         | [ |- ¬ Go.step _ _ Err ] => let Herr := fresh "Herr" in
                                    intros Herr
         | [ |- ¬ snd_lift _ _ Err ] => apply snd_lift_non_err;
                                        try (apply zoom2_non_err);
                                        try (apply zoom_non_err);
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
         | [ H : FS.step _ _ (Val _ _)  |- _ ] =>
           let Hhd := fresh "Hhd" in
           let Htl := fresh "Htl" in
           destruct H as (?&?&Hhd&Htl)
         | [ H : Globals.step _ _ (Val _ _)  |- _ ] =>
           let Hhd := fresh "Hhd" in
           let Htl := fresh "Htl" in
           destruct H as (?&?&Hhd&Htl)
         | [ H : and_then _ _ _ (Val _ _)  |- _ ] =>
           let Hhd := fresh "Hhd" in
           let Htl := fresh "Htl" in
           destruct H as (?&?&Hhd&Htl)
         | [ H: lookup _ _ _ _ |- _ ] => unfold lookup in H
         | [ H: resolvePath _ _ _ _ |- _ ] => unfold resolvePath in H
         | [ H: puts _ _ _ |- _ ] => inversion H; subst; clear H
         | [ H: fresh_key _ _ _ |- _ ] => inversion H; subst; clear H
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
         | [ H : ?σ2 = RecordSet.set fs (λ _ : FS.State, ?σ2.(fs)) ?σ |- _ ] =>
           let Heq := fresh "Heq" in
           let fsName := fresh "fs" in
           remember (σ2.(fs)) as fsName eqn:Heq; clear Heq; subst
         | [ H : ?σ2 = RecordSet.set maillocks (λ _, ?σ2.(maillocks)) ?σ |- _ ] =>
           let Heq := fresh "Heq" in
           let fsName := fresh "ml" in
           remember (σ2.(maillocks)) as fsName eqn:Heq; clear Heq; subst
         | [ H : context[let '(s, alloc) := ?x in _] |- _] => destruct x
         | [ H : lock_acquire _ Unlocked = Some _ |- _ ] => inversion H; subst; clear H
         | [ H : lock_acquire Writer _ = Some _ |- _ ] =>
           apply lock_acquire_writer_inv in H as (?&?)
         | [ H : lock_available Reader _ = None |- _ ] =>
           apply lock_available_reader_fail_inv in H
         | [ H : reads _ _ _ |- _ ] =>
           unfold reads in H
         | [ H : delAllocs _ _ (Val _ _) |- _ ] =>
           inversion H; subst; clear H
         | [ H : updAllocs _ _ _ (Val _ _) |- _ ] =>
           inversion H; subst; clear H
         | [ H: allocPtr _ _ _ _ |- _ ] => unfold allocPtr in H
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

Import Reg_wp.
Section lifting.
Context `{@gooseG gmodel Hwf Σ}.

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

Lemma wp_setX (l: slice.t LockRef) s E :
  {{{ global ↦ None }}}
    Globals.setX l @ s; E
  {{{ RET tt; global ↦ Some l }}}.
Proof.
  iIntros (Φ) "Hp HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&?&?&HG)".
  iDestruct (ghost_var_agree (A := discreteC sliceLockC) with "HG Hp") as %Heq.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; try congruence.
    inversion Hhd. subst. rewrite Heq in Htl_err. inv_step.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. inversion Hhd; subst. rewrite Heq in Htl. inv_step.
  iMod (ghost_var_update (A := discreteC sliceLockC) _ (Some l) with "HG Hp") as "(HG&HP)".
  iFrame. by iApply "HΦ".
Qed.

Lemma wp_getX (l: slice.t LockRef) q s E :
  {{{ global ↦{q} Some l }}}
    Globals.getX @ s; E
  {{{ RET l; global ↦{q} Some l }}}.
Proof.
  iIntros (Φ) "Hp HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&?&?&HG)".
  iDestruct (ghost_var_agree (A := discreteC sliceLockC) with "HG Hp") as %Heq.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; try congruence.
    rewrite Heq in Herr. inversion Herr.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. rewrite Heq in H0. rewrite Heq. inversion H0; subst.
  iFrame. by iApply "HΦ".
Qed.

Lemma dom_insert_L_in {K A} `{Countable K} (m: gmap K A) (i: K) (x: A):
  i ∈ dom (gset K) m →
  dom (gset K) (<[i:=x]> m) = dom (gset K) m.
Proof.
  rewrite dom_insert_L. intros. set_solver.
Qed.

Lemma wp_link_new dir1 name1 dir2 name2 (inode: Inode) S s E :
  {{{ (path.mk dir1 name1) ↦ inode
      ∗ dir2 ↦ S
      ∗ ⌜ ¬ name2 ∈ S ⌝
  }}}
    link dir1 name1 dir2 name2 @ s ; E
  {{{ RET true;
     (path.mk dir1 name1) ↦ inode
     ∗ (path.mk dir2 name2) ↦ inode
     ∗ dir2 ↦ (S ∪ {[name2]})
  }}}.
Proof.
  iIntros (Φ) "(Hp&Hd&%) HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&?&HFS&?)".
  iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?&%)".
  iDestruct (gen_heap_valid with "Hents Hd") as %Hset.
  rewrite lookup_fmap in Hset.
  eapply fmap_Some_1 in Hset as (?&?&?).
  subst.
  iDestruct (gen_dir_valid with "Hpaths Hp") as %H'.
  simpl in H'. destruct H' as (σd&Hd&Hf).
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step. simpl in *; subst; try congruence.
    rewrite Hf in Hhd_err. inv_step; inversion Hhd_err.
    rewrite Hf in Hhd0. inversion Hhd0; subst.
    simpl in *; congruence.
    rewrite Hf in Hhd0. inversion Hhd0; subst. simpl in *.
    inv_step.
    rewrite not_elem_of_dom in H0 * => Hsome.
    rewrite Hsome in Htl_err.
    inv_step.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. rewrite Hf in Hhd0. inversion Hhd0. subst.
  simpl in *. inv_step.
  rewrite not_elem_of_dom in H0 * => Hsome. rewrite Hsome in Htl.
  inv_step.
  do 2 (inv_step; intuition).
  iMod (gen_dir_alloc2 _ _ dir2 name2 _ with "Hpaths") as "(Hpaths&Hp2)"; eauto.
  iMod (gen_heap_update _ (dir2) _ (dom (gset string) (<[name2 := _]> x4))
          with "Hents Hd") as "(?&?)".
  iFrame.
  rewrite -fmap_insert. iFrame. simpl.
  rewrite ?(dom_insert_L_in _ dir2); last first.
  { apply elem_of_dom. eexists; eauto. }
  iFrame.
  iSplitL ""; auto.
  iApply "HΦ". iFrame. by rewrite dom_insert_L comm_L.
Qed.

Lemma wp_link_not_new dir1 name1 dir2 name2 (inode: Inode) S s E :
  {{{ (path.mk dir1 name1) ↦ inode
      ∗ dir2 ↦ S
      ∗ ⌜ name2 ∈ S ⌝
  }}}
    link dir1 name1 dir2 name2 @ s ; E
  {{{ RET false;
     (path.mk dir1 name1) ↦ inode
     ∗ dir2 ↦ S
  }}}.
Proof.
  iIntros (Φ) "(Hp&Hd&%) HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&?&HFS&?)".
  iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?&%)".
  iDestruct (gen_heap_valid with "Hents Hd") as %Hset.
  rewrite lookup_fmap in Hset.
  eapply fmap_Some_1 in Hset as (?&?&?).
  subst.
  iDestruct (gen_dir_valid with "Hpaths Hp") as %H'.
  simpl in H'. destruct H' as (σd&Hd&Hf).
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step. simpl in *; subst; try congruence.
    rewrite Hf in Hhd_err. inv_step; inversion Hhd_err.
    rewrite Hf in Hhd0. inversion Hhd0; subst.
    simpl in *; congruence.
    rewrite Hf in Hhd0. inversion Hhd0; subst. simpl in *.
    inv_step.
    rewrite elem_of_dom in H0 * => Hsome. destruct Hsome as (?&Hsome).
    rewrite Hsome in Htl_err.
    inv_step; inversion Hhd_err; congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. rewrite Hf in Hhd0. inversion Hhd0. subst. simpl in *. inv_step.
  rewrite elem_of_dom in H0 * => Hsome. destruct Hsome as (?&Hsome).
  rewrite Hsome in Htl. inv_step.
  iFrame. iSplitL ""; auto.
  iApply "HΦ". iFrame. eauto.
Qed.

Lemma createSlice_non_err V (data: List.list V) s : ¬ createSlice data s Err.
Proof. inversion 1 as [Hhd_err|(?&?&Hhd&Htl_err)]; inv_step. Qed.

Lemma lock_available_reader_succ l:
  l ≠ Locked → lock_available Reader l = Some tt.
Proof. destruct l; eauto; try congruence. Qed.

Lemma wp_readAt fh (inode: Inode) (bs: Datatypes.list byte) off len q1 q2 s E :
  {{{ fh ↦{q1} (inode, Read)
      ∗ inode ↦{q2} bs
  }}}
    readAt fh off len @ s ; E
  {{{ (s: slice.t byte), RET s;
      fh ↦{q1} (inode, Read)
      ∗ inode ↦{q2} bs
      ∗ s ↦ (list.take len (list.drop off bs))
  }}}.
Proof.
  iIntros (Φ) "(Hfh&Hi) HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&HFS&?)".
  iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?&%)".
  iDestruct (gen_heap_valid with "Hfds Hfh") as %Hfd.
  iDestruct (gen_heap_valid with "Hinodes Hi") as %Hi.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; try unfold readFd in Hhd_err; inv_step.
    * simpl in *; subst; try congruence.
    * simpl in *; inv_step. congruence.
    * eapply createSlice_non_err in Htl_err; eauto.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. red in Htl. do 2 (inv_step; intuition).
  unfold readFd in Hhd. inv_step. destruct equal; last by congruence.
  inv_step.
  iMod (gen_typed_heap_alloc with "Hσ") as "(Hσ&Hp)"; eauto.
  iFrame. iSplitL ""; auto.
  iApply "HΦ". iFrame. iModIntro.
  iExists _. iFrame. iPureIntro.
  rewrite /getSliceModel sublist_lookup_all //= app_length //=.
Qed.

Lemma wp_append fh (inode: Inode) (p': slice.t byte) (bs bs': Datatypes.list byte) q1 q2 s E :
  {{{ fh ↦{q1} (inode, Write)
      ∗ inode ↦ bs
      ∗ p' ↦{q2} bs'
  }}}
    append fh p' @ s ; E
  {{{ RET tt;
      fh ↦{q1} (inode, Write)
      ∗ inode ↦ (bs ++ bs')
      ∗ p' ↦{q2} bs'
  }}}.
Proof.
  iIntros (Φ) "(Hfh&Hi&Hp) HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&HFS&?)".
  iDestruct "Hp" as (vs Heq) "Hp".
  iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?&%)".
  iDestruct (gen_heap_valid with "Hfds Hfh") as %Hfd.
  iDestruct (gen_heap_valid with "Hinodes Hi") as %Hi.
  iDestruct (gen_typed_heap_valid (Ptr.Heap byte) with "Hσ Hp") as %[s' [? ?]].
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; try unfold readFd in *; inv_step; try congruence;
    (destruct equal; last by congruence); inv_step; try congruence.
    * unfold unwrap in Hhd_err. rewrite Heq in Hhd_err. inv_step.
    * unfold unwrap in Hhd_err. destruct l0; try congruence; inv_step.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  unfold readFd in *. unfold unwrap in *.
  inv_step. destruct equal; last by congruence.
  inv_step. rewrite lock_available_reader_succ // in Hhd1.
  rewrite Heq in Hhd0.
  inv_step.
  iMod (gen_heap_update with "Hinodes Hi") as "($&?)".
  iFrame. iSplitL ""; first by auto.
  iApply "HΦ". iFrame.
  iModIntro. iExists _; eauto.
Qed.

Lemma wp_create_new dir fname S s E :
  {{{ dir ↦ S ∗ ⌜ ¬ fname ∈ S ⌝ }}}
    create dir fname @ s ; E
  {{{ (i: Inode) (f: File), RET (f, true);
      f ↦ (i, Write)
        ∗ i ↦ []
        ∗ dir ↦ (S ∪ {[fname]})
        ∗ {| path.dir := dir; path.fname := fname |} ↦ i
  }}}.
Proof.
  iIntros (Φ) "(Hd&%) HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&?&HFS&?)".
  iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?&%)".
  iDestruct (gen_heap_valid with "Hents Hd") as %H'.
  rewrite lookup_fmap in H'.
  eapply fmap_Some_1 in H' as (?&?&?).
  subst.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step. simpl in *; subst; try congruence.
    rewrite not_elem_of_dom in H0 * => Hsome. rewrite Hsome in Htl_err.
    inv_step; inversion Hhd_err.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  rewrite not_elem_of_dom in H0 * => Hsome. rewrite Hsome in Htl.
  do 2 (inv_step; intuition).
  iMod (gen_dir_alloc2 _ _ dir fname x with "Hpaths") as "(Hpaths&Hp)"; eauto.
  iMod (gen_heap_update _ (dir) _ (dom (gset string) (<[fname := x]> x0)) with "Hents Hd") as "(?&?)".
  iMod (gen_heap_alloc with "Hinodes") as "(?&?)"; first eauto.
  iMod (gen_heap_alloc with "Hfds") as "(?&?)"; first eauto.
  iFrame.
  rewrite -fmap_insert. iFrame.
  simpl.
  rewrite ?(dom_insert_L_in _ dir); last first.
  { apply elem_of_dom. eexists; eauto. }
  iFrame.
  iSplitL ""; auto.
  iApply "HΦ". iFrame. by rewrite dom_insert_L comm_L.
Qed.

Lemma identity_val_inv {A B: Type} (x x': A) (b: B):
  identity x (Val x' b) → x = x'.
Proof. inversion 1; subst. congruence. Qed.

Lemma wp_create_not_new dir fname S s E :
  {{{ dir ↦ S ∗ ⌜ fname ∈ S ⌝ }}}
    create dir fname @ s ; E
  {{{ (f: File), RET (f, false); dir ↦ S }}}.
Proof.
  iIntros (Φ) "(Hd&%) HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&?&HFS&?)".
  iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?)".
  iDestruct (gen_heap_valid with "Hents Hd") as %H'.
  rewrite lookup_fmap in H'.
  eapply fmap_Some_1 in H' as (?&?&?).
  subst.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step. simpl in *; subst; try congruence.
    rewrite elem_of_dom in H0 * => Hsome. destruct Hsome as (?&Hsome).
    rewrite Hsome in Htl_err.
    inv_step; inversion Hhd_err; congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  rewrite elem_of_dom in H0 * => Hsome. destruct Hsome as (?&Hsome).
  rewrite Hsome in Htl.
  do 2 (inv_step; intuition).
  apply identity_val_inv in Hhd; subst.
  iFrame. by iApply "HΦ".
Qed.

Lemma wp_open dir fname inode q s E :
  {{{ path.mk dir fname ↦{q} inode  }}}
    open dir fname @ s ; E
  {{{ (f: File), RET f; path.mk dir fname ↦{q} inode ∗ f ↦ (inode, Read) }}}.
Proof.
  iIntros (Φ) "Hd HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&?&HFS&?)".
  iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?)".
  iDestruct (gen_dir_valid with "Hpaths Hd") as %H'.
  simpl in H'. destruct H' as (σd&Hd&Hf).
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iMod (gen_heap_alloc with "Hfds") as "[Hfds Hp]"; first by eauto.
  iFrame. iApply "HΦ". by iFrame.
Qed.

Lemma wp_close fh m s E :
  {{{ fh ↦ m }}}
    close fh @ s ; E
  {{{ RET tt; True }}}.
Proof.
  iIntros (Φ) "Hd HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&?&HFS&?)".
  iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?)".
  iDestruct (gen_heap_valid with "Hfds Hd") as %H'.
  simpl in H'.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  iMod (gen_heap_dealloc with "Hfds Hd") as "Hfds".
  iFrame. iApply "HΦ". by iFrame.
Qed.

Lemma wp_list_start dir q s E :
  {{{ dir ↦{q} Unlocked }}}
    list_start dir @ s ; E
  {{{ RET tt; dir ↦{q} ReadLocked O }}}.
Proof.
  iIntros (Φ) "Hdl HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&?&HFS&?)".
  iDestruct "HFS" as "(Hents&Hdlocks&Hpaths&Hinodes&Hfds&?&Hdom)".
  iDestruct "Hdom" as %Hdom.
  iDestruct (Count_Heap.gen_heap_valid with "Hdlocks Hdl") as %[s' [Hlookup Hnl]].
  simpl in Hlookup.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; try congruence.
    destruct l0; try congruence; inversion Hhd_err.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  iMod (Count_Heap.gen_heap_readlock with "Hdlocks Hdl") as (s'' Heq) "(Hdlocks&Hdl)".
  inv_step. iFrame. iSplitR "HΦ Hdl"; last first.
  { iApply "HΦ". by iFrame. }
  (* TODO: casework here is silly *)
  destruct s''; try congruence; inversion Hhd; subst.
  * iFrame. simpl.
    iSplitL.
    { iModIntro. iApply Count_Heap.gen_heap_ctx_proper; last auto. intros k.
      simpl. rewrite {1}/insert/Count_Heap.partial_fn_insert//=.
      destruct equal; eauto. subst. by rewrite lookup_insert.
      rewrite lookup_insert_ne //=.
    }
    iPureIntro. rewrite dom_insert_L. rewrite Hdom.
    assert (dir ∈ dom (gset string) σ.(fs).(dirlocks)).
    { apply elem_of_dom. eexists; eauto. }
    set_solver.
  * iFrame. simpl.
    iSplitL.
    { iModIntro. iApply Count_Heap.gen_heap_ctx_proper; last auto. intros k.
      simpl. rewrite {1}/insert/Count_Heap.partial_fn_insert//=.
      destruct equal; eauto. subst. by rewrite lookup_insert.
      rewrite lookup_insert_ne //=.
    }
    iPureIntro. rewrite dom_insert_L. rewrite Hdom.
    assert (dir ∈ dom (gset string) σ.(fs).(dirlocks)).
    { apply elem_of_dom. eexists; eauto. }
    set_solver.
Qed.

Lemma map_to_list_dom_perm {K V} `{Countable K} (m: gmap K V):
  map fst (map_to_list m) ≡ₚ elements (dom (gset K) m).
Proof.
  apply NoDup_Permutation.
  - apply NoDup_fst_map_to_list.
  - apply NoDup_elements.
  - intros k. rewrite elem_of_elements elem_of_dom. split.
    * intros ((?&v)&?&?%elem_of_map_to_list)%elem_of_list_fmap_2.
       simpl in *; subst; eexists; eauto.
    * intros (v&?). apply elem_of_list_fmap.
      exists (k, v); split; eauto.
      rewrite elem_of_map_to_list. eauto.
Qed.

Lemma wp_delete dir fname (S: gset string) (inode: Inode) s E :
  {{{ dir ↦ S ∗ dir ↦ Unlocked ∗ path.mk dir fname ↦ inode }}}
    delete dir fname @ s ; E
  {{{ RET tt; dir ↦ (S ∖ {[ fname ]}) ∗ dir ↦ Unlocked }}}.
Proof.
  iIntros (Φ) "(Hd&Hdl&Hp) HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&?&HFS&?)".
  iDestruct "HFS" as "(Hents&Hdlocks&Hpaths&Hinodes&Hfds&?&Hdom)".
  iDestruct "Hdom" as %Hdom.
  iDestruct (Count_Heap.gen_heap_valid1 with "Hdlocks Hdl") as %?.
  iDestruct (gen_dir_valid with "Hpaths Hp") as %H'.
  simpl in H'. destruct H' as (σd&Hd&Hf).
  iDestruct (gen_heap_valid with "Hents Hd") as %H'.
  rewrite lookup_fmap in H'.
  eapply fmap_Some_1 in H' as (?&?&?).
  subst.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; simpl in *; subst; try congruence.
    inv_step. rewrite Hf in Hhd_err. inversion Hhd_err.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step.
  unfold unwrap in *. simpl in *. inv_step. rewrite Hf in Hhd1. inv_step.
  iFrame. simpl.
  iMod (gen_dir_dealloc with "Hpaths Hp") as "Hpaths"; eauto.
  simpl. iFrame.
  iMod (gen_heap_update _ (dir) _ (dom (gset string) (map_delete fname _)) with "Hents Hd") as "(?&?)".
  rewrite fmap_insert. iFrame.
  simpl. rewrite ?(dom_insert_L_in _ dir) ; last first.
  { apply elem_of_dom. eexists; eauto. }
  iFrame.
  iSplitL ""; auto.
  iApply "HΦ". iFrame. rewrite dom_delete_L. by iFrame.
Qed.

Lemma wp_list_finish dir (S: gset string) s q1 q2 E :
  {{{ dir ↦{q1} S ∗ dir ↦{q2} (ReadLocked O) }}}
    list_finish dir @ s ; E
  {{{ (s: slice.t string) (l: Datatypes.list string), RET s;
      ⌜ (Permutation.Permutation l (elements S)) ⌝ ∗
      s ↦ l ∗ dir ↦{q1} S ∗ dir ↦{q2} Unlocked }}}.
Proof.
  iIntros (Φ) "(Hd&Hdl) HΦ".
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ&HFS&?)".
  iDestruct "HFS" as "(Hents&Hdlocks&Hpaths&Hinodes&Hfds&?&Hdom)".
  iDestruct "Hdom" as %Hdom.
  iDestruct (Count_GHeap.gen_heap_valid with "Hents Hd") as %Hlookup1.
  rewrite lookup_fmap in Hlookup1.
  eapply fmap_Some_1 in Hlookup1 as (?&?&?).
  subst.
  iDestruct (Count_Heap.gen_heap_valid2 with "Hdlocks Hdl") as %[s' [Hlookup2 Hl]].
  apply Count_Heap.Cinl_included_nat' in Hl as (m&?&?); subst.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro.
    inv_step; subst; try congruence.
    - destruct l0; simpl in *; try congruence. destruct num; try inversion Hhd_err.
      inv_step; lia.
    - eapply createSlice_non_err; eauto.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  iMod (Count_Heap.gen_heap_readunlock with "Hdlocks Hdl") as (s'' Heq) "(Hdlocks&Hdl)".
  inversion Hstep; subst.
  inv_step. unfold createSlice in Htl. do 2 (inv_step; intuition).
  match goal with
    | [ H:  unwrap  _ ?x1 (Val ?x2 ?res) |- _] =>
      assert (x1 = x2)
  end.
  { destruct s''; inversion Hhd0; subst; eauto. }
  subst.
  iMod (gen_typed_heap_alloc with "Hσ") as "(Hσ&Hp)"; eauto.
  iFrame. iSplitR "HΦ Hd Hdl Hp"; last first.
  { iApply "HΦ". iFrame. iSplitR; last first. iModIntro.
    iExists _. iFrame. iPureIntro.
    rewrite /getSliceModel sublist_lookup_all //= app_length //=. iPureIntro.
    rewrite -map_to_list_dom_perm //.
  }
  simpl.
  iFrame.
  iSplitL.
  { iModIntro. iApply Count_Heap.gen_heap_ctx_proper; last auto. intros k.
    simpl. rewrite {1}/insert/Count_Heap.partial_fn_insert//=.
    destruct s''; inversion Hhd0; inv_step; destruct equal; eauto; subst;
    rewrite ?lookup_insert ?lookup_insert_ne //=.
  }
  iPureIntro. rewrite dom_insert_L. rewrite Hdom.
    assert (dir ∈ dom (gset string) σ.(fs).(dirlocks)).
    { apply elem_of_dom. eexists; eauto. }
    set_solver.
Qed.

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
  destruct H0 as ((?&?)&?).
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

Lemma slice_agree {T} (p: slice.t T) v1 v2 q1 q2:
  p ↦{q1} v1 -∗ p ↦{q2} v2 -∗ ⌜ v1 = v2 ⌝.
Proof.
  iIntros "Hp1 Hp2".
  iDestruct "Hp1" as (l1 ?) "Hp1".
  iDestruct "Hp2" as (l2 ?) "Hp2".
  iAssert (⌜l1 = l2⌝)%I with "[Hp1 Hp2]" as %Heq.
  { iApply (@Count_Typed_Heap.mapsto_agree _ _ _ _ _ (go_heap_inG) (Ptr.Heap T)
                  with "Hp1 Hp2"). }
  subst. iPureIntro. congruence.
Qed.

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
  (∃ (n: Z) stat, lock_mapsto l n stat ∗
    match stat with
      | Unlocked => ⌜ n = O ⌝ ∗ P O
      | ReadLocked n' => ⌜ n = S n' ⌝ ∗ P (S n')
      | Locked => ⌜ n = (-1)%Z ⌝
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
  lock_mapsto l 1 Locked.

Definition rlocked (l: LockRef) : iProp Σ :=
  lock_mapsto l (-1) Unlocked.

Global Instance inhabited_LockStatus: Inhabited LockStatus.
Proof. eexists. exact Unlocked. Qed.

Global Instance inhabited_LockMode: Inhabited LockMode.
Proof. eexists. exact Reader. Qed.

Lemma wlocked_wlocked l:
  wlocked l -∗ wlocked l -∗ False.
Proof. rewrite /wlocked/lock_mapsto. apply Count_Typed_Heap.mapsto_valid_locked; lia. Qed.

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
    subst.
    iDestruct (read_split_join2 (T := Ptr.Lock) with "Hl") as "(Hl&?)".
    iSplitL "Hl HP".
    { iNext. iExists (S (S num)), (ReadLocked (S num)). subst. by iFrame. }
    iApply "HΦ"; iFrame.
  }
  {
    iMod (gen_typed_heap_readlock (Ptr.Lock) with "Hσ H") as (s Heq) "(Hσ&Hl)".
    simpl; inv_step. iFrame.
    iDestruct "Hstat" as "(%&HP)".
    iMod ("HPQ1" with "HP") as "(HP&HQ)".
    do 2 iModIntro.
    subst.
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
  iDestruct (read_split_join3 (T := Ptr.Lock) l O with "Hl") as "(?&Hl)".
  iSplitL "Hl".
  { iNext. iExists (-1)%Z, Locked. by iFrame. }
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
    destruct l0; eauto; try congruence.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inv_step. subst; simpl in *.
  iMod (gen_typed_heap_readlock (Ptr.Map T) with "Hσ Hi") as (s' Heq) "(Hσ&Hl)".
  iFrame.
  destruct l0; simpl in *; try congruence;
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
  destruct l0; simpl in *; try congruence;
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
