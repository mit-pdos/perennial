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

Notation heap_inG := (gen_heapG (sigT (Ptr.t)) (sigT ptrModel)).

Class gooseG Σ := GooseG {
                     go_invG : invG Σ;
                     go_heap_inG :> heap_inG Σ;
                     (* Maybe actually we do want a gmap version for these *)
                     go_fs_inG :> gen_heapG string (List.list byte) Σ;
                     go_fds_inG :> gen_heapG File (List.list byte) Σ;
                     go_treg_inG :> tregG Σ;
                   }.

Definition heap_interp {Σ} (hM: heap_inG Σ) :=
  (λ s, (gen_heap_ctx (SemanticsHelpers.dynMap (allocs s.(heap))) (hG := hM)))%I.

Definition goose_interp {Σ} {hM: heap_inG Σ} {tr: tregG Σ} :=
  (λ s, thread_count_interp (fst s) ∗ heap_interp hM (snd s))%I.

Instance gooseG_irisG `{gooseG Σ} : irisG GoLayer.Op GoLayer.Go.l Σ :=
  {
    iris_invG := go_invG;
    state_interp := goose_interp
  }.

Definition ptr_mapsto `{gooseG Σ} {T} (l: ptr T) (q: nat) (v: Datatypes.list T) : iProp Σ :=
   mapsto (existT (Ptr.Heap T) l) q (existT (Ptr.Heap T) (Unlocked, v)).

(*
Definition path_mapsto `{baseG Σ} (p: Path) (bs: ByteString) : iProp Σ.
Admitted.

Definition fd_mapsto `{baseG Σ} (fh: Fd) (s:Path * FS.OpenMode) : iProp Σ.
Admitted.
*)

Class GenericMapsTo `{gooseG Σ} (Addr:Type) :=
  { ValTy : Type;
    generic_mapsto : Addr -> nat → ValTy -> iProp Σ; }.

Instance ptr_gen_mapsto `{gooseG Σ} T : GenericMapsTo (ptr T)
  := {| generic_mapsto := ptr_mapsto; |}.

Notation "l ↦{ q } v" := (generic_mapsto l q v)
                      (at level 20) : bi_scope.
Notation "l ↦ v" := (generic_mapsto l 0 v)
                      (at level 20) : bi_scope.



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

Lemma wp_ptrStore_start {T} s E (p: ptr T) off l l' v :
  list_nth_upd l off v = Some l' →
  {{{ ▷ p ↦ l }}}
   Call (InjectOp.inject (PtrStore p off v SemanticsHelpers.Begin)) @ s ; E
   {{{ RET tt; mapsto (existT (Ptr.Heap T) p) 0 (existT (Ptr.Heap T) (Locked, l)) }}}.
Proof.
  intros Hupd.
  iIntros (Φ) ">Hi HΦ". rewrite /ptrStore/nonAtomicWriteOp.
  iApply wp_lift_call_step.
  iIntros ((n, σ)) "(?&Hσ)".
  iDestruct (@gen_heap_valid with "Hσ Hi") as %?.
  simpl in H0.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro. intros Hsnd.
    rewrite /snd_lift in Hsnd.
    inversion Hsnd. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H1.
    subst. inversion H3.
    rewrite /readSome in H1.
    rewrite /getAlloc in H1.
    erewrite SemanticsHelpers.getDyn_lookup in H1; eauto.
    congruence.
    destruct H1 as ((?&?)&?&?&?).
    rewrite /readSome in H1.
    rewrite /getAlloc in H1.
    erewrite SemanticsHelpers.getDyn_lookup in H1; eauto.
    inversion H1. subst.
    inversion H2.
    rewrite /readSome in H4.
    simpl in H4. congruence.
    destruct H4 as (?&?&?&?).
    rewrite //= in H4.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inversion H1. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H2.
    subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H7.
    subst.
  destruct H6 as (?&?&?&?).
  rewrite /readSome in H2. destruct x.
  destruct H3 as (?&?&?&?).
  rewrite /getAlloc in H2.
    erewrite SemanticsHelpers.getDyn_lookup in H2; eauto.
    inversion H2; subst.
    inversion H4. subst.
    simpl in *.
    destruct Hstep. rewrite /goose_interp. iFrame.
    rewrite /heap_interp//=.
  inversion H3. subst.

  unshelve (iMod (@gen_heap_update with "Hσ Hi") as "[$ Hi]").
  iModIntro.
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
  iDestruct (@gen_heap_valid with "Hσ Hi") as %?.
  simpl in H0.
  iModIntro. iSplit.
  { destruct s; auto. iPureIntro. intros Hsnd.
    rewrite /snd_lift in Hsnd.
    inversion Hsnd. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H1.
    subst. inversion H3.
    rewrite /readSome in H1.
    rewrite /getAlloc in H1.
    erewrite SemanticsHelpers.getDyn_lookup in H1; eauto.
    congruence.
    destruct H1 as ((?&?)&?&?&?).
    rewrite /readSome in H1.
    rewrite /getAlloc in H1.
    erewrite SemanticsHelpers.getDyn_lookup in H1; eauto.
    inversion H1. subst.
    inversion H2.
    rewrite /readSome in H4.
    simpl in H4. congruence.
    destruct H4 as (?&?&?&?).
    rewrite //= in H4.
    rewrite /readSome in H4. inversion H4; subst.
    inversion H5.
    rewrite /readSome in H6.
    rewrite Hupd in H6. congruence.
    destruct H6 as (?&?&?&?).
    rewrite /readSome in H6.
    rewrite Hupd in H6. inversion H6. subst.
    inversion H7.
  }
  iIntros (e2 (n', σ2) Hstep) "!>".
  inversion Hstep; subst.
  inversion H1. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H2.
    subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H7.
    subst.
  destruct H6 as (?&?&?&?).
  rewrite /readSome in H2. destruct x.
  destruct H3 as (?&?&?&?).
  rewrite /getAlloc in H2.
    erewrite SemanticsHelpers.getDyn_lookup in H2; eauto.
    inversion H2; subst.
    inversion H4. subst.
    simpl in *.
    destruct Hstep. rewrite /goose_interp. iFrame.
    rewrite /heap_interp//=.
  inversion H3. subst.
  destruct H5 as (?&?&?).
  rewrite /readSome in H5. rewrite Hupd in H5. inversion H5. subst.
  rewrite /updAllocs in H8. inversion H8. subst. simpl in *.
  unshelve (iMod (@gen_heap_update with "Hσ Hi") as "[$ Hi]").
  iModIntro. by iApply "HΦ".
Qed.

Lemma wp_writePtr {T} s E (p: ptr T) v' l v :
  {{{ ▷ p ↦ (v' :: l) }}} writePtr p v @ s; E {{{ RET tt; p ↦ (v :: l) }}}.
Proof. iIntros (Φ) ">Hi HΦ". iApply (wp_ptrStore with "Hi"); eauto. Qed.

End lifting.