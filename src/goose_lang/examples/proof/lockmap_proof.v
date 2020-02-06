From iris.proofmode Require Import coq_tactics reduction.
From Goose.github_com.mit_pdos.goose_nfsd Require Import lockmap.
From Perennial.goose_lang Require Import wpc_proofmode.
From Perennial.goose_lang Require Import basic_triples.
From Perennial.goose_lang Require Import slice.
From Perennial.goose_lang Require Import locks.
From Perennial.goose_lang Require Import map_triples.
From Perennial.goose_lang Require Import lib.spin_lock.
Import uPred.

Hint Rewrite app_length @drop_length @take_length @fmap_length
     @replicate_length : len.
Hint Rewrite @vec_to_list_length : len.
Hint Rewrite @insert_length : len.
Hint Rewrite u64_le_length : len.

Ltac word := try lazymatch goal with
                 | |- envs_entails _ _ => iPureIntro
                 end; Integers.word.

Ltac len := autorewrite with len; try word.


Section heap.
Context `{!heapG Σ} `{!lockG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types stk : stuckness.

Definition lockN : namespace := nroot .@ "lockShard".

Definition is_lockShard_inner (mptr : loc) :=
  (∃ m mv def,
    mptr ↦ Free mv ∗
    ⌜map_val mv = Some (m, def)⌝
  )%I.

Definition is_lockShard (ls : loc) :=
  (∃ l γl mptr,
    is_lock lockN γl l (is_lockShard_inner mptr) ∗
    ls ↦[structTy lockShard.S] (l, #mptr))%I.

Theorem wp_mkLockShard :
  {{{ True }}}
    mkLockShard #()
  {{{ ls, RET #ls; is_lockShard ls }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /mkLockShard.
  wp_call.

  wp_apply wp_NewMap.
  iIntros (m mv def) "[Hmap %]".
  wp_pures.

  wp_bind (newlock _).
  iApply (newlock_spec _ (is_lockShard_inner _) with "[Hmap]").
  {
    iExists _, _, _.
    iFrame.
    auto.
  }
  iNext.
  iIntros (lk γl) "Hlock".
  wp_pures.

  iDestruct (lock.is_lock_ty with "Hlock") as "%".
  wp_apply (wp_alloc _ _ (structTy lockShard.S)).
  { repeat econstructor. auto. }
  iIntros (ls) "Hls".
  wp_pures.

  iApply "HΦ".
  iExists _, _, _.
  iFrame.
Qed.

Theorem wp_lockShard__acquire ls (addr : u64) (id : u64) :
  {{{ is_lockShard ls }}}
    lockShard__acquire #ls #addr #id
  {{{ RET #(); is_lockShard ls }}}.
Proof.
  iIntros (Φ) "Hls HΦ".
  iDestruct "Hls" as (l γl mptr) "(#Hlock&Hls)".

  wp_call.

  (* What's the right way to deal with loadField? *)
  Transparent loadField.
  rewrite /struct.loadF /=.
  iDestruct "Hls" as "[(Hl & Hm) %]".
  iDestruct (lock.is_lock_ty with "Hlock") as "%".
  inversion H0; subst.
  inversion H; subst.
  inversion H7; subst.
  rewrite /=.
  wp_steps.
  iDestruct "Hl" as "[Hl _]".
  iDestruct "Hm" as "[Hm _]".
  wp_load.

  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hinner]".

  wp_pures.
  wp_apply ((wp_forBreak
      (is_lockShard_inner mptr ∗ locked γl ∗ (ls +ₗ 1%nat) ↦ Free #mptr)
      (is_lockShard_inner mptr ∗ locked γl ∗ (ls +ₗ 1%nat) ↦ Free #mptr)
    ) with "[] [$Hinner $Hlocked $Hm]").
  2: {
    iIntros "(Hinner & Hlocked & Hm)".
    wp_pures.
    wp_load.
    wp_apply (release_spec with "[$Hlock $Hlocked $Hinner]").
    iIntros.
    iApply "HΦ".

    iExists _, _, _.
    iSplitL "Hlock"; [ iApply "Hlock" | ].
    rewrite /struct_mapsto.
    (* XXX *)
    admit.
  }

  iIntros (Φloop) "!> (Hinner & Hlocked & Hm) HΦloop".
  wp_pures.

  (* XXX annoying that the proof has to keep specifying these
    types, when the goose-generated .v file already has them! *)
  wp_apply (wp_alloc _ _ (refT (structTy lockState.S))).
  { val_ty. }
  iIntros (state) "Hstate".
  wp_pures.

  wp_load.

  iDestruct "Hinner" as (m mv def) "[Hmptr %]".
  wp_apply (wp_MapGet with "[$Hmptr]"); auto.
  iIntros (v ok) "[% Hmptr]".

  wp_pures.
  (* XXX annoying that i have to keep unfolding allocation
    types even when i'm not allocating a struct.. *)
  (* wp_store. *)

Abort.

Theorem wp_lockShard__release ls (addr : u64) :
  {{{ is_lockShard ls }}}
    lockShard__release #ls #addr
  {{{ RET #(); is_lockShard ls }}}.
Proof.
  iIntros (Φ) "Hls HΦ".
  iDestruct "Hls" as (l γl mptr) "(Hlock&Hls)".
  wp_call.

  (* What's the right way to deal with loadField? *)
  Transparent loadField.
  rewrite /struct.loadF /=.
  iDestruct "Hls" as "[(Hl & Hm) %]".
  iDestruct (lock.is_lock_ty with "Hlock") as "%".
  inversion H0; subst.
  inversion H; subst.
  inversion H7; subst.
  rewrite /=.
  wp_steps.
  iDestruct "Hl" as "[Hl _]".
  iDestruct "Hm" as "[Hm _]".
  replace (1 * int.val 0) with (0) by len.
  wp_load.

  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hinner]".
  iDestruct "Hinner" as (m mv def) "[Hmptr %]".

  wp_pures.
  replace (1 * int.val (1 + 0)) with (1) by len.
  wp_load.
  wp_bind (map.MapGet _ _).
  iApply (wp_MapGet with "[Hmptr]").
  {
    iFrame.
    auto.
  }
  iNext.
  iIntros (v ok) "[% Hmptr]".
  wp_pures.

  (* need some invariant about present map items *)

Abort.

End heap.
