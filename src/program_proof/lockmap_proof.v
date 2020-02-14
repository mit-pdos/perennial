From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.goose_nfsd Require Import lockmap.

Hint Rewrite app_length @drop_length @take_length @fmap_length
     @replicate_length : len.
Hint Rewrite @vec_to_list_length : len.
Hint Rewrite @insert_length : len.
Hint Rewrite u64_le_length : len.

Ltac word := try lazymatch goal with
                 | |- envs_entails _ _ => iPureIntro
                 end; Integers.word.

Ltac len := autorewrite with len; try word.

(*
Locate "[∗".
Search _ loc_add.
Print big_sepM2.
Print big_sepM2_aux.
Print big_sepM2_def.
*)

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!gen_heapPreG u64 bool Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "lockShard".
Definition lockshardN : namespace := nroot .@ "lockShardMem".

Definition locked (hm : gen_heapG u64 bool Σ) (addr : u64) : iProp Σ :=
  ( mapsto (hG := hm) addr 1 true )%I.

Definition lockShard_addr gh (shardlock : loc) (addr : u64) (gheld : bool) (ptrVal : val) (covered : gset u64) (P : u64 -> iProp Σ) :=
  ( ∃ (lockStatePtr : loc) owner (cond : loc) waiters,
      ⌜ ptrVal = #lockStatePtr ⌝ ∗
      lockStatePtr ↦[structTy lockState.S] (owner, #gheld, #cond, waiters) ∗
      cond ↦[lockRefT] #shardlock ∗
      ⌜ addr ∈ covered ⌝ ∗
      ( ⌜ gheld = true ⌝ ∨
        ( ⌜ gheld = false ⌝ ∗ locked gh addr ∗ P addr ) )
  )%I.

Definition is_lockShard_inner (mptr : loc) (shardlock : loc) (ghostHeap : gen_heapG u64 bool Σ) (covered : gset u64) (P : u64 -> iProp Σ) : iProp Σ :=
  ( ∃ m def ghostMap,
      is_map mptr (m, def) ∗
      gen_heap_ctx (hG := ghostHeap) ghostMap ∗
      ( [∗ map] addr ↦ gheld; lockStatePtrV ∈ ghostMap; m,
          lockShard_addr ghostHeap shardlock addr gheld lockStatePtrV covered P ) ∗
      ( [∗ set] addr ∈ covered ∖ (dom _ m),
          P addr )
  )%I.

Definition is_lockShard (ls : loc) (ghostHeap : gen_heapG u64 bool Σ) (covered : gset u64) (P : u64 -> iProp Σ) :=
  ( ∃ (shardlock mptr : loc) γl,
      inv lockshardN (ls ↦[structTy lockShard.S] (#shardlock, #mptr)) ∗
      is_lock lockN γl #shardlock (is_lockShard_inner mptr shardlock ghostHeap covered P)
  )%I.

Global Instance is_lockShard_persistent ls gh (P : u64 -> iProp Σ) c : Persistent (is_lockShard ls gh c P).
Proof. apply _. Qed.
(*
Global Instance is_lockShard_ne ls gh c : ∀ n, Proper (Pointwise (dist n) ==> dist n) (is_lockShard ls gh c).
Proof. apply _. Qed.
*)

Opaque zero_val.

Theorem wp_mkLockShard covered (P : u64 -> iProp Σ) :
  {{{ [∗ set] a ∈ covered, P a }}}
    mkLockShard #()
  {{{ ls gh, RET #ls; is_lockShard ls gh covered P }}}.
Proof using gen_heapPreG0 heapG0 lockG0 Σ.
  iIntros (Φ) "Hinit HΦ".
  rewrite /mkLockShard.
  wp_call.

  wp_apply wp_NewMap.
  iIntros (mref) "Hmap".
  wp_pures.

  wp_bind (newlock _).
  iApply lock.new_free_lock; auto.

  iNext.
  iIntros (shardlock) "Hfreelock".

  wp_pures.
  iDestruct (lock.is_free_lock_ty with "Hfreelock") as "%".
  wp_apply (wp_alloc _ _ (structTy lockShard.S)); first by eauto.
  iIntros (ls) "Hls".

  iMod (gen_heap_init (∅: gmap u64 bool)) as (hG) "Hheapctx".
  rewrite -wp_fupd.

  wp_pures.

  iAssert (is_lockShard_inner mref shardlock hG covered P) with "[Hinit Hmap Hheapctx]" as "Hinner".
  {
    iExists _, _, _.
    iFrame.

    iSplitR; eauto.

    rewrite dom_empty_L difference_empty_L.
    iFrame.
  }

  iMod (alloc_lock with "Hfreelock Hinner") as (γ) "Hlock".
  iMod (inv_alloc lockshardN _ (ls ↦[struct.t lockShard.S] (#shardlock, #mref)) with "Hls") as "Hls".
  iModIntro.

  iApply "HΦ".
  iExists _, _, _.
  iFrame.
Qed.

Theorem wp_load_lockShard_0 (ls shardlock mptr : loc) :
  {{{ inv lockshardN (ls ↦[struct.t lockShard.S] (#shardlock, #mptr)) }}}
    Load #(ls +ₗ 0)
  {{{ RET #shardlock; True }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ".
  iInv lockshardN as "Hls".
  iDestruct "Hls" as "[([Hl _] & [Hm _]) Ht]".
  rewrite /=.
  wp_load.
  iModIntro.
  iSplitL "Hl Hm Ht".
  {
    iModIntro.
    iFrame.
    rewrite /=.
    done.
  }
  iApply "HΦ".
  auto.
Qed.

Theorem wp_load_lockShard_1 (ls shardlock mptr : loc) :
  {{{ inv lockshardN (ls ↦[struct.t lockShard.S] (#shardlock, #mptr)) }}}
    Load #(ls +ₗ 1)
  {{{ RET #mptr; True }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ".
  iInv lockshardN as "Hls".
  iDestruct "Hls" as "[([Hl _] & [Hm _]) Ht]".
  rewrite /=.
  wp_load.
  iModIntro.
  iSplitL "Hl Hm Ht".
  {
    iModIntro.
    iFrame.
    rewrite /=.
    done.
  }
  iApply "HΦ".
  auto.
Qed.

Ltac inv_ty :=
  repeat match goal with
         | [ H: val_ty _ _ |- _ ] => inversion H; subst; clear H
         | [ H: lit_ty _ _ |- _ ] => inversion H; subst; clear H
         end.

Theorem wp_store_lockState_1 (lsp : loc) owner held cond waiters (v : bool) :
  {{{ lsp ↦[struct.t lockState.S] (owner, held, cond, waiters) }}}
    #(lsp +ₗ 1) <- #v
  {{{ RET #(); lsp ↦[struct.t lockState.S] (owner, #v, cond, waiters) }}}.
Proof.
  iIntros (Φ) "[Hlsp %] HΦ".
  inv_ty.
  iDestruct "Hlsp" as "[[[[Howner _] [Hheld _]] [Hcond _]] [Hwaiters _]]".
  rewrite /=.
  wp_store.
  iApply "HΦ".
  iSplitL.
  {
    rewrite /=.
    iFrame.
  }
  iPureIntro.
  val_ty.
Qed.

Theorem wp_load_lockState_2 (lsp : loc) owner held cond waiters :
  {{{ lsp ↦[struct.t lockState.S] (owner, held, cond, waiters) }}}
    Load #(lsp +ₗ 2)
  {{{ RET cond; lsp ↦[struct.t lockState.S] (owner, held, cond, waiters) }}}.
Proof.
  iIntros (Φ) "Hlsp HΦ".
  iDestruct "Hlsp" as "[Hlsp %]".
  inv_ty.
  iDestruct "Hlsp" as "[[[[Howner _] [Hheld _]] [Hcond _]] [Hwaiters _]]".
  rewrite /=.
  wp_load.
  iApply "HΦ".
  iSplitL; eauto.
  rewrite /=.
  iFrame.
Qed.

Theorem wp_load_lockState_3 (lsp : loc) owner held cond waiters :
  {{{ lsp ↦[struct.t lockState.S] (owner, held, cond, waiters) }}}
    Load #(lsp +ₗ 3)
  {{{ (nwaiters : u64), RET #nwaiters; ⌜waiters = #nwaiters⌝ ∗ lsp ↦[struct.t lockState.S] (owner, held, cond, waiters) }}}.
Proof.
  iIntros (Φ) "Hlsp HΦ".
  iDestruct "Hlsp" as "[Hlsp %]".
  inv_ty.
  iDestruct "Hlsp" as "[[[[Howner _] [Hheld _]] [Hcond _]] [Hwaiters _]]".
  rewrite /=.
  wp_load.
  iApply "HΦ".
  iSplitR; eauto.
  iSplitL; eauto.
  rewrite /=.
  iFrame.
Qed.

Theorem wp_lockShard__acquire ls gh covered (addr : u64) (id : u64) (P : u64 -> iProp Σ) :
  {{{ is_lockShard ls gh covered P ∗
      ⌜addr ∈ covered⌝ }}}
    lockShard__acquire #ls #addr #id
  {{{ RET #(); P addr ∗ locked gh addr }}}.
Proof.
  iIntros (Φ) "[Hls %] HΦ".
  iDestruct "Hls" as (shardlock mptr γl) "(#Hls&#Hlock)".

  wp_call.

  (* What's the right way to deal with loadField? *)
  Transparent loadField.
  rewrite /struct.loadF /=.

  wp_pures.
  change (1 * int.val 0) with 0.
  wp_apply wp_load_lockShard_0; [done|].

  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hinner]".

  wp_pures.
  wp_apply (wp_forBreak
    (is_lockShard_inner mptr shardlock gh covered P)
    (is_lockShard_inner mptr shardlock gh covered P ∗ P addr ∗ locked gh addr)
    with "[] [$Hinner]").

  {
    iIntros (Φloop) "!> Hinner HΦloop".
    iDestruct "Hinner" as (m def gm) "(Hmptr & Hghctx & Haddrs & Hcovered)".
    wp_pures.
    wp_apply wp_alloc_zero.
    iIntros (state) "Hstate".
    wp_pures.

    replace (1 * int.val (1 + 0)) with (1) by len.
    wp_apply wp_load_lockShard_1; [done|].

    wp_apply (wp_MapGet with "[$Hmptr]"); auto.
    iIntros (v ok) "[% Hmptr]".

    wp_pures.
    iDestruct "Hstate" as "[[Hstate _] _]". rewrite /=.
    rewrite loc_add_0.
    wp_store.

    wp_pures.
    wp_load.

    (* XXX *)
    admit.
  }

  {
    iIntros "(Hinner & Hp & Haddrlocked)".

    wp_pures.
    replace (1 * int.val 0) with (0) by len.
    wp_apply wp_load_lockShard_0; [done|].

    wp_apply (release_spec with "[Hlocked Hinner]").
    {
      iSplitR. { iApply "Hlock". }
      iFrame.
    }

    iApply "HΦ".
    iFrame.
  }


(*
*)
Abort.
  

Lemma big_sepM2_lookup_1_some 
    (PROP : bi) (K : Type) (EqDecision0 : EqDecision K) (H : Countable K)
    (A B : Type) (Φ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B)
    (i : K) (x1 : A)
    (_ : forall x2 : B, Absorbing (Φ i x1 x2)) :
  m1 !! i = Some x1 ->
    ( ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
        ⌜∃ x2, m2 !! i = Some x2⌝ )%I.
Proof.
  intros.
  iIntros "H".
  iDestruct (big_sepM2_lookup_1 with "H") as (x2) "[% _]"; eauto.
Qed.

Theorem wp_lockShard__release ls (addr : u64) (P : u64 -> iProp Σ) covered gh :
  {{{ is_lockShard ls gh covered P ∗ P addr ∗ locked gh addr }}}
    lockShard__release #ls #addr
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(Hls & Hp & Haddrlocked) HΦ".
  iDestruct "Hls" as (shardlock mptr γl) "(#Hls&#Hlock)".
  wp_call.

  (* What's the right way to deal with loadField? *)
  Transparent loadField.
  rewrite /struct.loadF /=.

  wp_pures.
  replace (1 * int.val 0) with (0) by len.
  wp_bind (Load _).
  iApply wp_load_lockShard_0; [done|].
  iNext.
  iIntros "_".

  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hinner]".
  iDestruct "Hinner" as (m def gm) "(Hmptr & Hghctx & Haddrs & Hcovered)".

  wp_pures.
  replace (1 * int.val (1 + 0)) with (1) by len.
  wp_apply wp_load_lockShard_1; [done|].

  wp_apply (wp_MapGet with "Hmptr").
  iIntros (v ok) "[% Hmptr]".

  wp_pures.

  rewrite /locked.
  iDestruct (gen_heap_valid with "Hghctx Haddrlocked") as %Hsome.
  iDestruct (big_sepM2_lookup_1_some with "Haddrs") as %Hsome2; eauto.
  destruct Hsome2.

  iDestruct (big_sepM2_delete with "Haddrs") as "[Haddr Haddrs]"; eauto.

  iDestruct "Haddr" as (lockStatePtr owner cond waiters) "[-> (Hlockstateptr & Hcond & [% Hxx])]".

  rewrite /map_get H0 /= in H.
  inversion H; clear H; subst.

  Transparent storeField.
  rewrite /struct.storeF /=.

  wp_pures.
  replace (1 * int.val (1 + 0)) with (1) by len.
  wp_apply (wp_store_lockState_1 with "Hlockstateptr").
  iIntros "Hlockstateptr".

  wp_pures.
  replace (1 * int.val (1 + (1 + (1 + 0)))) with (3) by len.
  wp_apply (wp_load_lockState_3 with "Hlockstateptr").
  iIntros (nwaiters) "[-> Hlockstateptr]".

  wp_pures.
  destruct (bool_decide (int.val 0 < int.val nwaiters)).

  {
    wp_pures.
    replace (1 * int.val (1 + (1 + 0))) with (2) by len.
    wp_apply (wp_load_lockState_2 with "Hlockstateptr").
    iIntros "Hlockstateptr".

    wp_apply (lock.wp_condSignal with "[Hcond]").
    {
      iExists _.
      iDestruct "Hcond" as "[[Hcond _] %]".
      rewrite /=.
      rewrite loc_add_0.
      iFrame.
      iApply "Hlock".
    }

    iIntros "Hcond".
    wp_pures.

    replace (1 * int.val 0) with (0) by len.
    wp_bind (Load _).
    iApply wp_load_lockShard_0; [done|].
    iNext.
    iIntros "_".

    wp_apply (release_spec with "[Hlock Hlocked Hp Haddrlocked Hghctx Hcovered Hmptr Haddrs Hlockstateptr Hcond]").
    {
      iFrame.
      iSplitR.
      { iApply "Hlock". }
      iExists m, _, gm.
      iFrame.

      admit.
    }

    iApply "HΦ".
    auto.
  }

  {
    wp_pures.
    replace (1 * int.val (1 + 0)) with (1) by len.
    wp_apply wp_load_lockShard_1; [done|].

    wp_pures.
    wp_apply (wp_MapDelete with "[$Hmptr]").
    iIntros "Hmptr".

    wp_pures.

    replace (1 * int.val 0) with (0) by len.
    wp_apply wp_load_lockShard_0; [done|].

    wp_apply (release_spec with "[Hlock Hlocked Hp Haddrlocked Hghctx Hcovered Hmptr Haddrs Hlockstateptr Hcond]").
    {
      iFrame.
      iSplitR.
      { iApply "Hlock". }
      iExists _, _, (delete addr gm).
      iFrame.
      (* don't have a lemma for gen_heap deletion.. *)
      iSplitL "Hghctx". { admit. }

      rewrite dom_delete_L.
      admit.
    }

    iApply "HΦ".
    auto.
  }

Abort.

End heap.
