From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import deletable_heap.
From Goose.github_com.mit_pdos.goose_nfsd Require Import lockmap.
From Perennial.goose_lang.lib Require Import wp_store.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

From Perennial.Helpers Require Import NamedProps.

Local Transparent load_ty store_ty.

Ltac word := try lazymatch goal with
                 | |- envs_entails _ _ => iPureIntro
                 end; Integers.word.

Ltac len := autorewrite with len; try word.

Section heap.
Context `{!heapG Σ}.
Context `{!gen_heapPreG u64 bool Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "lockShard".
Definition lockshardN : namespace := nroot .@ "lockShardMem".

Definition locked (hm : gen_heapG u64 bool Σ) (addr : u64) : iProp Σ :=
  ( mapsto (hG := hm) addr 1 true )%I.

Definition lockShard_addr gh (shardlock : loc) (addr : u64) (gheld : bool)
           (lockStatePtr : loc) (covered : gset u64) (P : u64 -> iProp Σ) :=
  ( ∃ (cond : loc) (nwaiters : u64),
      "held" ∷ lockStatePtr ↦[lockState.S :: "held"] #gheld ∗
      "cond" ∷ lockStatePtr ↦[lockState.S :: "cond"] #cond ∗
      "waiters" ∷ lockStatePtr ↦[lockState.S :: "waiters"] #nwaiters ∗
      "#Hcond" ∷ lock.is_cond cond #shardlock ∗
      "%Hcovered" ∷ ⌜ addr ∈ covered ⌝ ∗
      "Hwaiters" ∷ ( ⌜ gheld = true ⌝ ∨
        ( ⌜ gheld = false ⌝ ∗ mapsto (hG := gh) addr 1 false ∗ P addr ) )
  )%I.

Definition is_lockShard_inner (mptr : loc) (shardlock : loc)
           (ghostHeap : gen_heapG u64 bool Σ) (covered : gset u64) (P : u64 -> iProp Σ) : iProp Σ :=
  ( ∃ (m: Map.t loc) ghostMap,
      is_map mptr m ∗
      gen_heap_ctx (hG := ghostHeap) ghostMap ∗
      ( [∗ map] addr ↦ gheld; lockStatePtrV ∈ ghostMap; m,
          lockShard_addr ghostHeap shardlock addr gheld lockStatePtrV covered P ) ∗
      ( [∗ set] addr ∈ covered,
          ⌜m !! addr = None⌝ → P addr )
  )%I.

Definition is_lockShard (ls : loc) (ghostHeap : gen_heapG u64 bool Σ) (covered : gset u64) (P : u64 -> iProp Σ) : iProp Σ :=
  ( ∃ (shardlock mptr : loc),
      "#Hls_mu" ∷ readonly (ls ↦[lockShard.S :: "mu"] #shardlock) ∗
      "#Hls_state" ∷ readonly (ls ↦[lockShard.S :: "state"] #mptr) ∗
      "#Hlock" ∷ is_lock lockN #shardlock (is_lockShard_inner mptr shardlock ghostHeap covered P)
  )%I.

Global Instance is_lockShard_persistent ls gh (P : u64 -> iProp Σ) c : Persistent (is_lockShard ls gh c P).
Proof. apply _. Qed.

Opaque zero_val.

Theorem wp_mkLockShard covered (P : u64 -> iProp Σ) :
  {{{ [∗ set] a ∈ covered, P a }}}
    mkLockShard #()
  {{{ ls gh, RET #ls; is_lockShard ls gh covered P }}}.
Proof using gen_heapPreG0 heapG0 Σ.
  iIntros (Φ) "Hinit HΦ".
  rewrite /mkLockShard.
  wp_pures.

  wp_apply (wp_NewMap loc).
  iIntros (mref) "Hmap".
  wp_pures.

  wp_apply wp_new_free_lock; auto.

  iIntros (shardlock) "Hfreelock".

  wp_pures.
  iDestruct (is_free_lock_ty with "Hfreelock") as "%".
  wp_apply wp_allocStruct; first by eauto.
  iIntros (ls) "Hls".

  iMod (gen_heap_init (∅: gmap u64 bool)) as (hG) "Hheapctx".
  rewrite -wp_fupd.

  wp_pures.

  iAssert (is_lockShard_inner mref shardlock hG covered P) with "[Hinit Hmap Hheapctx]" as "Hinner".
  {
    iExists _, _.
    iFrame.

    iSplitR; eauto.

    iApply big_sepS_mono; last iFrame.
    iIntros; iFrame.
  }

  iMod (alloc_lock with "Hfreelock Hinner") as "Hlock".
  iDestruct (struct_fields_split with "Hls") as "(Hmu & Hstate & _)".
  iMod (readonly_alloc_1 with "Hmu") as "mu".
  iMod (readonly_alloc_1 with "Hstate") as "Hstate".
  iModIntro.

  iApply "HΦ".
  iExists _, _.
  iFrame.
Qed.

Theorem wp_lockShard__acquire ls gh covered (addr : u64) (P : u64 -> iProp Σ) :
  {{{ is_lockShard ls gh covered P ∗
      ⌜addr ∈ covered⌝ }}}
    lockShard__acquire #ls #addr
  {{{ RET #(); P addr ∗ locked gh addr }}}.
Proof.
  iIntros (Φ) "[Hls %] HΦ".
  iNamed "Hls".

  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hinner]".

  wp_pures.
  wp_apply (wp_forBreak
    (fun b => is_lockShard_inner mptr shardlock gh covered P ∗ lock.locked #shardlock ∗ if b then emp else P addr ∗ locked gh addr)%I
    with "[] [$Hlocked $Hinner]").

  {
    iIntros (Φloop) "!> (Hinner&Hlocked&_) HΦloop".
    iDestruct "Hinner" as (m gm) "(Hmptr & Hghctx & Haddrs & Hcovered)".
    wp_pures.
    wp_apply wp_ref_of_zero; first by auto.
    iIntros (state) "Hstate".
    wp_loadField.
    wp_apply (wp_MapGet with "[$Hmptr]"); auto.
    iIntros (lockStatePtr ok) "[% Hmptr]".

    wp_pures.
    iEval (rewrite struct_mapsto_eq) in "Hstate".
    iDestruct "Hstate" as "[[Hstate _] _]". rewrite /=.
    rewrite loc_add_0.

    destruct ok; wp_if.
    - wp_pures.
      wp_apply (wp_store with "Hstate"); iIntros "Hstate".

      wp_apply wp_ref_of_zero; first by auto.
      iIntros (acquired) "Hacquired".

      wp_untyped_load.
      apply map_get_true in H0.
      iDestruct (big_sepM2_lookup_2_some with "Haddrs") as (gheld) "%"; eauto.
      iDestruct (big_sepM2_insert_acc with "Haddrs") as "[Haddr Haddrs]"; eauto.
      iNamed "Haddr".
      wp_loadField.
      destruct gheld; wp_pures.
      + wp_untyped_load.
        wp_loadField.
        wp_untyped_load.
        wp_storeField.
        wp_pures.

        iSpecialize ("Haddrs" $! true lockStatePtr).
        rewrite insert_id; eauto.
        rewrite insert_id; eauto.

        wp_untyped_load.
        wp_loadField.
        wp_apply (lock.wp_condWait with "[-HΦloop Hstate Hacquired]").
        {
          iFrame "Hlock Hcond Hlocked".
          iExists _, _.
          iFrame.
          iApply "Haddrs".
          iExists _, _.
          iFrame "∗ Hcond".
          done.
        }

        iIntros "(Hlocked & Hinner)".
        wp_loadField.

        iDestruct "Hinner" as (m2 gm2) "(Hmptr & Hghctx & Haddrs & Hcovered)".
        wp_apply (wp_MapGet with "[$Hmptr]"). iIntros (lockStatePtr2 ok) "[% Hmptr]".
        destruct ok.
        * wp_pures.

          apply map_get_true in H2.
          iDestruct (big_sepM2_lookup_2_some with "Haddrs") as (gheld) "%"; eauto.
          iDestruct (big_sepM2_lookup_acc with "Haddrs") as "[Haddr Haddrs]"; eauto.
          iDestruct "Haddr" as (cond2 nwaiters2) "(? & ? & ? & Hcond2 & % & Hwaiters2)".

          wp_loadField.
          wp_storeField.

          iEval (rewrite struct_mapsto_eq) in "Hacquired".
          iDestruct "Hacquired" as "[[Hacquired _] _]"; rewrite loc_add_0.
          wp_untyped_load.

          wp_pures.
          iApply "HΦloop".
          iFrame.
          iExists _, _. iFrame.
          iApply "Haddrs".
          iExists _, _. iFrame. done.

        * iEval (rewrite struct_mapsto_eq) in "Hacquired".
          iDestruct "Hacquired" as "[[Hacquired _] _]"; rewrite loc_add_0.
          wp_untyped_load.
          wp_pures.
          iApply "HΦloop".
          iFrame.
          iExists _, _. iFrame.

      + wp_untyped_load.
        wp_storeField.
        wp_pures.

        iDestruct "Hwaiters" as "[% | [_ [Haddr Hp]]]"; try congruence.
        iMod (gen_heap_update _ _ _ true with "Hghctx Haddr") as "[Hghctx Haddr]".

        iEval (rewrite struct_mapsto_eq) in "Hacquired".
        iDestruct "Hacquired" as "[[Hacquired _] _]"; rewrite loc_add_0.
        wp_pures.
        wp_untyped_store.
        wp_untyped_load.

        wp_pures.
        iApply "HΦloop".
        iFrame "Hlocked Hp Haddr".
        iExists _, _. iFrame.

        erewrite <- (insert_id m) at 1; eauto.
        iApply "Haddrs".
        iExists _, _. iFrame "∗ Hcond".
        iSplit; try done.
        iLeft; done.

    - wp_pures.
      wp_loadField.
      wp_apply lock.wp_newCond; [done|].
      iIntros (c) "#Hcond".
      wp_apply (wp_allocStruct); first by val_ty.
      iIntros (lst) "Hlst".
      wp_untyped_store.
      wp_untyped_load.
      wp_loadField.
      wp_apply (wp_MapInsert with "[$Hmptr]"); first by reflexivity.
      iIntros "Hmptr".

      wp_apply wp_ref_of_zero; first by auto.
      iIntros (acquired) "Hacquired".

      iDestruct (struct_fields_split with "Hlst") as "(?&?&?&_)".

      wp_pures.
      wp_untyped_load.
      wp_loadField.
      wp_pures.
      wp_untyped_load.
      wp_storeField.

      apply map_get_false in H0.
      iDestruct (big_sepM2_lookup_2_none with "Haddrs") as %Hgaddr; intuition eauto.

      iMod (gen_heap_alloc _ addr true with "Hghctx") as "(Hghctx & Haddrlocked)"; [auto|].  

      iEval (rewrite struct_mapsto_eq) in "Hacquired".
      iDestruct "Hacquired" as "[[Hacquired _] _]"; rewrite loc_add_0.
      wp_untyped_store.
      wp_untyped_load.

      wp_pures.
      iApply "HΦloop".
      iFrame.

      iDestruct (big_sepS_delete with "Hcovered") as "[Hp Hcovered]"; eauto.
      iSplitR "Hp".
      2: { iApply "Hp"; done. }

      iExists _, _. iFrame.

      iSplitR "Hcovered".
      {
        iApply (big_sepM2_insert); [auto | auto | ].
        iFrame.
        iExists  _, _.
        iFrame "∗ Hcond".
        iFrame.
        iSplitL; [ iPureIntro; congruence | ].
        iLeft; done.
      }

      replace (covered) with ({[ addr ]} ∪ (covered ∖ {[ addr ]})) at 3.
      2: {
        rewrite -union_difference_L; auto.
        set_solver.
      }

      iApply (big_sepS_insert).
      { set_solver. }

      iSplitR. { rewrite lookup_insert; iIntros (Hx). congruence. }

      iApply big_sepS_mono; iFrame.
      iIntros (x Hx) "H".
      destruct (decide (addr = x)); subst.
      { set_solver. }

      rewrite lookup_insert_ne //.
  }

  iIntros "(Hinner & Hlocked & Hp & Haddrlocked)".
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hinner]").
  {
    iSplitR. { iApply "Hlock". }
    iFrame.
  }

  iApply "HΦ".
  iFrame.
Qed.

Theorem wp_lockShard__release ls (addr : u64) (P : u64 -> iProp Σ) covered gh :
  {{{ is_lockShard ls gh covered P ∗ P addr ∗ locked gh addr }}}
    lockShard__release #ls #addr
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(Hls & Hp & Haddrlocked) HΦ".
  iDestruct "Hls" as (shardlock mptr) "(#Hls_mu&#Hls_state&#Hlock)".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hinner]".
  iDestruct "Hinner" as (m gm) "(Hmptr & Hghctx & Haddrs & Hcovered)".

  wp_loadField.
  wp_apply (wp_MapGet with "Hmptr").
  iIntros (lockStatePtr ok) "[% Hmptr]".

  wp_pures.

  rewrite /locked.
  iDestruct (gen_heap_valid with "Hghctx Haddrlocked") as %Hsome.
  iDestruct (big_sepM2_lookup_1_some with "Haddrs") as %Hsome2; eauto.
  destruct Hsome2.

  iDestruct (big_sepM2_delete with "Haddrs") as "[Haddr Haddrs]"; eauto.

  iNamed "Haddr".

  rewrite /map_get H0 /= in H.
  inversion H; clear H; subst.

  wp_storeField.
  wp_loadField.
  wp_pures.

  destruct (bool_decide (int.val 0 < int.val nwaiters))%Z.

  {
    wp_pures.
    wp_loadField.
    wp_apply (lock.wp_condSignal with "[$Hcond]").

    iMod (gen_heap_update _ _ _ false with "Hghctx Haddrlocked") as "[Hghctx Haddrlocked]".

    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "Hlock Hlocked".
      iExists _, _.
      iFrame.

      iDestruct (big_sepM2_insert_2 _ _ _ addr false lockStatePtr
        with "[-Haddrs] Haddrs") as "Haddrs".
      {
        rewrite /setField_f /=.
        iExists _, _.
        iFrame "∗ Hcond".
        iSplitR; auto.
        iRight.
        iFrame. done.
      }

      rewrite insert_delete.
      rewrite insert_delete.
      rewrite (insert_id m); eauto.
    }

    iApply "HΦ".
    auto.
  }

  {
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapDelete with "[$Hmptr]").
    iIntros "Hmptr".

    iMod (gen_heap_delete with "[$Haddrlocked $Hghctx]") as "Hghctx".

    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "∗ Hlock".
      iExists _, (delete addr gm).
      iFrame.

      iDestruct (big_sepS_delete with "Hcovered") as "[Hcaddr Hcovered]"; eauto.
      replace (covered) with ({[ addr ]} ∪ (covered ∖ {[ addr ]})) at 3.
      2: {
        rewrite -union_difference_L; auto.
        set_solver.
      }

      iApply (big_sepS_insert).
      { set_solver. }

      iSplitL "Hp". { iFrame. done. }

      iApply big_sepS_mono; iFrame.
      iIntros (x Hx) "H".
      destruct (decide (addr = x)); subst.
      { set_solver. }

      rewrite lookup_delete_ne //.
    }

    iApply "HΦ".
    auto.
  }
Qed.


Definition NSHARD : Z := 43.

Definition covered_by_shard (shardnum : Z) (covered: gset u64) : gset u64 :=
  filter (λ x, Z.modulo (int.val x) NSHARD = shardnum) covered.

Lemma covered_by_shard_mod addr covered :
  addr ∈ covered ->
  addr ∈ covered_by_shard (int.nat (word.modu addr NSHARD)) covered.
Proof.
  intros.
  rewrite /covered_by_shard.
  apply elem_of_filter; intuition.
  rewrite /NSHARD.
  word_cleanup.
  rewrite Z2Nat.id.
  - word.
  - apply Z_mod_pos. lia.
Qed.

Definition is_lockMap (l: loc) (ghs: list (gen_heapG u64 bool Σ)) (covered: gset u64) (P: u64 -> iProp Σ) : iProp Σ :=
  ∃ (shards: list loc) (shardslice: Slice.t),
    "#Href" ∷ readonly (l ↦[LockMap.S :: "shards"] (slice_val shardslice)) ∗
    "#Hslice" ∷ readonly (is_slice_small shardslice (struct.ptrT lockShard.S) 1 shards) ∗
    "%Hlen" ∷ ⌜ length shards = Z.to_nat NSHARD ⌝ ∗
    "#Hshards" ∷ [∗ list] shardnum ↦ shardloc; shardgh ∈ shards; ghs,
      is_lockShard shardloc shardgh (covered_by_shard shardnum covered) P.

Definition Locked (ghs : list (gen_heapG u64 bool Σ)) (addr : u64) : iProp Σ :=
  ∃ gh,
    ⌜ ghs !! (Z.to_nat (Z.modulo (int.val addr) NSHARD)) = Some gh ⌝ ∗
    locked gh addr.


(* XXX why is this needed here? *)
Opaque load_ty.
Opaque lockShard.S.

Theorem wp_MkLockMap covered (P : u64 -> iProp Σ) :
  {{{ [∗ set] a ∈ covered, P a }}}
    MkLockMap #()
  {{{ l ghs, RET #l; is_lockMap l ghs covered P }}}.
Proof.
  iIntros (Φ) "Hcovered HΦ".
  wp_call.
  wp_apply wp_ref_of_zero; eauto.
  iIntros (shards) "Hvar".
  rewrite zero_slice_val.
  wp_pures.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (iv) "Hi".
  wp_pures.
  wp_apply (wp_forUpto (λ i,
                          ∃ s shardlocs ghs,
                            "Hvar" ∷ shards ↦[slice.T (refT (struct.t lockShard.S))] (slice_val s) ∗
                            "Hslice" ∷ is_slice s (struct.ptrT lockShard.S) 1 shardlocs ∗
                            "%Hlen" ∷ ⌜ length shardlocs = int.nat i ⌝ ∗
                            "Hshards" ∷ [∗ list] shardnum ↦ shardloc; shardgh ∈ shardlocs; ghs,
                              is_lockShard shardloc shardgh (covered_by_shard shardnum covered) P)%I
            with "[] [$Hi Hvar]").
  { word. }
  { clear Φ.
    iIntros (i).
    iIntros "!>" (Φ) "(HI & Hi & %Hibound) HΦ".
    iNamed "HI".
    wp_pures.
    wp_apply wp_mkLockShard.
    { admit. }
    iIntros (ls gh) "Hls".
    wp_load.
    wp_apply (wp_SliceAppend (V:=loc) with "Hslice").
    iIntros (s') "Hslice".
    wp_store.
    iApply "HΦ".
    iFrame "Hi".
    iExists _, _, _.
    iFrame "Hvar Hslice".
    iSplitR.
    { rewrite app_length Hlen /=. word. }
    iApply (big_sepL2_app with "Hshards").
    iApply big_sepL2_singleton.
    iApply "Hls".
  }
  {
    iExists _, nil, nil.
    iFrame "Hvar".
    iSplit.
    { iApply is_slice_zero. }
    iSplit.
    { done. }
    iApply big_sepL2_nil. done.
  }
  iIntros "[HI Hi]".
  iNamed "HI".
  wp_pures.
  wp_load.
  wp_apply wp_allocStruct; first by val_ty.
  iIntros (lm) "Hlm".
  iDestruct (struct_fields_split with "Hlm") as "(Hlm&_)".
  iMod (readonly_alloc_1 with "Hlm") as "Hlm".
  iDestruct (is_slice_to_small with "Hslice") as "Hslice".
  iMod (readonly_alloc_1 with "Hslice") as "Hslice".
  wp_pures.
  iApply "HΦ".
  iExists _, _.
  iFrame "Hlm".
  iFrame "Hslice".
  iSplitR.
  { iPureIntro. rewrite Hlen. reflexivity. }
  iApply "Hshards".
Admitted.

Theorem wp_LockMap__Acquire l ghs covered (addr : u64) (P : u64 -> iProp Σ) :
  {{{ is_lockMap l ghs covered P ∗
      ⌜addr ∈ covered⌝ }}}
    LockMap__Acquire #l #addr
  {{{ RET #(); P addr ∗ Locked ghs addr }}}.
Proof.
  iIntros (Φ) "[Hlm %] HΦ".
  iNamed "Hlm".

  wp_call.
  wp_loadField.

  iMod (readonly_load with "Hslice") as (q) "Hslice_copy".
  { solve_ndisj. }

  iDestruct (big_sepL2_length with "Hshards") as "%Hlen2".

  edestruct (list_lookup_lt _ shards (int.nat (word.modu addr NSHARD))).
  { rewrite Hlen /NSHARD. word_cleanup.
    apply Z2Nat.inj_lt; word_cleanup.
    { apply Z_mod_pos. lia. }
    { apply Z_mod_lt. lia. }
  }

  edestruct (list_lookup_lt _ ghs (int.nat (word.modu addr NSHARD))).
  { rewrite -Hlen2 Hlen /NSHARD. word_cleanup.
    apply Z2Nat.inj_lt; word_cleanup.
    { apply Z_mod_pos. lia. }
    { apply Z_mod_lt. lia. }
  }

  wp_apply (wp_SliceGet _ _ _ _ _ shards with "[$Hslice_copy]").
  { eauto. }
  iIntros "Hslice_copy".

  iDestruct (big_sepL2_lookup with "Hshards") as "Hshard"; eauto.
  wp_apply (wp_lockShard__acquire with "[$Hshard]").
  { iPureIntro. apply covered_by_shard_mod. auto. }

  iIntros "[HP Hlocked]".
  iApply "HΦ".
  iFrame "HP".

  iExists _. iFrame.
  iPureIntro.
  rewrite -H1 /NSHARD. f_equal.
  word.
Qed.

Theorem wp_LockMap__Release l ghs covered (addr : u64) (P : u64 -> iProp Σ) :
  {{{ is_lockMap l ghs covered P ∗ P addr ∗ Locked ghs addr }}}
    LockMap__Release #l #addr
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[Hlm [HP Hlocked]] HΦ".
  iNamed "Hlm".

  wp_call.
  wp_loadField.

  iMod (readonly_load with "Hslice") as (q) "Hslice_copy".
  { solve_ndisj. }

  edestruct (list_lookup_lt _ shards (int.nat (word.modu addr NSHARD))).
  { rewrite Hlen /NSHARD. word_cleanup.
    apply Z2Nat.inj_lt; word_cleanup.
    { apply Z_mod_pos. lia. }
    { apply Z_mod_lt. lia. }
  }

  iDestruct "Hlocked" as (gh) "[% Hlocked]".

  wp_apply (wp_SliceGet _ _ _ _ _ shards with "[$Hslice_copy]").
  { eauto. }
  iIntros "Hslice_copy".

  iDestruct (big_sepL2_lookup with "Hshards") as "Hshard"; eauto.
  { erewrite <- H0. rewrite /NSHARD. f_equal. word. }

  wp_apply (wp_lockShard__release with "[$Hshard $HP $Hlocked]").
  iApply "HΦ". done.
Qed.

End heap.
