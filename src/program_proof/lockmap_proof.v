From Perennial.program_proof Require Import disk_prelude.
From Perennial.base_logic Require Import lib.ghost_map.

From Goose.github_com.mit_pdos.go_journal Require Import lockmap.
From Perennial.goose_lang.lib Require Import wp_store.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

From Perennial.Helpers Require Import NamedProps range_set.

Local Transparent load_ty store_ty.

Ltac word := try lazymatch goal with
                 | |- envs_entails _ _ => iPureIntro
                 end; Integers.word.

Ltac len := autorewrite with len; try word.

Class lockmapG Σ : Set := lockmap_inG :> ghost_mapG Σ u64 bool.
Definition lockmapΣ := ghost_mapΣ u64 bool.
#[global]
Instance subG_lockmapΣ Σ : subG lockmapΣ Σ → lockmapG Σ.
Proof. solve_inG. Qed.

Section heap.
Context `{!heapGS Σ}.
Context `{!lockmapG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "lockShard".
Definition lockshardN : namespace := nroot .@ "lockShardMem".

Definition locked (hm : gname) (addr : u64) : iProp Σ :=
  ( addr ↪[hm] true )%I.

Definition lockShard_addr gh (shardlock : loc) (addr : u64) (gheld : bool)
           (lockStatePtr : loc) (covered : gset u64) (P : u64 -> iProp Σ) :=
  ( ∃ (cond : loc) (nwaiters : u64),
      "held" ∷ lockStatePtr ↦[lockState :: "held"] #gheld ∗
      "cond" ∷ lockStatePtr ↦[lockState :: "cond"] #cond ∗
      "waiters" ∷ lockStatePtr ↦[lockState :: "waiters"] #nwaiters ∗
      "#Hcond" ∷ lock.is_cond cond #shardlock ∗
      "%Hcovered" ∷ ⌜ addr ∈ covered ⌝ ∗
      "Hwaiters" ∷ ( ⌜ gheld = true ⌝ ∨
        ( ⌜ gheld = false ⌝ ∗ addr ↪[gh] false ∗ P addr ) )
  )%I.

Definition is_lockShard_inner (mptr : loc) (shardlock : loc)
           (ghostHeap : gname) (covered : gset u64) (P : u64 -> iProp Σ) : iProp Σ :=
  ( ∃ (m: gmap u64 loc) ghostMap,
      own_map mptr (DfracOwn 1) m ∗
      ghost_map_auth ghostHeap 1 ghostMap ∗
      ( [∗ map] addr ↦ gheld; lockStatePtrV ∈ ghostMap; m,
          lockShard_addr ghostHeap shardlock addr gheld lockStatePtrV covered P ) ∗
      ( [∗ set] addr ∈ covered,
          ⌜m !! addr = None⌝ → P addr )
  )%I.

Definition is_lockShard (ls : loc) (ghostHeap : gname) (covered : gset u64) (P : u64 -> iProp Σ) : iProp Σ :=
  ( ∃ (shardlock mptr : loc),
      "#Hls_mu" ∷ readonly (ls ↦[lockShard :: "mu"] #shardlock) ∗
      "#Hls_state" ∷ readonly (ls ↦[lockShard :: "state"] #mptr) ∗
      "#Hlock" ∷ is_lock lockN #shardlock (is_lockShard_inner mptr shardlock ghostHeap covered P)
  )%I.

Global Instance is_lockShard_persistent ls gh (P : u64 -> iProp Σ) c : Persistent (is_lockShard ls gh c P).
Proof. apply _. Qed.

Theorem wp_mkLockShard covered (P : u64 -> iProp Σ) :
  {{{ [∗ set] a ∈ covered, P a }}}
    mkLockShard #()
  {{{ ls gh, RET #ls; is_lockShard ls gh covered P }}}.
Proof.
  iIntros (Φ) "Hinit HΦ".
  rewrite /mkLockShard.
  wp_pures.

  wp_apply (wp_NewMap _ loc).
  iIntros (mref) "Hmap".
  wp_pures.

  wp_apply wp_new_free_lock; auto.

  iIntros (shardlock) "Hfreelock".

  wp_pures.
  iDestruct (is_free_lock_ty with "Hfreelock") as "%".
  wp_apply wp_allocStruct; first val_ty.
  iIntros (ls) "Hls".

  iMod (ghost_map_alloc (∅: gmap u64 bool)) as (hG) "[Hheapctx _]".
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
    iEval (rewrite struct_pointsto_eq) in "Hstate".
    iDestruct "Hstate" as "[[Hstate _] _]". rewrite /=.
    rewrite loc_add_0.

    destruct ok; wp_if.
    - wp_pures.
      wp_apply (wp_store with "Hstate"); iIntros "Hstate".

      wp_apply wp_ref_of_zero; first by auto.
      iIntros (acquired) "Hacquired".

      wp_untyped_load.
      apply map_get_true in H0.
      iDestruct (big_sepM2_lookup_r_some with "Haddrs") as (gheld) "%"; eauto.
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
          iDestruct (big_sepM2_lookup_r_some with "Haddrs") as (gheld) "%"; eauto.
          iDestruct (big_sepM2_lookup_acc with "Haddrs") as "[Haddr Haddrs]"; eauto.
          iDestruct "Haddr" as (cond2 nwaiters2) "(? & ? & ? & Hcond2 & % & Hwaiters2)".

          wp_loadField.
          wp_storeField.

          iEval (rewrite struct_pointsto_eq) in "Hacquired".
          iDestruct "Hacquired" as "[[Hacquired _] _]"; rewrite loc_add_0.
          wp_untyped_load.

          wp_pures.
          iApply "HΦloop".
          iFrame.
          iApply "Haddrs".
          iExists _, _. iFrame. done.

        * iEval (rewrite struct_pointsto_eq) in "Hacquired".
          iDestruct "Hacquired" as "[[Hacquired _] _]"; rewrite loc_add_0.
          wp_untyped_load.
          wp_pures.
          iApply "HΦloop".
          by iFrame.

      + wp_untyped_load.
        wp_storeField.
        wp_pures.

        iDestruct "Hwaiters" as "[% | [_ [Haddr Hp]]]"; try congruence.
        iMod (ghost_map_update true with "Hghctx Haddr") as "[Hghctx Haddr]".

        iEval (rewrite struct_pointsto_eq) in "Hacquired".
        iDestruct "Hacquired" as "[[Hacquired _] _]"; rewrite loc_add_0.
        wp_pures.
        wp_untyped_store.
        wp_untyped_load.

        wp_pures.
        iApply "HΦloop".
        iFrame "Hlocked Hp Haddr".
        iExists _, _. iFrame.

        erewrite <- (insert_id m) at 1; eauto.
        iApply "Haddrs". iModIntro.
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
      iDestruct (big_sepM2_lookup_r_none with "Haddrs") as %Hgaddr; intuition eauto.

      iMod (ghost_map_insert addr true with "Hghctx") as "(Hghctx & Haddrlocked)"; [auto|].  

      iEval (rewrite struct_pointsto_eq) in "Hacquired".
      iDestruct "Hacquired" as "[[Hacquired _] _]"; rewrite loc_add_0.
      wp_untyped_store.
      wp_untyped_load.

      wp_pures.
      iApply "HΦloop".
      iFrame.

      iDestruct (big_sepS_delete with "Hcovered") as "[Hp Hcovered]"; eauto.
      iSplitR "Hp".
      2: { iApply "Hp"; done. }

      iSplitR "Hcovered".
      {
        iApply (big_sepM2_insert); [auto | auto | ].
        iFrame "∗ Hcond".
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

      iModIntro.
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

  wp_pures. iApply "HΦ".
  by iFrame.
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
  iDestruct (ghost_map_lookup with "Hghctx Haddrlocked") as %Hsome.
  iDestruct (big_sepM2_lookup_l_some with "Haddrs") as %Hsome2; eauto.
  destruct Hsome2.

  iDestruct (big_sepM2_delete with "Haddrs") as "[Haddr Haddrs]"; eauto.

  iNamed "Haddr".

  rewrite /map_get H0 /= in H.
  inversion H; clear H; subst.

  wp_storeField.
  wp_loadField.
  wp_pures.

  destruct (bool_decide (uint.Z 0 < uint.Z nwaiters))%Z.

  {
    wp_pures.
    wp_loadField.
    wp_apply (lock.wp_condSignal with "[$Hcond]").

    iMod (ghost_map_update false with "Hghctx Haddrlocked") as "[Hghctx Haddrlocked]".

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
        by iFrame.
      }

      rewrite insert_delete_insert.
      rewrite insert_delete_insert.
      rewrite (insert_id m); eauto.
    }

    wp_pures. iApply "HΦ".
    auto.
  }

  {
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapDelete with "[$Hmptr]").
    iIntros "Hmptr".

    iMod (ghost_map_delete with "Hghctx Haddrlocked") as "Hghctx".

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

    wp_pures. iApply "HΦ".
    auto.
  }
Qed.


Definition NSHARD_def : Z := Eval vm_compute in (match NSHARD with #(LitInt z) => uint.Z z | _ => 0 end).
Definition NSHARD_aux : seal (@NSHARD_def). Proof. by eexists. Qed.
Definition NSHARD := NSHARD_aux.(unseal).
Definition NSHARD_eq : @NSHARD = @NSHARD_def := NSHARD_aux.(seal_eq).

Ltac unseal_nshard := rewrite NSHARD_eq /NSHARD_def.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Definition covered_by_shard (shardnum : Z) (covered: gset u64) : gset u64 :=
  filter (λ x, Z.modulo (uint.Z x) NSHARD = shardnum) covered.

Lemma covered_by_shard_mod addr covered :
  addr ∈ covered <->
  addr ∈ covered_by_shard (uint.nat (word.modu addr NSHARD)) covered.
Proof.
  intros.
  rewrite /covered_by_shard.
  split; intros.
  + apply elem_of_filter; intuition.
    unseal_nshard.
    word.
  + apply elem_of_filter in H; intuition.
Qed.

Lemma covered_by_shard_empty x :
  covered_by_shard x ∅ = ∅.
Proof. done. Qed.

Lemma covered_by_shard_insert x X :
  covered_by_shard (uint.Z (word.modu x (W64 NSHARD))) ({[x]} ∪ X) =
  {[x]} ∪ covered_by_shard (uint.Z (word.modu x (W64 NSHARD))) X.
Proof.
  rewrite /covered_by_shard filter_union_L filter_singleton_L //.
  unseal_nshard.
  word.
Qed.

Lemma covered_by_shard_insert_ne (x x' : u64) X :
  (uint.Z x `mod` NSHARD)%Z ≠ uint.Z x' ->
  covered_by_shard (uint.Z x') ({[x]} ∪ X) =
    covered_by_shard (uint.Z x') X.
Proof.
  intros.
  rewrite /covered_by_shard filter_union_L filter_singleton_not_L.
  { set_solver. }
  auto.
Qed.

Lemma rangeSet_lookup_mod (x : u64) (n : Z) :
  (0 < n < 2^64)%Z ->
  word.modu x (W64 n) ∈ rangeSet 0 n.
Proof.
  intros.
  apply rangeSet_lookup; try word.
  word_cleanup.
  word.
Qed.

Lemma covered_by_shard_split (P : u64 -> iProp Σ) covered :
  ( [∗ set] a ∈ covered, P a ) -∗
  [∗ set] shardnum ∈ rangeSet 0 NSHARD,
    [∗ set] a ∈ covered_by_shard (uint.Z shardnum) covered, P a.
Proof.
  induction covered using set_ind_L.
  - setoid_rewrite big_sepS_empty.
    auto.
  - iIntros "H".
    iDestruct (big_sepS_insert with "H") as "[HP H]"; try assumption.
    iDestruct (IHcovered with "H") as "H".
    replace (rangeSet 0 NSHARD) with ({[ word.modu x NSHARD ]} ∪
                                      rangeSet 0 NSHARD ∖ {[ word.modu x NSHARD ]}).
    2: {
      rewrite -union_difference_L; auto.
      assert (0 < NSHARD < 2^64)%Z as Hbound by (unseal_nshard; done).
      pose proof (rangeSet_lookup_mod x NSHARD Hbound).
      set_solver.
    }

    iDestruct (big_sepS_insert with "H") as "[Hthis Hother]"; first by set_solver.
    iApply big_sepS_insert; first by set_solver.

    iSplitL "HP Hthis".
    + rewrite covered_by_shard_insert.
      iApply big_sepS_insert.
      { intro Hx. apply H. apply covered_by_shard_mod.
        rewrite Z2Nat.id; eauto.
        revert Hx. unseal_nshard. word. }
      iFrame.
    + iApply (big_sepS_mono with "Hother").
      iIntros (x' Hx') "H".
      rewrite covered_by_shard_insert_ne.
      { iFrame. }

      intro Heq.
      apply elem_of_difference in Hx'.
      destruct Hx'.
      apply H1.
      apply elem_of_singleton.
      revert Heq.
      unseal_nshard.
      word_cleanup.

      intros.
      apply int_Z_inj; first by apply _.
      word.
Qed.

Definition is_lockMap (l: loc) (ghs: list gname) (covered: gset u64) (P: u64 -> iProp Σ) : iProp Σ :=
  ∃ (shards: list loc) (shardslice: Slice.t),
    "#Href" ∷ readonly (l ↦[LockMap :: "shards"] (slice_val shardslice)) ∗
    "#Hslice" ∷ readonly (own_slice_small shardslice ptrT (DfracOwn 1) shards) ∗
    "%Hlen" ∷ ⌜ length shards = Z.to_nat NSHARD ⌝ ∗
    "#Hshards" ∷ [∗ list] shardnum ↦ shardloc; shardgh ∈ shards; ghs,
      is_lockShard shardloc shardgh (covered_by_shard shardnum covered) P.

Definition Locked (ghs : list gname) (addr : u64) : iProp Σ :=
  ∃ gh,
    ⌜ ghs !! (Z.to_nat (Z.modulo (uint.Z addr) NSHARD)) = Some gh ⌝ ∗
    locked gh addr.


(* XXX why is this needed here? *)
Opaque load_ty.
Opaque lockShard.

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
  wp_apply (wp_forUpto (λ (i : u64),
                          ∃ s shardlocs ghs,
                            "Hvar" ∷ shards ↦[slice.T ptrT] (slice_val s) ∗
                            "Hslice" ∷ own_slice s ptrT (DfracOwn 1) shardlocs ∗
                            "%Hlen" ∷ ⌜ length shardlocs = uint.nat i ⌝ ∗
                            "Hpp" ∷ ( [∗ set] shardnum ∈ rangeSet (uint.Z i) (NSHARD-uint.Z i),
                              [∗ set] a ∈ covered_by_shard (uint.Z shardnum) covered, P a ) ∗
                            "Hshards" ∷ [∗ list] shardnum ↦ shardloc; shardgh ∈ shardlocs; ghs,
                              is_lockShard shardloc shardgh (covered_by_shard shardnum covered) P)%I
            with "[] [$Hi Hvar Hcovered]").
  { word. }
  { clear Φ.
    iIntros (i).
    iIntros "!>" (Φ) "(HI & Hi & %Hibound) HΦ".
    iNamed "HI".
    wp_pures.
    rewrite rangeSet_first.
    2: { unseal_nshard. word. }
    iDestruct (big_sepS_insert with "Hpp") as "[Hp Hpp]".
    { unseal_nshard. intro Hx.
      apply rangeSet_lookup in Hx; try word.
      intuition. revert H. word. }
    wp_apply (wp_mkLockShard with "Hp").
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
    iSplitL "Hpp".
    { replace (uint.Z (word.add i 1))%Z with (uint.Z i + 1)%Z by word.
      replace (NSHARD - (uint.Z i + 1))%Z with (NSHARD - uint.Z i - 1)%Z by word.
      by iFrame. }
    iApply (big_sepL2_app with "Hshards").
    iApply big_sepL2_singleton.
    rewrite Hlen.
    replace (Z.of_nat (uint.nat i + 0)) with (uint.Z (W64 (uint.Z i))) by word.
    by iFrame.
  }
  {
    iExists _, nil, nil.
    iFrame "Hvar".
    iSplitR.
    { iApply own_slice_zero. }
    iSplitR.
    { done. }
    iSplitL "Hcovered".
    { iDestruct (covered_by_shard_split with "Hcovered") as "Hsplit".
      change (uint.Z 0%Z) with 0%Z.
      replace (NSHARD - 0)%Z with NSHARD by word.
      iFrame. }
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
  iDestruct (own_slice_to_small with "Hslice") as "Hslice".
  iMod (readonly_alloc_1 with "Hslice") as "Hslice".
  wp_pures.
  iApply "HΦ".
  iExists _, _.
  iFrame "Hlm".
  iFrame "Hslice".
  iSplitR.
  { iPureIntro. rewrite Hlen. unseal_nshard. reflexivity. }
  iApply "Hshards".
Qed.

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

  iDestruct (big_sepL2_length with "Hshards") as "%Hlen2".

  list_elem shards (uint.nat (word.modu addr NSHARD)) as shard.
  { revert Hlen. unseal_nshard. word. }
  list_elem ghs (uint.nat (word.modu addr NSHARD)) as gh.
  { revert Hlen. unseal_nshard. word. }

  wp_apply (wp_SliceGet _ _ _ _ _ shards with "[$Hslice_copy]").
  { revert Hshard_lookup. unseal_nshard. eauto. }
  iIntros "Hslice_copy".

  iDestruct (big_sepL2_lookup with "Hshards") as "Hshard"; eauto.
  wp_apply (wp_lockShard__acquire with "[$Hshard]").
  { iPureIntro. rewrite -covered_by_shard_mod. auto. }

  iIntros "[HP Hlocked]".
  wp_pures. iModIntro. iApply "HΦ".
  iFrame "HP".

  iExists _. iFrame.
  iPureIntro.
  rewrite -Hgh_lookup. f_equal.
  unseal_nshard.
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

  list_elem shards (uint.nat (word.modu addr NSHARD)) as shard.
  { revert Hlen. unseal_nshard. word. }

  iDestruct "Hlocked" as (gh) "[% Hlocked]".

  wp_apply (wp_SliceGet _ _ _ _ _ shards with "[$Hslice_copy]").
  { revert Hshard_lookup. unseal_nshard. eauto. }
  iIntros "Hslice_copy".

  iDestruct (big_sepL2_lookup with "Hshards") as "Hshard"; eauto.
  { erewrite <- H. unseal_nshard. f_equal. word. }

  wp_apply (wp_lockShard__release with "[$Hshard $HP $Hlocked]").
  wp_pures. iApply "HΦ". eauto.
Qed.

End heap.
