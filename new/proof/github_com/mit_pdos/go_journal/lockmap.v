Require Import New.generatedproof.github_com.mit_pdos.go_journal.lockmap.
Require Import New.proof.proof_prelude.
Require Import New.proof.github_com.goose_lang.primitive.disk.
Require Import New.proof.sync.

From Perennial.base_logic Require Import lib.ghost_map.
From Perennial.Helpers Require Import range_set.

Ltac len := autorewrite with len; try word.

Class lockmapG Σ : Set := #[global] lockmap_inG :: ghost_mapG Σ u64 bool.
Definition lockmapΣ := ghost_mapΣ u64 bool.
#[global]
Instance subG_lockmapΣ Σ : subG lockmapΣ Σ → lockmapG Σ.
Proof. solve_inG. Qed.

Section heap.
Context `{!heapGS Σ} `{!goGlobalsGS Σ}.
Context `{!lockmapG Σ}.

#[global]
Program Instance : IsPkgInit lockmap := ltac2:(build_pkg_init ()).
Next Obligation.
  (* XXX why isn't this automatic? *)
  refine _.
Qed.

Implicit Types s : slice.t.

Definition locked (hm : gname) (addr : u64) : iProp Σ :=
  ( addr ↪[hm] true )%I.

Definition lockShard_addr gh (shardlock : interface.t) (addr : u64) (gheld : bool)
           (lockStatePtr : loc) (covered : gset u64) (P : u64 -> iProp Σ) :=
  ( ∃ (cond : loc) (nwaiters : u64),
      "held" ∷ lockStatePtr ↦s[lockmap.lockState :: "held"] gheld ∗
      "cond" ∷ lockStatePtr ↦s[lockmap.lockState :: "cond"] cond ∗
      "waiters" ∷ lockStatePtr ↦s[lockmap.lockState :: "waiters"] nwaiters ∗
      "#Hcond" ∷ is_Cond cond shardlock ∗
      "%Hcovered" ∷ ⌜ addr ∈ covered ⌝ ∗
      "Hwaiters" ∷ ( ⌜ gheld = true ⌝ ∨
        ( ⌜ gheld = false ⌝ ∗ addr ↪[gh] false ∗ P addr ) )
  )%I.

Definition is_lockShard_inner (mptr : loc) (shardlock : loc)
           (ghostHeap : gname) (covered : gset u64) (P : u64 -> iProp Σ) : iProp Σ :=
  ( ∃ (m: gmap u64 loc) ghostMap,
      "Hmptr" ∷ own_map mptr (DfracOwn 1) m ∗
      "Hghctx" ∷ ghost_map_auth ghostHeap 1 ghostMap ∗
      "Haddrs" ∷ ( [∗ map] addr ↦ gheld; lockStatePtrV ∈ ghostMap; m,
          lockShard_addr ghostHeap (interface.mk Mutex_type_id #shardlock) addr gheld lockStatePtrV covered P ) ∗
      "Hcovered" ∷ ( [∗ set] addr ∈ covered,
          ⌜m !! addr = None⌝ → P addr )
  )%I.

Definition is_lockShard (ls : loc) (ghostHeap : gname) (covered : gset u64) (P : u64 -> iProp Σ) : iProp Σ :=
  ( ∃ (shardlock mptr : loc),
      "#Hls_mu" ∷ ls ↦s[lockmap.lockShard :: "mu"]□ shardlock ∗
      "#Hls_state" ∷ ls ↦s[lockmap.lockShard :: "state"]□ mptr ∗
      "#Hlock" ∷ is_Mutex shardlock (is_lockShard_inner mptr shardlock ghostHeap covered P)
  )%I.

Global Instance is_lockShard_persistent ls gh (P : u64 -> iProp Σ) c : Persistent (is_lockShard ls gh c P).
Proof. apply _. Qed.

Theorem wp_mkLockShard covered (P : u64 -> iProp Σ) :
  {{{ is_pkg_init lockmap ∗
      [∗ set] a ∈ covered, P a }}}
    lockmap@"mkLockShard" #()
  {{{ ls gh, RET #ls; is_lockShard ls gh covered P }}}.
Proof.
  wp_start as "Hinit".
  wp_auto.
  wp_apply wp_map_make; first eauto. iIntros (mref) "Hmap".
  wp_auto.
  wp_alloc shardlock as "Hshardlock".
  wp_auto.
  wp_alloc ls as "Hls".

  iMod (ghost_map_alloc (∅: gmap u64 bool)) as (hG) "[Hheapctx _]".
  iAssert (is_lockShard_inner mref shardlock hG covered P) with "[Hinit Hmap Hheapctx]" as "Hinner".
  {
    iExists _, _.
    iFrame.

    iSplitR; eauto.

    iApply big_sepS_mono; last iFrame.
    iIntros; iFrame.
  }

  iMod (init_Mutex with "Hshardlock Hinner") as "Hlock".
  iPersist "Hls".

  wp_auto.
  wp_pures.

  iApply "HΦ".
  iExists _, _.
  iDestruct (struct_fields_split with "Hls") as "Hls'". iNamed "Hls'".
  iFrame "∗#".
Qed.

Theorem wp_lockShard__acquire ls gh covered (addr : u64) (P : u64 -> iProp Σ) :
  {{{ is_pkg_init lockmap ∗
      is_lockShard ls gh covered P ∗
      ⌜addr ∈ covered⌝ }}}
    ls@lockmap@"lockShard'ptr"@"acquire" #addr
  {{{ RET #(); P addr ∗ locked gh addr }}}.
Proof.
  wp_start as "[Hls %]".
  iNamed "Hls".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hinner]".

  wp_auto.
  wp_for.
  iNamed "Hinner".
  wp_apply (wp_map_get with "Hmptr"). iIntros "Hmptr".
  wp_auto.

  destruct (m !! addr) eqn:Hmaddr.
  - wp_auto.
    iDestruct (big_sepM2_lookup_r_some with "Haddrs") as (gheld) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Haddrs") as "[Haddr Haddrs]"; eauto.
    iNamed "Haddr".
    wp_auto.
    destruct gheld; wp_auto.
    + iSpecialize ("Haddrs" $! true l).
      rewrite insert_id; eauto.
      rewrite insert_id; eauto.

      iDestruct ("Haddrs" with "[held cond waiters]") as "Haddrs".
      {
        iFrame "∗#%".
        iLeft. done.
      }
      wp_apply (wp_Cond__Wait with "[$Hcond Hlocked Hmptr Hghctx Hcovered Haddrs]").
      {
        iDestruct (Mutex_is_Locker with "[] [$Hlock]") as "$".
        { iPkgInit. }
        iFrame.
      }
      iIntros "(Hlocked & Hinner)".
      wp_auto.
      iDestruct "Hinner" as (m2 gm2) "(Hmptr & Hghctx & Haddrs & Hcovered)".

      wp_apply (wp_map_get with "Hmptr"). iIntros "Hmptr".
      wp_auto.
      destruct (m2 !! addr) eqn:Hm2addr.
      * wp_auto.
        iDestruct (big_sepM2_lookup_r_some with "Haddrs") as (gheld) "%"; eauto.
        iDestruct (big_sepM2_lookup_acc with "Haddrs") as "[Haddr Haddrs]"; eauto.
        iNamedSuffix "Haddr" "2".
        wp_auto.
        wp_for_post.
        iDestruct ("Haddrs" with "[$held2 $cond2 $waiters2 $Hwaiters2 $Hcond2]") as "Haddrs".
        { done. }
        iFrame.

      * wp_auto.
        wp_for_post.
        iFrame.

    + wp_for_post.

      iDestruct "Hwaiters" as "[% | [_ [Haddr Hp]]]"; try congruence.
      iMod (ghost_map_update true with "Hghctx Haddr") as "[Hghctx Haddr]".

      iDestruct ("Haddrs" with "[held cond waiters]") as "Haddrs".
      {
        iFrame "∗#%".
        iLeft. done.
      }

      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hmptr $Hghctx $Hcovered Haddrs]").
      { erewrite <- (insert_id m) at 2; eauto. }
      iApply "HΦ". iFrame.

  - wp_auto.
    wp_apply (wp_NewCond) as "%c #Hcond".
    wp_alloc lst as "Hlst".
    wp_auto.
    wp_apply (wp_map_insert with "Hmptr"). iIntros "Hmptr".
    wp_auto.
    wp_for_post.

    iDestruct (big_sepM2_lookup_r_none with "Haddrs") as %Hgaddr; intuition eauto.
    iMod (ghost_map_insert addr true with "Hghctx") as "(Hghctx & Haddrlocked)"; [auto|].
    iDestruct (big_sepS_delete with "Hcovered") as "[Hp Hcovered]"; eauto.
    iDestruct ("Hp" with "[]") as "Hp"; first auto.
    iDestruct (big_sepM2_insert _ _ _ _ true lst with "[$Haddrs Hlst]") as "Haddrs"; [ eassumption | eassumption | | ].
    { iDestruct (struct_fields_split with "Hlst") as "Hlst". iNamedSuffix "Hlst" "x". iFrame "∗#%". iLeft; done. }

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hmptr $Hghctx $Haddrs Hcovered]").
    { replace (covered) with ({[ addr ]} ∪ (covered ∖ {[ addr ]})) at 3.
      2: { rewrite -union_difference_L; set_solver. }
      iApply big_sepS_insert.
      { set_solver. }
      iSplitR.
      { rewrite lookup_insert; iIntros "!>%Hne". done. }
      iApply big_sepS_mono; iFrame.
      iIntros (x Hx) "H".
      destruct (decide (addr = x)); subst.
      + set_solver.
      + rewrite lookup_insert_ne //.
    }

    iApply "HΦ". iFrame.
Qed.

Theorem wp_lockShard__release ls (addr : u64) (P : u64 -> iProp Σ) covered gh :
  {{{ is_pkg_init lockmap ∗
      is_lockShard ls gh covered P ∗ P addr ∗ locked gh addr }}}
    ls@lockmap@"lockShard'ptr"@"release" #addr
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(Hls & Hp & Haddrlocked)".
  iDestruct "Hls" as (shardlock mptr) "(#Hls_mu&#Hls_state&#Hlock)".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hinner]".
  iDestruct "Hinner" as (m gm) "(Hmptr & Hghctx & Haddrs & Hcovered)".
  wp_auto.
  wp_apply (wp_map_get with "Hmptr"). iIntros "Hmptr".

  rewrite /locked.
  iDestruct (ghost_map_lookup with "Hghctx Haddrlocked") as %Hsome.
  iDestruct (big_sepM2_lookup_l_some with "Haddrs") as %Hsome2; eauto.
  destruct Hsome2 as [x Hsome2]. rewrite Hsome2.

  iDestruct (big_sepM2_delete with "Haddrs") as "[Haddr Haddrs]"; eauto.
  iNamed "Haddr".

  wp_auto.
  wp_if_destruct.
  - wp_auto.
    wp_apply (wp_Cond__Signal with "[$Hcond]").

    iMod (ghost_map_update false with "Hghctx Haddrlocked") as "[Hghctx Haddrlocked]".
    iDestruct (big_sepM2_insert_2 _ _ _ addr with "[held cond waiters Haddrlocked Hp] Haddrs") as "Haddrs".
    { iFrame "∗#%". iRight. iFrame. done. }
    rewrite insert_delete_insert.
    rewrite insert_delete_insert.
    rewrite (insert_id m); eauto.

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hmptr $Hghctx $Haddrs $Hcovered]").
    iApply "HΦ". done.

  - wp_auto.
    wp_apply (wp_map_delete with "Hmptr"). iIntros "Hmptr".
    wp_auto.

    iMod (ghost_map_delete with "Hghctx Haddrlocked") as "Hghctx".
    iDestruct (big_sepS_delete with "Hcovered") as "[Hcaddr Hcovered]"; eauto.

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hmptr $Hghctx $Haddrs Hcovered Hp]").
    { replace (covered) with ({[ addr ]} ∪ (covered ∖ {[ addr ]})) at 3.
      2: { rewrite -union_difference_L; set_solver. }
      iApply big_sepS_insert; first set_solver.
      iSplitL "Hp".
      { iIntros "!>_". iFrame. }
      iApply big_sepS_mono; iFrame.
      iIntros (y Hy) "H".
      destruct (decide (addr = y)); subst.
      + set_solver.
      + rewrite lookup_delete_ne //.
    }

    iApply "HΦ". done.
Qed.


Definition NSHARD_def : Z := 65537.
Definition NSHARD_aux : seal (@NSHARD_def). Proof. by eexists. Qed.
Definition NSHARD := NSHARD_aux.(unseal).
Definition NSHARD_eq : @NSHARD = @NSHARD_def := NSHARD_aux.(seal_eq).

Ltac unseal_nshard := rewrite NSHARD_eq /NSHARD_def.

Lemma NSHARD_pos : (0 < uint.Z NSHARD)%Z.
Proof. unseal_nshard. word. Qed.

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
      intros. word.
Qed.

Definition is_lockMap (l: loc) (ghs: list gname) (covered: gset u64) (P: u64 -> iProp Σ) : iProp Σ :=
  ∃ (shards: list loc) (shardslice: slice.t),
    "#Href" ∷ l ↦s[lockmap.LockMap :: "shards"]□ shardslice ∗
    "#Hslice" ∷ own_slice shardslice DfracDiscarded shards ∗
    "%Hlen" ∷ ⌜ length shards = Z.to_nat NSHARD ⌝ ∗
    "#Hshards" ∷ [∗ list] shardnum ↦ shardloc; shardgh ∈ shards; ghs,
      is_lockShard shardloc shardgh (covered_by_shard shardnum covered) P.

Definition Locked (ghs : list gname) (addr : u64) : iProp Σ :=
  ∃ gh,
    ⌜ ghs !! (Z.to_nat (Z.modulo (uint.Z addr) NSHARD)) = Some gh ⌝ ∗
    locked gh addr.


Theorem wp_MkLockMap covered (P : u64 -> iProp Σ) :
  {{{ is_pkg_init lockmap ∗
      [∗ set] a ∈ covered, P a }}}
    lockmap@"MkLockMap" #()
  {{{ l ghs, RET #l; is_lockMap l ghs covered P }}}.
Proof.
  wp_start as "Hcovered".
  wp_auto.

  iAssert (∃ (i: w64) (s: slice.t) shardlocs ghs,
              "i" ∷ i_ptr ↦ i ∗
              "Hvar" ∷ shards_ptr ↦ s ∗
              "Hslice" ∷ own_slice s (DfracOwn 1) shardlocs ∗
              "Hslice_cap" ∷ own_slice_cap loc s ∗
              "%Hlen" ∷ ⌜ length shardlocs = uint.nat i ⌝ ∗
              "Hpp" ∷ ( [∗ set] shardnum ∈ rangeSet (uint.Z i) (NSHARD-uint.Z i),
                [∗ set] a ∈ covered_by_shard (uint.Z shardnum) covered, P a ) ∗
              "Hshards" ∷ ([∗ list] shardnum ↦ shardloc; shardgh ∈ shardlocs; ghs,
                is_lockShard shardloc shardgh (covered_by_shard shardnum covered) P) ∗
              "%Hrange" ∷ ⌜0 ≤ uint.Z i ≤ NSHARD⌝%Z)%I
    with "[$i Hcovered $shards]" as "Hloop".
  { iExists nil, nil.
    iDestruct own_slice_nil as "$".
    iDestruct own_slice_cap_none as "$".
    { done. }
    iDestruct (big_sepL2_nil with "[$]") as "$".
    iSplitR.
    { done. }
    iDestruct (covered_by_shard_split with "Hcovered") as "Hsplit".
    change (uint.Z 0%Z) with 0%Z.
    replace (NSHARD - 0)%Z with NSHARD by word.
    iFrame.
    unseal_nshard. word.
  }

  wp_for.
  iNamed "Hloop".
  wp_auto.
  wp_if_destruct.
  - wp_auto.
    rewrite rangeSet_first.
    2: { unseal_nshard. word. }
    iDestruct (big_sepS_insert with "Hpp") as "[Hp Hpp]".
    { unseal_nshard. intro Hx.
      apply rangeSet_lookup in Hx; try word. }
    wp_apply (wp_mkLockShard with "[$Hp]").
    iIntros (ls gh) "Hls".
    wp_auto.
    wp_apply wp_slice_literal.
    iIntros (sls) "Hsls".
    wp_auto.

    wp_apply (wp_slice_append with "[$Hslice_cap $Hslice $Hsls]").
    iIntros (s') "(Hslice & Hslice_cap & Hsls)".
    wp_auto.
    iDestruct (big_sepL2_app with "Hshards [Hls]") as "Hshards".
    { iApply big_sepL2_singleton.
      rewrite Hlen.
      replace (uint.Z (W64 (uint.Z i))) with (uint.Z i) by word.
      replace (Z.of_nat (uint.nat i + 0)) with (uint.Z i) by word.
      iFrame.
    }

    wp_for_post.
    iFrame "HΦ i Hslice_cap Hvar Hslice Hshards".
    iSplitR.
    { rewrite length_app Hlen /=. word. }
    replace (uint.Z (word.add i 1))%Z with (uint.Z i + 1)%Z by word.
    replace (NSHARD - (uint.Z i + 1))%Z with (NSHARD - uint.Z i - 1)%Z by word.
    iFrame.
    unseal_nshard. word.

  - (* XXX why do i get this [if decide ... then .. else ..] around my goal? *)
    replace (# true) with (into_val_bool.(to_val_def) true) by ( rewrite to_val_unseal; auto ).
    replace (# false) with (into_val_bool.(to_val_def) false) by ( rewrite to_val_unseal; auto ).
    simpl.

    wp_auto.
    wp_alloc lm as "Hlm".
    iDestruct (struct_fields_split with "Hlm") as "Hlm".
    iPersist "Hlm".
    iPersist "Hslice".
    wp_auto.
    iApply "HΦ".
    iFrame "∗#".

    iPureIntro.
    rewrite Hlen. revert Hrange. unseal_nshard. word.
Qed.

Theorem wp_LockMap__Acquire l ghs covered (addr : u64) (P : u64 -> iProp Σ) :
  {{{ is_pkg_init lockmap ∗
      is_lockMap l ghs covered P ∗
      ⌜addr ∈ covered⌝ }}}
    l@lockmap@"LockMap'ptr"@"Acquire" #addr
  {{{ RET #(); P addr ∗ Locked ghs addr }}}.
Proof.
  wp_start as "[Hlm %]".
  iNamed "Hlm".

  iDestruct (big_sepL2_length with "Hshards") as "%Hlen2".
  pose proof NSHARD_pos.
  list_elem shards (uint.nat (word.modu addr NSHARD)) as shard.
  { revert Hlen. unseal_nshard. word. }
  list_elem ghs (uint.nat (word.modu addr NSHARD)) as gh.
  { revert Hlen. unseal_nshard. word. }

  iDestruct (own_slice_len with "Hslice") as "%Hlen3".
  pose proof NSHARD_eq as Hunseal. unfold NSHARD_def in Hunseal.
  rewrite Hunseal in Hshard_lookup.
  rewrite Hunseal in Hgh_lookup.
  wp_auto.

  (* XXX is this the expected way to use the [pure_elem_ref] instance of PureWp? *)
  wp_pure; first word.

  (* XXX is this the expected way to use [wp_load_slice_elem]? *)
  wp_apply (wp_load_slice_elem with "[$Hslice]"); first eauto. iIntros "_".

  wp_auto.
  iDestruct (big_sepL2_lookup with "Hshards") as "Hshard"; eauto.
  wp_apply (wp_lockShard__acquire with "[$Hshard]").
  { iPureIntro. rewrite -Hunseal. rewrite -covered_by_shard_mod. eauto. }

  iIntros "[HP Hlocked]".
  wp_auto.
  iApply "HΦ". iFrame.
  iPureIntro.
  rewrite -Hgh_lookup. f_equal.
  unseal_nshard.
  word.
Qed.

Theorem wp_LockMap__Release l ghs covered (addr : u64) (P : u64 -> iProp Σ) :
  {{{ is_pkg_init lockmap ∗
      is_lockMap l ghs covered P ∗ P addr ∗ Locked ghs addr }}}
    l@lockmap@"LockMap'ptr"@"Release" #addr
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[Hlm [HP Hlocked]]".
  iNamed "Hlm".

  iDestruct (big_sepL2_length with "Hshards") as "%Hlen2".
  pose proof NSHARD_pos.
  list_elem shards (uint.nat (word.modu addr NSHARD)) as shard.
  { revert Hlen. unseal_nshard. word. }

  iDestruct (own_slice_len with "Hslice") as "%Hlen3".
  pose proof NSHARD_eq as Hunseal. unfold NSHARD_def in Hunseal.
  rewrite Hunseal in Hshard_lookup.
  wp_auto.

  (* XXX is this the expected way to use the [pure_elem_ref] instance of PureWp? *)
  wp_pure; first word.

  (* XXX is this the expected way to use [wp_load_slice_elem]? *)
  wp_apply (wp_load_slice_elem with "[$Hslice]"); first eauto. iIntros "_".

  wp_auto.
  iDestruct "Hlocked" as (gh) "[%Hgh_lookup Hlocked]".
  rewrite Hunseal in Hgh_lookup.
  iDestruct (big_sepL2_lookup _ _ _ _ _ gh with "Hshards") as "Hshard"; eauto.
  { rewrite -Hgh_lookup. f_equal. word. }
  wp_apply (wp_lockShard__release with "[$Hshard $HP $Hlocked]").
  wp_pures. iApply "HΦ". eauto.
Qed.

End heap.
