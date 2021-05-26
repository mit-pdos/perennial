From Perennial.program_proof Require Import disk_prelude.
From Perennial.base_logic Require Import lib.ghost_map.

From Goose.github_com.mit_pdos.go_journal Require Import lockmap.
From Perennial.goose_lang.lib Require Import wp_store.
From Perennial.goose_lang.lib Require crash_lock.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

From Perennial.Helpers Require Import NamedProps range_set.
From Perennial.goose_lang Require Import proofmode wpc_proofmode notation crash_borrow.

Local Transparent load_ty store_ty.
Opaque crash_borrow.

Ltac word := try lazymatch goal with
                 | |- envs_entails _ _ => iPureIntro
                 end; Integers.word.

Ltac len := autorewrite with len; try word.

Class lockmapG Σ := lockmap_inG :> ghost_mapG Σ u64 bool.
Definition lockmapΣ := ghost_mapΣ u64 bool.
Instance subG_lockmapΣ Σ : subG lockmapΣ Σ → lockmapG Σ.
Proof. solve_inG. Qed.

Section heap.
Context `{!heapGS Σ}.
Context `{!lockmapG Σ}.
Context `{!stagedG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "lockShard".
Definition lockshardN : namespace := nroot .@ "lockShardMem".

Definition locked (hm : gname) (addr : u64) : iProp Σ :=
  ( addr ↪[hm] true )%I.

Definition lockShard_addr gh (shardlock : loc) (addr : u64) (gheld : bool)
           (lockStatePtr : loc) (covered : gset u64) (P Pc : u64 -> iProp Σ) :=
  ( ∃ (cond : loc) (nwaiters : u64),
      "held" ∷ lockStatePtr ↦[lockState :: "held"] #gheld ∗
      "cond" ∷ lockStatePtr ↦[lockState :: "cond"] #cond ∗
      "waiters" ∷ lockStatePtr ↦[lockState :: "waiters"] #nwaiters ∗
      "#Hcond" ∷ lock.is_cond cond #shardlock ∗
      "%Hcovered" ∷ ⌜ addr ∈ covered ⌝ ∗
      "Hwaiters" ∷ ( ⌜ gheld = true ⌝ ∨
        ( ⌜ gheld = false ⌝ ∗ addr ↪[gh] false ∗ crash_borrow (P addr) (Pc addr) ) )
  )%I.

Definition is_lockShard_inner (mptr : loc) (shardlock : loc)
           (ghostHeap : gname) (covered : gset u64) (P Pc : u64 -> iProp Σ) : iProp Σ :=
  ( ∃ (m: Map.t loc) ghostMap,
      is_map mptr 1 m ∗
      ghost_map_auth ghostHeap 1 ghostMap ∗
      ( [∗ map] addr ↦ gheld; lockStatePtrV ∈ ghostMap; m,
          lockShard_addr ghostHeap shardlock addr gheld lockStatePtrV covered P Pc ) ∗
      crash_borrow ([∗ set] addr ∈ covered,
                     ⌜m !! addr = None⌝ → P addr)
                   ([∗ set] addr ∈ covered,
                     ⌜m !! addr = None⌝ → Pc addr)
  )%I.

Definition is_lockShard (ls : loc) (ghostHeap : gname) (covered : gset u64) (P Pc : u64 -> iProp Σ) : iProp Σ :=
  ( ∃ (shardlock mptr : loc),
      "#Hcovered_crash_wand" ∷ □ ([∗ set] a ∈ covered, (P a -∗ Pc a)) ∗
      "#Hls_mu" ∷ readonly (ls ↦[lockShard :: "mu"] #shardlock) ∗
      "#Hls_state" ∷ readonly (ls ↦[lockShard :: "state"] #mptr) ∗
      "#Hlock" ∷ is_lock lockN #shardlock (is_lockShard_inner mptr shardlock ghostHeap covered P Pc)
  )%I.

Definition is_free_lockShard (ls : loc) : iProp Σ :=
  ( ∃ (shardlock mptr : loc),
      "#Hls_mu" ∷ readonly (ls ↦[lockShard :: "mu"] #shardlock) ∗
      "#Hls_state" ∷ readonly (ls ↦[lockShard :: "state"] #mptr) ∗
      "Hmap" ∷ is_map mptr 1 (∅ : Map.t loc) ∗
      "Hfree" ∷ crash_lock.is_free_crash_lock shardlock
  )%I.

Global Instance is_lockShard_persistent ls gh (P Pc : u64 -> iProp Σ) c : Persistent (is_lockShard ls gh c P Pc).
Proof. apply _. Qed.

Opaque zero_val.

Theorem wp_mkLockShard :
  {{{ True }}}
    mkLockShard #()
  {{{ ls, RET #ls; is_free_lockShard ls }}}.
Proof.
  iIntros (Φ) "Hinit HΦ".
  rewrite /mkLockShard.
  wp_pures.

  wp_apply (wp_NewMap loc).
  iIntros (mref) "Hmap".
  wp_pures.

  wp_apply crash_lock.wp_new_free_crash_lock; auto.

  iIntros (shardlock) "Hfreelock".

  wp_pures.
  wp_apply wp_allocStruct; first by eauto.
  iIntros (ls) "Hls".
  wp_pures.

  iDestruct (struct_fields_split with "Hls") as "(Hmu & Hstate & _)".
  iMod (readonly_alloc_1 with "Hmu") as "mu".
  iMod (readonly_alloc_1 with "Hstate") as "Hstate".
  iModIntro.
  iApply "HΦ".
  iExists _, _. iFrame "# ∗".
Qed.

Theorem alloc_lockShard_init_cancel covered ls (P Pc : u64 → iProp Σ):
   ([∗ set] a ∈ covered, P a ∗ □ (P a -∗ Pc a)) -∗
    is_free_lockShard ls -∗
    init_cancel (∃ gh, is_lockShard ls gh covered P Pc) ([∗ set] a ∈ covered, Pc a).
Proof.
  iIntros "HP Hfree".
  rewrite /is_free_lockShard.
  iNamed "Hfree".

  iDestruct "Hfree" as "(Hfree1&Htoks)".

  iDestruct (big_sepS_sep with "HP") as "(HP&#Hwand)".
  iPoseProof (crash_borrow_init_cancel ([∗ set] a ∈ covered, ⌜(∅ : Map.t loc) !! a = None⌝ → P a)
                                ([∗ set] a ∈ covered, ⌜(∅ : Map.t loc) !! a = None⌝ → Pc a)
                                with "[$] [HP] []") as "Hcancel".
  { iApply (big_sepS_mono with "HP"). iIntros; eauto. }
  { iIntros "!> Hs".
    iDestruct (big_sepS_sep with "[$Hs $Hwand]") as "Hs".
    iApply (big_sepS_mono with "Hs").
    iIntros (??) "(HP&Hw) Hlook". iApply "Hw". iApply "HP". eauto. }
  iApply (init_cancel_fupd ⊤).
  iApply (init_cancel_wand with "Hcancel [Hmap Hfree1]").
  - iMod (ghost_map_alloc (∅: gmap u64 bool)) as (hG) "[Hheapctx _]".
    iIntros "Hborrow".
    iAssert (is_lockShard_inner mptr shardlock hG covered P Pc) with "[Hborrow Hmap Hheapctx]" as "Hinner".
    {
      iExists _, _.
      iFrame. eauto.
    }
    iMod (alloc_lock lockN with "Hfree1 Hinner") as "Hlock".
    iModIntro.
    iExists _, _, _. iFrame "# ∗". iModIntro.
    iApply (big_sepS_mono with "Hwand"); eauto.
    iIntros (??) "H". iApply "H".
  - iIntros "H2". iApply (big_sepS_mono with "H2").
    iIntros (??) "HP". iApply "HP". eauto.
Qed.

Theorem alloc_lockShard_wpc k covered Φ Φc e ls (P Pc : u64 → iProp Σ):
   ([∗ set] a ∈ covered, P a ∗ □ (P a -∗ Pc a)) -∗
    is_free_lockShard ls -∗
    (∀ gh, is_lockShard ls gh covered P Pc -∗
           WPC e @ k; ⊤ {{ Φ }} {{ ([∗ set] a ∈ covered, Pc a) -∗ Φc }}) -∗
    WPC e @ k; ⊤ {{ Φ }} {{ Φc }}.
Proof.
  iIntros "HP Hfree Hwp".
  iDestruct (alloc_lockShard_init_cancel with "HP Hfree") as "H".
  iApply (init_cancel_elim with "H"). iDestruct 1 as (gh) "Hshard".
  iApply "Hwp". eauto.
Qed.

Theorem wp_lockShard__acquire ls gh covered (addr : u64) (P Pc : u64 -> iProp Σ) :
  {{{ is_lockShard ls gh covered P Pc ∗
      ⌜addr ∈ covered⌝ }}}
    lockShard__acquire #ls #addr
  {{{ RET #(); crash_borrow (P addr) (Pc addr) ∗ locked gh addr }}}.
Proof.
  iIntros (Φ) "[Hls %] HΦ".
  iNamed "Hls".

  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Hinner]".

  wp_pures.
  wp_apply (wp_forBreak
    (fun b => is_lockShard_inner mptr shardlock gh covered P Pc ∗
              lock.locked #shardlock ∗ if b then emp else crash_borrow (P addr) (Pc addr) ∗ locked gh addr)%I
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
          iExists _, _. by iFrame.

      + wp_untyped_load.
        wp_storeField.
        wp_pures.

        iDestruct "Hwaiters" as "[% | [_ [Haddr Hp]]]"; try congruence.
        iMod (ghost_map_update true with "Hghctx Haddr") as "[Hghctx Haddr]".

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

      iEval (rewrite struct_mapsto_eq) in "Hacquired".
      iDestruct "Hacquired" as "[[Hacquired _] _]"; rewrite loc_add_0.
      wp_untyped_store.

      (* Creating a new lock, so we split out that piece from the shard's primary crash borrow *)

        set (m' := typed_map.map_insert m addr lst).
        iApply (wpc_wp NotStuck 0 _ _ _ True).
        iApply (wpc_crash_borrow_split _ _ _ _ _ _ _
                                       ([∗ set] addr0 ∈ covered, ⌜m' !! addr0 = None⌝ → P addr0)
                                       (P addr)
                                       ([∗ set] addr0 ∈ covered, ⌜m' !! addr0 = None⌝ → Pc addr0)
                                       (Pc addr)
                  with "Hcovered"); auto.
        { iNext. iIntros "Hcovered".
          iDestruct (big_sepS_delete with "Hcovered") as "[Hp Hcovered]"; eauto.
          iSplitR "Hp".
          2: { iApply "Hp"; done. }
          replace (covered) with ({[ addr ]} ∪ (covered ∖ {[ addr ]})) at 4.
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
        {
          iNext. iModIntro.
          iIntros "Hs". iDestruct (big_sepS_sep with "[$Hs $Hcovered_crash_wand]") as "Hs".
          iApply (big_sepS_mono with "Hs"); iIntros (??) "(H1&H2) Hlook".
          iApply "H2". iApply "H1". eauto.
        }
        {
          iNext. iModIntro.
          iIntros "HP".
          iDestruct (big_sepS_elem_of_acc with "Hcovered_crash_wand") as "(Hw&_)"; eauto.
          iApply "Hw"; eauto.
        }
        {
          iNext. iIntros "(Hcovered&Ha)".
          assert (covered = ({[ addr ]} ∪ (covered ∖ {[ addr ]}))) as Hcovered.
          {
            rewrite -union_difference_L; auto.
            set_solver.
          }
          rewrite Hcovered.
          iApply (big_sepS_insert).
          { set_solver. }
          iSplitL "Ha".
          { by iFrame. }
          iDestruct (big_sepS_insert with "Hcovered") as "(_&Hcovered)".
          { set_solver. }
          iApply (big_sepS_mono with "Hcovered").
          { iIntros (x Hin) "HP %Hlookup". iApply "HP".
            iPureIntro. rewrite /m'.
            rewrite lookup_insert_ne //.
            set_solver.
          }
        }
        iApply wp_wpc. wp_pures.
        wp_untyped_load.
        wp_pures.
        iModIntro. iIntros "(Hborrow&Hrest)". iSplit; first auto.
        iApply "HΦloop".
        iFrame.

        iExists _, _. iFrame.
        iApply (big_sepM2_insert); [auto | auto | ].
        iFrame.
        iExists  _, _.
        iFrame "∗ Hcond".
        iFrame.
        iSplitL; [ iPureIntro; congruence | ].
        iLeft; done.
  }
  iIntros "(Hinner & Hlocked & Hp & Haddrlocked)".
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hinner]").
  {
    iSplitR. { iApply "Hlock". }
    iFrame.
  }

  iApply "HΦ".
  by iFrame.
Qed.

Theorem wp_lockShard__release ls (addr : u64) (P Pc : u64 -> iProp Σ) covered gh :
  {{{ is_lockShard ls gh covered P Pc ∗ crash_borrow (P addr) (Pc addr) ∗ locked gh addr }}}
    lockShard__release #ls #addr
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(Hls & Hp & Haddrlocked) HΦ".
  iNamed "Hls".
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

  destruct (bool_decide (int.Z 0 < int.Z nwaiters))%Z.

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

      rewrite insert_delete.
      rewrite insert_delete.
      rewrite (insert_id m); eauto.
    }

    iApply "HΦ".
    auto.
  }

  {
    wp_pures.
    wp_bind (struct.loadF _ _ _).
    iApply (wpc_wp NotStuck 0 _ _ _ True).
    set (m' := delete addr m).
    iApply (wpc_crash_borrow_combine _ _ _ _ _
                                   ([∗ set] addr0 ∈ covered, ⌜m' !! addr0 = None⌝ → P addr0)
                                   ([∗ set] addr0 ∈ covered, ⌜m' !! addr0 = None⌝ → Pc addr0)
                                   (P addr)
                                   ([∗ set] addr0 ∈ covered, ⌜m !! addr0 = None⌝ → P addr0)
                                   (Pc addr)
                                   ([∗ set] addr0 ∈ covered, ⌜m !! addr0 = None⌝ → Pc addr0)
              with "Hp Hcovered"); auto.
    {
      iNext. iModIntro.
      iIntros "Hs". iDestruct (big_sepS_sep with "[$Hs $Hcovered_crash_wand]") as "Hs".
      iApply (big_sepS_mono with "Hs"); iIntros (??) "(H1&H2) Hlook".
      iApply "H2". iApply "H1". eauto.
    }
    { iNext. iIntros "Hcovered".
      iDestruct (big_sepS_delete with "Hcovered") as "[Hp Hcovered]"; eauto.
      iSplitL "Hp".
      { iApply "Hp". rewrite lookup_delete //. }

      iApply (big_sepS_delete _ _ addr); first auto.
      iSplitL "".
      { iIntros "%Hfalse". exfalso.
        match goal with
          | [ H1 : m !! addr = Some _ |- _ ] => rewrite Hfalse in H1; inversion H1
        end.
      }
      iApply (big_sepS_mono with "Hcovered"). iIntros (x Hin) "HP %Hlookup".
      iApply "HP". iPureIntro.
      destruct (decide (addr = x)); subst.
      { set_solver. }
      rewrite lookup_delete_ne //.
    }
    {
      iNext. iIntros "(Ha&Hcovered)".
      assert (covered = ({[ addr ]} ∪ (covered ∖ {[ addr ]}))) as Hcovered'.
      {
        rewrite -union_difference_L; auto.
        set_solver.
      }
      rewrite Hcovered'.
      iApply (big_sepS_insert).
      { set_solver. }
      iSplitL "Ha".
      { by iFrame. }
      iDestruct (big_sepS_insert with "Hcovered") as "(_&Hcovered)".
      { set_solver. }
      iApply (big_sepS_mono with "Hcovered").
      { iIntros (x Hin) "HP %Hlookup". iApply "HP".
        iPureIntro. rewrite /m'.
        rewrite lookup_delete_ne in Hlookup; auto. set_solver.
      }
    }
    iApply wp_wpc.

    wp_loadField.
    iIntros "Hcovered". iSplit; first done.
    wp_apply (wp_MapDelete with "[$Hmptr]").
    iIntros "Hmptr".

    iMod (ghost_map_delete with "Hghctx Haddrlocked") as "Hghctx".

    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "∗ Hlock".
      iExists _, (delete addr gm).
      iFrame.
    }
    by iApply "HΦ".
  }
Qed.


Definition NSHARD_def : Z := Eval vm_compute in (match NSHARD with #(LitInt z) => int.Z z | _ => 0 end).
Definition NSHARD_aux : seal (@NSHARD_def). Proof. by eexists. Qed.
Definition NSHARD := NSHARD_aux.(unseal).
Definition NSHARD_eq : @NSHARD = @NSHARD_def := NSHARD_aux.(seal_eq).

Ltac unseal_nshard := rewrite NSHARD_eq /NSHARD_def.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Definition covered_by_shard (shardnum : Z) (covered: gset u64) : gset u64 :=
  filter (λ x, Z.modulo (int.Z x) NSHARD = shardnum) covered.

Lemma covered_by_shard_mod addr covered :
  addr ∈ covered <->
  addr ∈ covered_by_shard (int.nat (word.modu addr NSHARD)) covered.
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
Proof.
  rewrite /covered_by_shard filter_empty_L //.
Qed.

Lemma covered_by_shard_insert x X :
  covered_by_shard (int.Z (word.modu x (U64 NSHARD))) ({[x]} ∪ X) =
  {[x]} ∪ covered_by_shard (int.Z (word.modu x (U64 NSHARD))) X.
Proof.
  rewrite /covered_by_shard filter_union_L filter_singleton_L //.
  unseal_nshard.
  word.
Qed.

Lemma covered_by_shard_insert_ne (x x' : u64) X :
  (int.Z x `mod` NSHARD)%Z ≠ int.Z x' ->
  covered_by_shard (int.Z x') ({[x]} ∪ X) =
    covered_by_shard (int.Z x') X.
Proof.
  intros.
  rewrite /covered_by_shard filter_union_L filter_singleton_not_L.
  { set_solver. }
  auto.
Qed.

Lemma rangeSet_lookup_mod (x : u64) (n : Z) :
  (0 < n < 2^64)%Z ->
  word.modu x (U64 n) ∈ rangeSet 0 n.
Proof.
  intros.
  apply rangeSet_lookup; try word.
  word_cleanup.
  word.
Qed.

Lemma covered_by_shard_split (P : u64 -> iProp Σ) covered :
  ( [∗ set] a ∈ covered, P a ) -∗
  [∗ set] shardnum ∈ rangeSet 0 NSHARD,
    [∗ set] a ∈ covered_by_shard (int.Z shardnum) covered, P a.
Proof.
  induction covered using set_ind_L.
  - iIntros "H".
    setoid_rewrite covered_by_shard_empty.
    setoid_rewrite big_sepS_empty.
    iApply big_sepS_forall. done.
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

Lemma covered_by_shard_join (P : u64 -> iProp Σ) covered :
  ([∗ set] shardnum ∈ rangeSet 0 NSHARD,
    [∗ set] a ∈ covered_by_shard (int.Z shardnum) covered, P a) -∗
  ( [∗ set] a ∈ covered, P a ).
Proof.
  induction covered using set_ind_L.
  - iIntros "H".
    setoid_rewrite covered_by_shard_empty.
    setoid_rewrite big_sepS_empty.
    eauto.
  - iIntros "H".
    iApply (big_sepS_insert); try assumption.
    iAssert (P x ∗ [∗ set] shardnum ∈ rangeSet 0 NSHARD, [∗ set] a ∈ covered_by_shard (int.Z shardnum) X, P a)%I
       with "[H]" as "($&H)"; last first.
    { iApply IHcovered. eauto. }
    replace (rangeSet 0 NSHARD) with ({[ word.modu x NSHARD ]} ∪
                                      rangeSet 0 NSHARD ∖ {[ word.modu x NSHARD ]}).
    2: {
      rewrite -union_difference_L; auto.
      assert (0 < NSHARD < 2^64)%Z as Hbound by (unseal_nshard; done).
      pose proof (rangeSet_lookup_mod x NSHARD Hbound).
      set_solver.
    }

    iDestruct (big_sepS_insert with "H") as "[Hthis Hother]"; first by set_solver.
    rewrite covered_by_shard_insert.
    iDestruct (big_sepS_insert with "Hthis") as "($&Hrest)".
    { intro Hx. apply H. apply covered_by_shard_mod.
      rewrite Z2Nat.id; eauto.
      revert Hx. unseal_nshard. word. }
    iApply big_sepS_insert; first by set_solver.
    iFrame.
    iApply (big_sepS_mono with "Hother").
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

Definition is_lockMap (l: loc) (ghs: list gname) (covered: gset u64) (P Pc: u64 -> iProp Σ) : iProp Σ :=
  ∃ (shards: list loc) (shardslice: Slice.t),
    "#Href" ∷ readonly (l ↦[LockMap :: "shards"] (slice_val shardslice)) ∗
    "#Hslice" ∷ readonly (is_slice_small shardslice (struct.ptrT lockShard) 1 shards) ∗
    "%Hlen" ∷ ⌜ length shards = Z.to_nat NSHARD ⌝ ∗
    "#Hshards" ∷ [∗ list] shardnum ↦ shardloc; shardgh ∈ shards; ghs,
      is_lockShard shardloc shardgh (covered_by_shard shardnum covered) P Pc.

Definition is_free_lockMap (l: loc) : iProp Σ :=
  ∃ (shards: list loc) (shardslice: Slice.t),
    "#Href" ∷ readonly (l ↦[LockMap :: "shards"] (slice_val shardslice)) ∗
    "#Hslice" ∷ readonly (is_slice_small shardslice (struct.ptrT lockShard) 1 shards) ∗
    "%Hlen" ∷ ⌜ length shards = Z.to_nat NSHARD ⌝ ∗
    "Hfree_shards" ∷ [∗ list] shardnum ↦ shardloc ∈ shards, is_free_lockShard shardloc.

Definition Locked (ghs : list gname) (addr : u64) : iProp Σ :=
  ∃ gh,
    ⌜ ghs !! (Z.to_nat (Z.modulo (int.Z addr) NSHARD)) = Some gh ⌝ ∗
    locked gh addr.

Definition CrashLocked lk (ghs : list gname) (addr : u64) P Pcrash : iProp Σ :=
  ∃ covered,
  crash_borrow (P addr) (Pcrash addr) ∗
  is_lockMap lk ghs covered P Pcrash ∗
  Locked ghs addr.

(* XXX why is this needed here? *)
Opaque load_ty.
Opaque lockShard.

Theorem wp_MkLockMap :
  {{{ True }}}
    MkLockMap #()
  {{{ l, RET #l; is_free_lockMap l }}}.
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
                          ∃ s shardlocs,
                            "Hvar" ∷ shards ↦[slice.T (refT (struct.t lockShard))] (slice_val s) ∗
                            "Hslice" ∷ is_slice s (struct.ptrT lockShard) 1 shardlocs ∗
                            "%Hlen" ∷ ⌜ length shardlocs = int.nat i ⌝ ∗
                            "Hshards" ∷ [∗ list] shardnum ↦ shardloc ∈ shardlocs,
                              is_free_lockShard shardloc)%I
            with "[] [$Hi Hvar Hcovered]").
  { word. }
  { clear Φ.
    iIntros (i).
    iIntros "!>" (Φ) "(HI & Hi & %Hibound) HΦ".
    iNamed "HI".
    wp_pures.
    wp_apply (wp_mkLockShard).
    iIntros (ls) "Hls".
    wp_load.
    wp_apply (wp_SliceAppend (V:=loc) with "Hslice").
    iIntros (s') "Hslice".
    wp_store.
    iApply "HΦ".
    iFrame "Hi".
    iExists _, _.
    iFrame "Hvar Hslice".
    iSplitR.
    { rewrite app_length Hlen /=. word. }
    iModIntro.
    iApply big_sepL_app.
    iFrame. eauto.
  }
  {
    iExists _, nil.
    iFrame "Hvar".
    iSplitR.
    { iApply is_slice_zero. }
    iSplitR.
    { done. }
    eauto.
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
  { iPureIntro. rewrite Hlen. unseal_nshard. reflexivity. }
  iApply "Hshards".
Qed.

Lemma big_sepL_seqZ {A} i (n : nat) (Φ : Z → iProp Σ) (ls : list A):
  length ls = n →
  ([∗ list] k ∈ seqZ i n, Φ k) ⊣⊢ ([∗ list] k ↦ _ ∈ ls, Φ (i + k)).
Proof.
  iIntros (Hlen).
  iInduction n as [| n] "IH" forall (ls Hlen).
  { destruct ls; last (simpl in Hlen; congruence). eauto. }
  induction ls as [| a ls _] using rev_ind.
  { simpl in Hlen; congruence. }
  rewrite seqZ_S. rewrite ?big_sepL_app.
  iSplit.
  - iDestruct 1 as "(H1&H2)".
    rewrite app_length in Hlen.
    iSplitL "H1".
    { iApply "IH".
      { iPureIntro. simpl in Hlen; lia. }
      eauto. }
    rewrite ?big_sepL_singleton.
    iExactEq "H2". f_equal. simpl in Hlen. lia.
  - iDestruct 1 as "(H1&H2)".
    rewrite app_length in Hlen.
    iSplitL "H1".
    { iApply "IH"; iFrame.
      { iPureIntro. simpl in Hlen; lia. }
    }
    rewrite ?big_sepL_singleton.
    iExactEq "H2". f_equal. simpl in Hlen. lia.
Qed.

Lemma big_sepS_rangeSet_sepL {A} i (n : Z) (Φ : Z → iProp Σ) (ls : list A):
  0 ≤ i → 0 ≤ n → i + n < 2 ^ 64 →
  length ls = Z.to_nat n →
  ([∗ set] k ∈ rangeSet i n, Φ (int.Z k)) ⊣⊢ ([∗ list] k ↦ _ ∈ ls, Φ (i + k)).
Proof.
  intros Hlen1 Hlen2 Hlen3 Hlen4.
  rewrite /rangeSet.
  rewrite big_sepS_list_to_set; last first.
  { apply seq_U64_NoDup; auto. }
  rewrite big_sepL_fmap.
  replace n with (Z.of_nat (Z.to_nat n)); last first.
  { lia. }
  rewrite (big_sepL_seqZ _ _ _ ls); try eassumption.
  iApply big_sepL_proper.
  { iIntros (?? Hlookup) => /=. f_equiv.
    apply leibniz_equiv_iff.
    apply lookup_lt_Some in Hlookup.
    word. }
Qed.

Theorem alloc_lockMap_init_cancel covered ls (P Pc : u64 → iProp Σ):
   ([∗ set] a ∈ covered, P a ∗ □ (P a -∗ Pc a)) -∗
    is_free_lockMap ls -∗
    init_cancel (∃ gh, is_lockMap ls gh covered P Pc) ([∗ set] a ∈ covered, Pc a).
Proof.
  iIntros "Hcovered Hfree".
  iNamed "Hfree".
  iDestruct (big_sepS_sep with "Hcovered") as "(Hcovered&#Hcrash_wand)".
  iDestruct (covered_by_shard_split with "Hcovered") as "Hsplit".
  iDestruct (big_sepS_rangeSet_sepL _ _
                                     (λ z, [∗ set] a ∈ covered_by_shard z covered, P a)%I
                with "Hsplit") as "Hsplit"; try eassumption; try lia.
  { rewrite NSHARD_eq /NSHARD_def. lia. }
  { rewrite NSHARD_eq /NSHARD_def. lia. }
  iDestruct (big_sepL_sep with "[$Hfree_shards $Hsplit]") as "Hfree".
  iAssert ([∗ list] shardnum↦shardloc ∈ shards,
           init_cancel (∃ gh, is_lockShard shardloc gh (covered_by_shard shardnum covered) P Pc)
                 ([∗ set] a ∈ (covered_by_shard shardnum covered), Pc a))%I
          with "[Hfree]" as "H".
  { iApply (big_sepL_wand with "Hfree").
    iApply big_sepL_intro. iModIntro. iIntros (k x Hlookup) "(Hfree&Hcovered)".
    iApply (alloc_lockShard_init_cancel with "[Hcovered] [$]").
    iApply big_sepS_sep.
    replace (0 + Z.of_nat k) with (Z.of_nat k) by lia. iFrame.
    rewrite /covered_by_shard.
    iApply big_sepS_filter.
    iApply (big_sepS_mono with "Hcrash_wand"); eauto.
  }
  iDestruct (big_sepL_init_cancel with "[$]") as "H".
  iApply (init_cancel_wand with "H"); last first.
  { iIntros "H".
    iApply covered_by_shard_join.
    rewrite (big_sepS_rangeSet_sepL _ _ (λ z, [∗ set] a ∈ covered_by_shard z covered, Pc a)%I
                                    shards); auto; try lia.
    { rewrite NSHARD_eq /NSHARD_def. lia. }
    { rewrite NSHARD_eq /NSHARD_def. lia. }
  }
  iIntros "H".
  iAssert (∃ ghs, ([∗ list] shardnum↦shardloc;shardgh ∈ shards;ghs, is_lockShard shardloc shardgh
                                                          (covered_by_shard shardnum covered) P Pc))%I
          with "[H]"
          as "Hshards".
  { iClear "Href Hslice Hcrash_wand". clear.
    iInduction shards as [| shard shards] "IH" using rev_ind; first eauto.
    rewrite big_sepL_app. iDestruct "H" as "(Hrest&H1)".
    iEval (rewrite big_sepL_singleton) in "H1".
    iDestruct "H1" as (gh) "H1".
    iDestruct ("IH" with "[Hrest]") as (ghs) "H".
    { eauto. }
    iExists (ghs ++ [gh]).
    iApply (big_sepL2_app with "[$]").
    simpl. iFrame.
  }
  iDestruct "Hshards" as (ghs) "Hshards".
  rewrite /is_lockMap. iExists ghs, _, _. iFrame "# %"; eauto.
Qed.


Theorem alloc_lockMap k covered Φ Φc e ls (P Pc : u64 → iProp Σ):
   ([∗ set] a ∈ covered, P a ∗ □ (P a -∗ Pc a)) -∗
    is_free_lockMap ls -∗
    (∀ gh, is_lockMap ls gh covered P Pc -∗
           WPC e @ k; ⊤ {{ Φ }} {{ ([∗ set] a ∈ covered, Pc a) -∗ Φc }}) -∗
    WPC e @ k; ⊤ {{ Φ }} {{ Φc }}.
Proof.
  iIntros "Hcovered Hfree Hwp".
  iDestruct (alloc_lockMap_init_cancel with "[$] [$]") as "Hcancel".
  iApply (init_cancel_elim with "Hcancel").
  iDestruct 1 as (gh) "H". iApply "Hwp". eauto.
Qed.

Theorem wp_LockMap__Acquire l ghs covered (addr : u64) (P Pc : u64 -> iProp Σ) :
  {{{ is_lockMap l ghs covered P Pc ∗
      ⌜addr ∈ covered⌝ }}}
    LockMap__Acquire #l #addr
  {{{ RET #(); CrashLocked l ghs addr P Pc }}}.
Proof.
  iIntros (Φ) "[Hlm %] HΦ".
  iNamed "Hlm".

  wp_call.
  wp_loadField.

  iMod (readonly_load with "Hslice") as (q) "Hslice_copy".

  iDestruct (big_sepL2_length with "Hshards") as "%Hlen2".

  list_elem shards (int.nat (word.modu addr NSHARD)) as shard.
  { revert Hlen. unseal_nshard. word. }
  list_elem ghs (int.nat (word.modu addr NSHARD)) as gh.
  { revert Hlen. unseal_nshard. word. }

  wp_apply (wp_SliceGet _ _ _ _ _ shards with "[$Hslice_copy]").
  { revert Hshard_lookup. unseal_nshard. eauto. }
  iIntros "Hslice_copy".

  iDestruct (big_sepL2_lookup with "Hshards") as "Hshard"; eauto.
  wp_apply (wp_lockShard__acquire with "[$Hshard]").
  { iPureIntro. rewrite -covered_by_shard_mod. auto. }

  iIntros "[HP Hlocked]".
  iApply "HΦ".
  iFrame "HP".

  iExists _. iFrame.
  rewrite /Locked. iSplitR "Hlocked"; last first.
  { iExists _. iFrame. iPureIntro.
    rewrite -Hgh_lookup. f_equal.
    unseal_nshard.
    word. }
  iExists _, _. iFrame "# ∗". eauto.
Qed.

Theorem wp_LockMap__Release l ghs (addr : u64) (P Pc : u64 -> iProp Σ) :
    {{{ CrashLocked l ghs addr P Pc }}}
      LockMap__Release #l #addr
    {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hcrash_locked HΦ".
  iDestruct "Hcrash_locked" as (covered) "(HP&#His_lock&Hlocked)".
  iNamed "His_lock".
  wp_call.
  wp_loadField.

  iMod (readonly_load with "Hslice") as (q) "Hslice_copy".

  list_elem shards (int.nat (word.modu addr NSHARD)) as shard.
  { revert Hlen. unseal_nshard. word. }

  iDestruct "Hlocked" as (gh) "[% Hlocked]".

  wp_apply (wp_SliceGet _ _ _ _ _ shards with "[$Hslice_copy]").
  { revert Hshard_lookup. unseal_nshard. eauto. }
  iIntros "Hslice_copy".

  iDestruct (big_sepL2_lookup with "Hshards") as "Hshard"; eauto.
  { erewrite <- H. unseal_nshard. f_equal. word. }

  wp_apply (wp_lockShard__release with "[$Hshard $HP $Hlocked]").
  iApply "HΦ". done.
Qed.

Lemma use_CrashLocked k E1 e lk ghs addr R Rcrash Φ Φc :
  language.to_val e = None →
  CrashLocked lk ghs addr R Rcrash -∗
  Φc ∧ (R addr -∗
       WPC e @ k; E1 {{ λ v, (CrashLocked lk ghs addr R Rcrash -∗ (Φc ∧ Φ v)) ∗ R addr }}
                                       {{ Φc ∗ Rcrash addr }}) -∗
  WPC e @ k; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hcrash_locked H".
  iDestruct "Hcrash_locked" as (?) "(Hfull&#His_lock&Hlocked)".
  iApply (wpc_crash_borrow_open with "[$]"); auto.
  iSplit.
  - iDestruct "H" as "($&_)".
  - iIntros "HR". iDestruct "H" as "(_&H)".
    iSpecialize ("H" with "[$]").
    iApply (wpc_strong_mono with "H"); eauto.
    iSplit.
    * iIntros (?) "(Hclose&?)". iModIntro. iFrame. iFrame "#".
      iIntros. iApply "Hclose". iFrame; eauto.
    * iIntros. iIntros "!>". eauto.
Qed.

End heap.
