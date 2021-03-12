From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import liftable auth_map.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import simple.
From Perennial.program_proof Require Import txn.txn_proof marshal_proof addr_proof crash_lockmap_proof addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_proof buftxn.sep_buftxn_recovery_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List range_set.
From Perennial.algebra Require Import log_heap.
From Perennial.program_logic Require Import spec_assert.
From Perennial.goose_lang.lib Require Import slice.typed_slice into_val.
From Perennial.program_proof.simple Require Import spec invariant common.
From Perennial.goose_lang Require Import crash_modality.

Section stable.
Context `{!heapG Σ}.
Context `{!simpleG Σ}.

Global Instance is_inode_stable_set_stable γsrc γ':
    IntoCrash ([∗ set] a ∈ covered_inodes, is_inode_stable γsrc γ' a)
              (λ _, ([∗ set] a ∈ covered_inodes, is_inode_stable γsrc γ' a))%I.
Proof. rewrite /IntoCrash. iApply post_crash_nodep. Qed.

Global Instance is_txn_durable_stable γ dinit logm:
    IntoCrash (is_txn_durable γ dinit logm) (λ _, is_txn_durable γ dinit logm).
Proof.
  rewrite /IntoCrash. iNamed 1.
  iDestruct (post_crash_nodep with "Hlogm") as "Hlogm".
  iDestruct (post_crash_nodep with "Hasync_ctx") as "Hasync_ctx".
  iCrash. rewrite /is_txn_durable. iFrame.
Qed.

Lemma is_source_into_crash P P' γsrc:
  (∀ σ, P σ -∗ post_crash (λ hG, P' hG σ)) -∗
  is_source P γsrc -∗ post_crash (λ hG, is_source (P' hG) γsrc).
Proof.
  iIntros "HPwand Hsrc".
  iNamed "Hsrc".
  iDestruct (post_crash_nodep with "Hnooverflow") as "-#Hnooverflow'".
  iDestruct (post_crash_nodep with "Hsrcheap") as "Hsrcheap".
  iDestruct ("HPwand" with "[$]") as "HP".
  iCrash. iExists _. iFrame. eauto.
Qed.

End stable.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!simpleG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Context (P1 : SimpleNFS.State → iProp Σ).
Context (P2 : SimpleNFS.State → iProp Σ).

Open Scope Z_scope.

Definition fs_kinds sz : gmap u64 bufDataKind :=
  {[U64 513 := KindInode]} ∪
  gset_to_gmap KindBlock (rangeSet 514 (sz - 514)).

Definition fs_dinit sz : gmap Z Block :=
  gset_to_gmap block0 (list_to_set $ seqZ 513 (sz-513)).

Lemma dom_fs_dinit:
  ∀ sz : Z,
    513 + 1 + (32 - 2) ≤ sz
    → dom (gset Z) (fs_dinit sz) = list_to_set (seqZ 513 (sz - 513)).
Proof.
  intros sz Hsz.
  rewrite /fs_dinit.
  rewrite dom_gset_to_gmap.
  auto with f_equal lia.
Qed.

Lemma dom_fs_kinds:
  ∀ sz : Z,
    513 + 1 + (32 - 2) ≤ sz
    → dom (gset u64) (fs_kinds sz) = list_to_set (U64 <$> seqZ 513 (sz - 513)).
Proof.
  intros sz Hsz.
  rewrite /fs_kinds.
  rewrite dom_union_L dom_singleton_L.
  rewrite dom_gset_to_gmap.
  rewrite /rangeSet.
  replace (seqZ 513 (sz - 513)) with ([513] ++ seqZ 514 (sz - 514)); auto.
  change ([513]) with (seqZ 513 1).
  rewrite <- seqZ_app by lia.
  auto with f_equal lia.
Qed.

Lemma gmap_curry_union K1 K2 `{Countable K1} `{Countable K2} A
      (m1 m2: gmap K1 (gmap K2 A)) :
  m1 ##ₘ m2 →
  gmap_curry (m1 ∪ m2) = gmap_curry m1 ∪ gmap_curry m2.
Proof.
  intros.
  apply map_eq; intros.
  rewrite lookup_union.
  destruct i as [i1 i2].
  rewrite !lookup_gmap_curry.
  rewrite lookup_union.
  destruct (m1 !! i1) eqn:?;
           destruct (m2 !! i1) eqn:?;
           simpl;
    auto.
  - apply map_disjoint_dom in H1.
    apply elem_of_dom_2 in Heqo.
    apply elem_of_dom_2 in Heqo0.
    set_solver.
  - destruct (g !! i2); simpl; auto.
  - rewrite /union_with /=.
    destruct (g !! i2); simpl; auto.
Qed.

Lemma gmap_curry_insert K1 K2 `{Countable K1} `{Countable K2} A
      k (m11: gmap K2 A) (m2: gmap K1 (gmap K2 A)) :
  m2 !! k = None →
  gmap_curry (<[k := m11]> m2) = map_fold (λ i2 x, <[(k,i2):=x]>) (gmap_curry m2) m11.
Proof.
  rewrite /gmap_curry => Hlookup.
  simpl.

  rewrite map_fold_insert_L //; last first.
  intros.
Admitted.

Lemma zero_disk_to_inodes γ sz :
  (513 + 1 + (32-2) ≤ sz < 2^49) →
  ([∗ map] a ↦ o ∈ kind_heap0 (fs_kinds sz), durable_mapsto_own γ a o) -∗
  ([∗ set] inum ∈ covered_inodes, is_inode_enc inum (U64 0) (U64 0) (durable_mapsto_own γ)) ∗
  ([∗ list] _ ↦ a ∈ seqZ 513 (32-2), durable_mapsto_own γ (blk2addr (U64 a)) (existT _ (bufBlock block0)))
.
Proof.
  iIntros (Hsz) "Hobjs".
  rewrite /fs_kinds.
  rewrite /kind_heap0.

  rewrite map_fmap_union.
  rewrite gmap_curry_union.
  2: {
    admit.
  }
  rewrite map_fmap_singleton.
  rewrite fmap_gset_to_gmap.
  rewrite big_sepM_union.
  2: {
    admit.
  }
  iDestruct "Hobjs" as "[Hinodes Hblocks]".
  rewrite /covered_inodes.
  iSplitL "Hinodes".
  - rewrite /is_inode_enc.
    admit.
  - admit.
Admitted.

(* amazingly not in Coq 8.12 *)
Lemma repeat_app {A} n1 n2 (x:A) :
  repeat x (n1+n2)%nat = repeat x n1 ++ repeat x n2.
Proof. induction n1; simpl; congruence. Qed.

(* sz is the actual size of the disk *)
Lemma wpc_Mkfs (d:loc) sz :
  (513 + 1 + (32-2) ≤ sz < 2^49) →
  {{{ 0 d↦∗ repeat block0 (Z.to_nat sz) ∗ P1 (gset_to_gmap [] (rangeSet 2 (NumInodes-2)))  }}}
    Mkfs #d @ 0; ⊤
  {{{ γtxn γsrc (txn:loc), RET #txn;
      let logm0 := Build_async (kind_heap0 (fs_kinds sz)) [] in
      is_txn_durable γtxn (fs_dinit sz) logm0 ∗
      is_source P1 γsrc
    }}}
   {{{ True }}}.
Proof.
  intros Hsz.
  iIntros (Φ Φc) "Hd HΦ".
  replace (Z.to_nat sz) with (513 + (Z.to_nat sz - 513))%nat by lia.
  rewrite repeat_app disk_array_app.
  iDestruct "Hd" as "[Hlog Hd]".
  rewrite repeat_length.
  change (0 + 513%nat) with 513.
  replace (Z.to_nat sz - 513)%nat with (Z.to_nat $ sz - 513) by lia.
  iMod (is_txn_durable_init (fs_dinit sz) (fs_kinds sz) _
          with "[$Hlog $Hd]") as (γ) "(Htxn & #Hlb & Hmapstos)".
  { rewrite -> Z2Nat.id by word.
    apply dom_fs_dinit; lia. }
  { rewrite -> Z2Nat.id by word.
    apply dom_fs_kinds; lia. }
  { rewrite /block_bytes.
    rewrite -> !Z2Nat.id by word.
    lia. }
  rewrite /Mkfs.
  wpc_pures.
  { crash_case; auto. }
  iCache (<disc> Φc)%I with "HΦ".
  { crash_case; auto. }
  wpc_apply (wpc_MkTxn (nroot.@"simple") with "[$Htxn]").
  { solve_ndisj. }
  { solve_ndisj. }
  iSplit.
  { iLeft in "HΦ".
    iIntros "!> H".
    iApply "HΦ"; auto. }
  iNext.
  iIntros (γ' txn_l) "Hpost".
  iDestruct "Hpost" as "(#Htxn & #Htxn_system & Hcfupd & Hcinv)".
  wpc_pures.
  wpc_frame "HΦ".
  wp_apply (wp_BufTxn__Begin with "[$Htxn $Htxn_system]").
  iIntros (γtxn l).
  iIntros "Hbuftxn".
  wp_pures.
  (* the interesting part, reasoning about [inodeInit]; will need to break apart
     Hmapstos and turn it into a bunch of inodes in order to lift them *)
Abort.

Lemma is_source_later_upd P P' γsrc:
  (∀ σ, ▷ P σ -∗ |C={⊤ ∖ ↑N}_10=> ▷ P σ ∗ ▷ P' σ) -∗
   ▷ is_source P γsrc -∗
   |C={⊤}_10=> ▷ is_source P' γsrc.
Proof.
  iIntros "Hwand H". iDestruct "H" as (?) "(>?&>%&>#?&?)".
  iSpecialize ("Hwand" with "[$]").
  iMod (cfupd_weaken_all with "Hwand") as "(HP1&HP2)"; auto.
  iModIntro.
  iNext. iExists _. iFrame "# ∗ %".
Qed.

Lemma crash_upd_src γsrc γ' src:
  dom (gset u64) src = covered_inodes →
  ("Hlmcrash" ∷ ([∗ set] y ∈ covered_inodes, is_inode_stable γsrc γ' y) ∗
  "Hsrcheap" ∷ map_ctx γsrc 1 src) ==∗
  ∃ γsrc',
  map_ctx γsrc 1 src ∗
  map_ctx γsrc' 1 src ∗
  [∗ set] y ∈ covered_inodes, is_inode_stable γsrc' γ' y.
Proof.
  iIntros (Hdom) "H". iNamed "H".
  iMod (map_init ∅) as (γsrc') "H".
  iMod (map_alloc_many src with "H") as "(Hctx&Hmapsto)".
  { intros. rewrite lookup_empty //=. }
  rewrite right_id_L.
  iModIntro. iExists γsrc'.
  rewrite -Hdom -?big_sepM_dom.
  iFrame "Hctx".
  iCombine "Hmapsto Hlmcrash" as "H".
  rewrite -big_sepM_sep.
  iApply (big_sepM_mono_with_inv with "Hsrcheap H").
  iIntros (k v Hlookup) "(Hctx&src&Hstable)".
  iNamed "Hstable".
  iDestruct (map_valid with "[$] [$]") as %Heq.
  subst. iFrame. iExists _. iFrame. rewrite /named. iExactEq "src". f_equal. congruence.
Qed.

Definition fs_cfupd_cancel dinit P :=
  (<disc> (|C={⊤}_10=>
    ∃ γ γsrc logm',
    is_txn_durable γ dinit logm' ∗
    ▷ is_source P γsrc ∗
    [∗ set] a ∈ covered_inodes, is_inode_stable γsrc γ a))%I.

Theorem wpc_Recover γ γsrc (d : loc) dinit logm :
  {{{
    <disc> (∀ σ, ▷ P1 σ -∗ |C={⊤ ∖ ↑N}_10=> ▷ P1 σ ∗ ▷ P2 σ) ∗
    is_txn_durable γ dinit logm ∗
    ▷ is_source P1 γsrc ∗
    [∗ set] a ∈ covered_inodes, is_inode_stable γsrc γ a
  }}}
    Recover #d @ 10; ⊤
  {{{ γsimp nfs, RET #nfs;
      is_fs P1 γsimp nfs dinit ∗ fs_cfupd_cancel dinit P2 }}}
  {{{
    ∃ γ' γsrc' logm',
    is_txn_durable γ' dinit logm' ∗
    ▷ is_source P2 γsrc' ∗
    [∗ set] a ∈ covered_inodes, is_inode_stable γsrc' γ' a
  }}}.
Proof using All.
  iIntros (Φ Φc) "(Hshift & Htxndurable & Hsrc & Hstable) HΦ".
  iMod (fupd_later_to_disc with "Hsrc") as "Hsrc".
  rewrite /Recover.
  iApply wpc_cfupd.
  wpc_pures.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro.
    iMod (is_source_later_upd P1 P2 with "Hshift Hsrc") as "Hsrc".
    iModIntro. iApply "HΦc".
    iExists _, _, _. iFrame. }

  wpc_apply (wpc_MkTxn Nbuftxn with "Htxndurable").
  { solve_ndisj. }
  { solve_ndisj. }

  iSplit.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iIntros "H".
    iDestruct "H" as (γ' logm') "(%Hkinds & Htxndurable)".
    iDestruct "Htxndurable" as "(Hdurable&[%Heq|#Hexch])".
    { subst.
      iMod (is_source_later_upd P1 P2 with "[$] Hsrc") as "Hsrc".
      iModIntro. iApply "HΦc". iExists _, _, _.
      iFrame. }
    iMod (big_sepS_impl_cfupd with "Hstable []") as "Hcrash".
    { iModIntro. iIntros (x Hx) "H".
      iApply (is_inode_stable_crash with "[$] H").
    }
    iMod (is_source_later_upd P1 P2 with "[$] Hsrc") as "Hsrc".
    iModIntro.
    iApply "HΦc".
    iExists _, _, _. iFrame.
  }

  iModIntro.
  iIntros (γ' l) "(#Histxn & #Htxnsys & Hcfupdcancel & #Htxncrash)".

  wpc_pures.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro.
    iMod (big_sepS_impl_cfupd with "Hstable []") as "Hcrash".
    { iModIntro. iIntros (x Hx) "H".
      iMod (is_inode_stable_crash with "Htxncrash H") as "H".
      iModIntro. iExact "H". }
    iMod "Hcfupdcancel" as ">Hcfupdcancel".
    iMod (is_source_later_upd P1 P2 with "[$] Hsrc") as "Hsrc".
    iModIntro.
    iApply "HΦc".
    iDestruct "Hcfupdcancel" as (?) "H".
    iExists _, _, _. iFrame.
  }

  wpc_apply (wpc_MkLockMap _ covered_inodes (is_inode_stable γsrc γ) (is_inode_stable γsrc γ') with "[Hstable]").
  { iApply (big_sepS_impl with "Hstable").
    iModIntro.
    iIntros (a Ha) "H". iFrame.
    iModIntro. iIntros ">Hstable".
    iMod (is_inode_stable_crash with "Htxncrash Hstable") as "Hstable".
    iModIntro. done. }

  iSplit.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iIntros "H".
    rewrite -big_sepS_later.
    iDestruct "H" as ">H".
    iMod "Hcfupdcancel" as ">Hcfupdcancel".
    iDestruct "Hcfupdcancel" as (?) "Hcfupdcancel".
    iMod (is_source_later_upd P1 P2 with "[$] Hsrc") as "Hsrc".
    iModIntro.
    iApply "HΦc".
    iExists _, _, _. iFrame.
  }

  iModIntro.
  iIntros (lm ghs) "[#Hlm Hlmcrash]".

  iMod (own_disc_fupd_elim with "Hsrc") as "Hsrc".
  iMod (inv_alloc N with "Hsrc") as "#Hsrc".

  iApply wp_wpc_frame'.
  iSplitL "Hlmcrash Hcfupdcancel HΦ Hsrc Hshift".
  {
    iAssert (fs_cfupd_cancel dinit P2)%I with "[-HΦ]" as "Hcancel".
    { iModIntro.
      rewrite -big_sepS_later.
      iMod "Hlmcrash" as ">Hlmcrash". iMod "Hcfupdcancel" as ">Hcfupdcancel".
      iIntros "#HC".
      iInv "Hsrc" as "Hopen" "Hclose".
      iDestruct "Hopen" as (?) "(>Hsrcheap&>%Hdom&>#Hnooverflow&HP)".
      iMod (crash_upd_src with "[$]") as (γsrc') "(Hsrcheap&Hsrcheap'&Hlmcrash)".
      { eauto. }
      iMod ("Hshift" with "HP HC") as "(HP1&HP2)".
      iMod ("Hclose" with "[HP1 Hsrcheap]") as "_".
      { iNext. iExists _. iFrame "# ∗ %". }
      iDestruct "Hcfupdcancel" as (?) "?".
      iExists γ', γsrc', _. iFrame.
      iModIntro. iNext. iExists _. iFrame "# ∗ %".
    }
    iSplit.
    { iDestruct "HΦ" as "[HΦc _]". iModIntro. iMod ("Hcancel"). iModIntro. by iApply "HΦc". }
    { iNamedAccu. }
  }

  wp_apply wp_allocStruct; first by eauto.
  iIntros (nfs) "Hnfs".

  iDestruct (struct_fields_split with "Hnfs") as "Hnfs". iNamed "Hnfs".
  iMod (readonly_alloc_1 with "t") as "#Ht".
  iMod (readonly_alloc_1 with "l") as "#Hl".

  iAssert (is_fs P1 (Build_simple_names γ γ' γsrc ghs) nfs dinit) with "[]" as "Hfs".
  { iExists _, _. iFrame "Ht Hl Histxn Htxnsys Htxncrash Hlm Hsrc". }
  wp_pures. iNamed 1.
  iRight in "HΦ". iApply "HΦ". iFrame "# ∗".
Qed.

End goose_lang.
