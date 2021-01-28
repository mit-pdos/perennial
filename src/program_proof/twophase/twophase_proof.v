From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.goose_nfsd Require Import twophase.
From Perennial.program_proof Require Import buftxn_proof.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof txn.txn_proof.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.Helpers Require Import PropRestore.
From Perennial.algebra Require Import auth_map.

Section goose_lang.
Context `{!buftxnG Σ}.
Context `{!heapG Σ}.

Definition get_addr_map_blknos {A} (m: gmap addr A) :=
  dom (gset u64) (gmap_addr_by_block m).

Definition get_disk_blknos (d: disk): gset u64 :=
  set_map (λ x, U64 (x / (block_bytes * 8))) (dom (gset Z) d).

Definition addr_wf (dinit: disk) a :=
  is_Some (dinit !! (addr2flat_z a)) ∧ int.Z (addrOff a) < block_bytes * 8.

Definition addr_wf' (dinit: disk) a :=
  (addrBlock a) ∈ get_disk_blknos dinit ∧ int.Z (addrOff a) < block_bytes * 8.

Lemma addr_wf_wf' dinit a:
  addr_wf dinit a → addr_wf' dinit a.
Proof.
  intros [Hblk Hoff].
  split.
  2: assumption.
  rewrite /get_disk_blknos.
  destruct Hblk as [b Hb].
  eapply elem_of_map_2_alt.
  1: apply elem_of_dom; apply (mk_is_Some _ _ Hb).
  rewrite /addr2flat_z /addrBlock /=.
  rewrite -Z.mul_assoc Z.div_add_l.
  2: auto.
  rewrite Zdiv_small.
  all: word.
Qed.

Definition filter_by_key {K A} `{Countable K} P `{!∀ x, Decision (P x)} (m: gmap K A) :=
  filter (λ x, P x.1) m.

Lemma filter_by_key_lookup_notin {K A} `{Countable K} P `{!∀ x, Decision (P x)} (m: gmap K A) k :
  ~ P k → filter_by_key P m !! k = None.
Proof.
  intros Hnotin.
  apply map_filter_lookup_None_2.
  right.
  intros x Hacc.
  auto.
Qed.

Lemma filter_by_key_lookup_in {K A} `{Countable K} P `{!∀ x, Decision (P x)} (m: gmap K A) k :
  P k → filter_by_key P m !! k = m !! k.
Proof.
  intros Hin.
  destruct (m !! k) as [x|x] eqn:Hlookup.
  2: {
    apply map_filter_lookup_None_2.
    auto.
  }
  apply (map_filter_lookup_Some_2 _ _ _ _ Hlookup).
  auto.
Qed.

Lemma filter_by_key_or {K A} `{Countable K} P1 P2 `{!∀ x, Decision (P1 x)} `{!∀ x, Decision (P2 x)} (m: gmap K A) :
  filter_by_key (λ k, P1 k ∨ P2 k) m =
    filter_by_key P1 m ∪ filter_by_key P2 m.
Proof.
  apply map_eq.
  intros k.
  destruct (decide (P1 k ∨ P2 k)) as [Hin|Hnotin].
  2: {
    rewrite map_filter_lookup_key_notin.
    2: assumption.
    symmetry.
    apply (iffRL (lookup_union_None _ _ _)).
    rewrite -> filter_by_key_lookup_notin by set_solver.
    rewrite -> filter_by_key_lookup_notin by set_solver.
    auto.
  }
  rewrite filter_by_key_lookup_in.
  2: apply Hin.
  symmetry.
  destruct (decide (P1 k)) as [Hin1|Hnotin1].
  2: {
    rewrite lookup_union_r.
    2: apply (filter_by_key_lookup_notin _ _ _ Hnotin1).
    apply filter_by_key_lookup_in.
    set_solver.
  }
  destruct (m !! k) as [x|x] eqn:Hlookup.
  2: {
    apply (iffRL (lookup_union_None _ _ _)).
    split; apply map_filter_lookup_None_2; auto.
  }
  erewrite lookup_union_Some_l; first by auto.
  rewrite -Hlookup.
  apply (filter_by_key_lookup_in _ _ _ Hin1).
Qed.

Definition filter_addr_map_by_blk {A} (s: gset u64) (m: gmap addr A) :=
  filter_by_key (λ a, addrBlock a ∈ s) m.

Lemma map_filter_always_false {K A M} (P : K * A → Prop) `{!∀ x, Decision (P x)} `{FinMap K M} (m: M A) :
  (∀ k x, m !! k = Some x → ¬ P (k, x)) →
  filter P m = ∅.
Proof.
  intros HP.
  apply map_empty.
  intros k.
  destruct (filter P m !! k) eqn:Hfilter_acc.
  2: reflexivity.
  pose proof (map_filter_lookup_Some_1_1 _ _ _ _ Hfilter_acc) as Hacc.
  apply HP in Hacc.
  apply map_filter_lookup_Some_1_2 in Hfilter_acc.
  contradiction.
Qed.

Lemma filter_addr_map_by_blk_nil {A} (m: gmap addr A) :
  filter_addr_map_by_blk (∅: gset u64) m = ∅.
Proof.
  eapply map_filter_always_false.
  1: apply gmap_finmap.
  set_solver.
Qed.

Lemma filter_addr_map_by_blk_union {A} (s1 s2: gset u64) (m: gmap addr A) :
  filter_addr_map_by_blk (s1 ∪ s2) m =
    filter_addr_map_by_blk s1 m ∪ filter_addr_map_by_blk s2 m.
Proof.
  rewrite -filter_by_key_or.
  apply map_filter_iff.
  set_solver.
Qed.

Lemma filter_addr_map_by_blk_lookup_in {A} (s: gset u64) (m: gmap addr A) a :
  addrBlock a ∈ s →
  filter_addr_map_by_blk s m !! a = m !! a.
Proof.
  intros Hin.
  apply filter_by_key_lookup_in.
  assumption.
Qed.

Lemma filter_addr_map_by_blk_dom_in {A} (s: gset u64) (m: gmap addr A) a :
  a ∈ dom (gset addr) (filter_addr_map_by_blk s m) →
  is_Some (m !! a) ∧ addrBlock a ∈ s.
Proof.
  intros Hin.
  apply map_filter_elem_of_dom in Hin.
  destruct Hin as [obj [Hacc Ha]].
  apply mk_is_Some in Hacc.
  simpl in Ha.
  intuition.
Qed.

Lemma gmap_addr_by_block_filter_by_blk {A} (s: gset u64) (m: gmap addr A):
  gmap_addr_by_block (filter_addr_map_by_blk s m) =
  filter (λ x, x.1 ∈ s) (gmap_addr_by_block m).
Proof.
  pose proof (gmap_addr_by_block_filter m (λ x, x ∈ s)) as Hthm.
  simpl in Hthm.
  rewrite -Hthm.
  reflexivity.
Qed.

Lemma gmap_addr_by_block_lookup_not_empty {A} (m: gmap addr A) blkno mblk :
  gmap_addr_by_block m !! blkno = Some mblk → mblk ≠ ∅.
Proof.
  intros Hacc.
  apply gmap_uncurry_non_empty in Hacc.
  assumption.
Qed.

Lemma gmap_addr_by_block_lookup_is_Some {A} (m: gmap addr A) blkno :
  is_Some (gmap_addr_by_block m !! blkno) →
  ∃ off, is_Some (m !! Build_addr blkno off).
Proof.
  intros Hin.
  destruct Hin as [offmap Hoffmap].
  pose proof (gmap_addr_by_block_lookup_not_empty _ _ _ Hoffmap) as Hnot_empty.
  apply map_choose in Hnot_empty.
  destruct Hnot_empty as [off [x Hx]].
  apply gmap_uncurry_lookup with (k2:=off) in Hoffmap.
  rewrite Hx in Hoffmap.
  apply mk_is_Some in Hoffmap.
  eexists _.
  eassumption.
Qed.

Lemma gmap_addr_by_block_to_filter {A} (m: gmap addr A) blkno mblk :
  gmap_addr_by_block m !! blkno = Some mblk →
  list_to_map ((λ x, (addrOff x.1, x.2)) <$>
    map_to_list (filter_addr_map_by_blk {[blkno]} m)
  ) = mblk.
Proof.
  intros Hacc.
  apply map_eq.
  intros off.
  apply gmap_uncurry_lookup with (k2:=off) in Hacc.
  rewrite -Hacc.
  destruct (m !! (blkno, off)) as [obj|] eqn:Hmblk_acc; rewrite Hmblk_acc.
  {
    apply elem_of_list_to_map_1.
    {
      rewrite -list_fmap_compose.
      apply NoDup_fmap_2_strong.
      2: apply NoDup_map_to_list.
      intros x1 x2 Hx1 Hx2 Hoff_eq.
      simpl in Hoff_eq.
      apply elem_of_map_to_list' in Hx1.
      apply elem_of_map_to_list' in Hx2.
      pose proof (mk_is_Some _ _ Hx1) as Hdom1.
      pose proof (mk_is_Some _ _ Hx2) as Hdom2.
      apply elem_of_dom in Hdom1.
      apply elem_of_dom in Hdom2.
      apply filter_addr_map_by_blk_dom_in in Hdom1.
      apply filter_addr_map_by_blk_dom_in in Hdom2.
      destruct Hdom1 as [_ Hdom1].
      destruct Hdom2 as [_ Hdom2].
      apply elem_of_singleton_1 in Hdom1.
      apply elem_of_singleton_1 in Hdom2.
      subst.
      assert (x1.1 = x2.1) as Haddr_eq.
      {
        destruct x1 as [a1 x1].
        destruct x2 as [a2 x2].
        destruct a1.
        destruct a2.
        simpl in Hoff_eq.
        simpl in Hdom2.
        subst.
        auto.
      }
      rewrite -Haddr_eq in Hx2.
      rewrite Hx2 in Hx1.
      inversion Hx1.
      destruct x1.
      destruct x2.
      simpl in *.
      subst.
      auto.
    }
    eapply elem_of_list_fmap_1_alt with (x:=(Build_addr blkno off, obj)).
    2: rewrite //=.
    apply elem_of_map_to_list'.
    simpl.
    rewrite filter_addr_map_by_blk_lookup_in.
    2: simpl; set_solver.
    assumption.
  }
  apply not_elem_of_list_to_map_1.
  rewrite -list_fmap_compose.
  intros Hin.
  apply elem_of_list_fmap_2 in Hin.
  destruct Hin as [x [Hoff Hin]].
  simpl in Hoff.
  subst.
  apply elem_of_map_to_list' in Hin.
  apply mk_is_Some in Hin.
  apply elem_of_dom in Hin.
  apply filter_addr_map_by_blk_dom_in in Hin.
  destruct Hin as [Hm_acc Hin].
  apply elem_of_singleton_1 in Hin.
  subst blkno.
  rewrite -surjective_pairing in Hmblk_acc.
  rewrite Hmblk_acc in Hm_acc.
  destruct Hm_acc as [y Hy].
  inversion Hy.
Qed.

Implicit Types γ : @txn_names Σ.

Definition ptsto_mapsto γ γa a : iProp Σ := (
  ∃ (v: object),
    "Hptsto" ∷ ptsto_mut γa a 1 v ∗
    "Hmapsto" ∷ mapsto_txn γ a v
)%I.

Definition linv γ metamap blkno : iProp Σ := (
  [∗ map] a ↦ γa ∈ filter_addr_map_by_blk {[blkno]} metamap, (
    ptsto_mapsto γ γa a
  )
)%I.

Lemma linv_split γ metamap blkno :
  "Hlinv" ∷ linv γ metamap blkno -∗
  ∃ (mt: gmap addr object),
    (
      let metamap_blk := filter_addr_map_by_blk {[blkno]} metamap in
      "Hptstos" ∷ [∗ map] a ↦ γa; v ∈ metamap_blk; mt, (
        "Hptsto" ∷ ptsto_mut γa a 1 v
      )
    )
      ∗
    (
      "Hmapstos" ∷ [∗ map] a ↦ v ∈ mt, (
        "Hmapsto" ∷ mapsto_txn γ a v
      )
    ).
Proof.
  iIntros.
  iNamed.
  iDestruct (big_sepM_sepM2 with "Hlinv") as (mt) "Hlinv".
  iDestruct (big_sepM2_sep with "Hlinv") as "[Hptstos Hmapstos]".
  iDestruct (big_sepM2_sepM_2 with "Hmapstos") as "Hmapstos".
  iDestruct (big_sepM_mono _ (λ k x, "Hmapsto" ∷ mapsto_txn γ k x)
    with "Hmapstos") as "Hmapstos".
  {
    iIntros (k x _) "Φ".
    iDestruct "Φ" as (x') "[_ Φ]".
    iAssumption.
  }
  iExists _.
  iFrame.
Qed.

Definition obj_to_vobj (v: object): versioned_object :=
  existT (projT1 v) (projT2 v, projT2 v).

Lemma linv_lift E buftxnl mt_buftxn γ dinit anydirty metamap blkno:
  ↑invN ⊆ E →
  (
    "Hbuftxn" ∷ is_buftxn buftxnl mt_buftxn γ dinit anydirty ∗
    "Hlinv" ∷ linv γ metamap blkno
  )
    -∗ |NC={E}=>
  (
    ∃ mt_new,
      "Hbuftxn" ∷ is_buftxn buftxnl ((obj_to_vobj <$> mt_new) ∪ mt_buftxn) γ dinit anydirty ∗
      "Hptstos" ∷ [∗ map] a ↦ γa; v ∈ filter_addr_map_by_blk {[blkno]} metamap; mt_new, (
        "Hptsto" ∷ ptsto_mut γa a 1 v
      )
  ).
Proof.
  simpl.
  intros Hinv.
  iIntros "(?&?)".
  iNamed.
  iDestruct (linv_split with "Hlinv") as (mt_new) "(?&?)".
  iNamed.
  iExists mt_new.
  rewrite /obj_to_vobj.
  iDestruct (BufTxn_lift _ _ _ _ _ _ _ Hinv with "[$Hbuftxn $Hmapstos]")
    as "> Hbuftxn".
  iFrame.
  auto.
Qed.

Definition is_twophase_inner (l : loc) mt_buftxn (locks_held: list u64) γ (dinit: disk) metamap : iProp Σ := (
  ∃ (buftxnl locksl: loc) acquired_s anydirty ghs,
    let dinit_blknos := get_disk_blknos dinit in
    let mt_buftxn_blknos := get_addr_map_blknos mt_buftxn in
    let metamap_blknos := get_addr_map_blknos metamap in
    let locked_blknos: gset u64 := list_to_set locks_held in
    let metamap_in_mt := filter_addr_map_by_blk mt_buftxn_blknos metamap in
    "Htwophase.buftxn" ∷ l ↦[TwoPhase.S :: "buftxn"] #buftxnl ∗
    "Htwophase.locks" ∷ l ↦[TwoPhase.S :: "locks"] #locksl ∗
    "Htwophase.acquired" ∷ l ↦[TwoPhase.S :: "acquired"] (slice_val acquired_s) ∗
    "Hbuftxn" ∷ is_buftxn buftxnl mt_buftxn γ dinit anydirty ∗
    "#Hlocks" ∷ is_lockMap locksl ghs dinit_blknos (linv γ metamap) ∗
    "Hacquired_s" ∷ is_slice acquired_s uint64T 1 locks_held ∗
    "Hlocked_blknos" ∷ ([∗ set] blkno ∈ locked_blknos,
      "Hlocked" ∷ Locked ghs blkno
    ) ∗
    "Hptstos" ∷ ([∗ map] a ↦ γa; vo ∈ metamap_in_mt; mt_buftxn, (
      "Hptsto" ∷ ptsto_mut γa a 1 (committed vo)
    )) ∗
    "%Hmt_buftxn_blknos_locked" ∷ ⌜mt_buftxn_blknos ⊆ locked_blknos⌝ ∗
    "%Hlocked_blknos_wf" ∷ ⌜locked_blknos ⊆ dinit_blknos⌝ ∗
    "%Hmetamap_blknos_wf" ∷ ⌜metamap_blknos ⊆ dinit_blknos⌝ ∗
    "%Hlocks_held_NoDup" ∷ ⌜NoDup locks_held⌝
)%I.

Definition is_twophase (l : loc) mt_buftxn γ (dinit: disk) metamap : iProp Σ := (
  ∃ locks_held,
    "%Hlocks_held" ∷ ⌜list_to_set locks_held = get_addr_map_blknos mt_buftxn⌝ ∗
    "Htwophase" ∷ is_twophase_inner l mt_buftxn locks_held γ dinit metamap
)%I.

Ltac wp_start :=
  iIntros (Φ) "Hpre HΦ";
  lazymatch goal with
  | |- context[Esnoc _ (INamed "HΦ") (▷ ?Q)%I] =>
    set (post:=Q)
  end;
  lazymatch iTypeOf "Hpre" with
  | Some (_, named _ _ ∗ _)%I => iNamed "Hpre"
  | Some (_, named _ _)%I => iNamed "Hpre"
  | _ => idtac
  end.

Lemma get_addr_map_blknos_nil {A} :
  get_addr_map_blknos (∅: gmap addr A) = ∅.
Proof.
  set_solver.
Qed.

Theorem wp_twophase_Begin (txnl locksl: loc) γ dinit ghs γmap qmap metamap:
  {{{
    "Htxn" ∷ invariant.is_txn txnl γ dinit ∗
    "#Hlocks" ∷ is_lockMap locksl ghs (get_disk_blknos dinit) (linv γ metamap)
  }}}
    Begin #txnl #locksl
  {{{
    (l : loc), RET #l;
    "%Hmetamap_blknos_wf" ∷ ⌜get_addr_map_blknos metamap ⊆ get_disk_blknos dinit⌝ -∗
    "Hmetamap_ctx" ∷ map_ctx γmap qmap metamap -∗
    "Htwophase" ∷ is_twophase l ∅ γ dinit metamap
  }}}.
Proof.
  wp_start.
  wp_call.
  wp_apply (wp_buftxn_Begin with "Htxn").
  iIntros (buftxnl) "Hbuftxn".
  wp_apply (wp_NewSlice _ _ uint64T).
  iIntros (acquired_s) "Hacquired_s".
  wp_apply wp_allocStruct; first by auto.
  iIntros (l) "Hl".
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_pures.
  iApply "HΦ".
  iDestruct (struct_fields_split with "Hl") as "(Htwophase.buftxn & Htwophase.locks & Htwophase.acquired & %)".
  iIntros "? ?".
  iNamed.
  iExists [].
  iSplit; first by rewrite get_addr_map_blknos_nil //=.
  iExists _, _, _, _, _.
  rewrite list_to_set_nil get_addr_map_blknos_nil filter_addr_map_by_blk_nil.
  iFrame "∗ # %".
  iSplit; first by auto.
  iSplit; first by auto.
  iPureIntro.
  split; first by auto.
  split; first by set_solver.
  apply NoDup_nil_2.
Qed.

Lemma set_union_empty_r {A} `{Countable A} (s: gset A) :
  s ∪ ∅ = s.
Proof.
  pose proof (iffRL (elem_of_equiv (s ∪ ∅) s)) as equiv_thm.
  apply leibniz_equiv.
  apply (iffRL (elem_of_equiv (s ∪ ∅) s)).
  set_solver.
Qed.

Lemma map_zip_fst {K A B} `{Countable K} (m1: gmap K A) (m2: gmap K B) :
  dom (gset K) m1 = dom (gset K) m2 →
  fst <$> (map_zip m1 m2) = m1.
Proof.
  intros Hdom.
  apply map_eq.
  intros k.
  rewrite lookup_fmap.
  destruct (m1 !! k) as [x|] eqn:Hacc.
  2: rewrite (map_zip_lookup_none_1 _ _ _ Hacc) //.
  pose proof ((iffRL (elem_of_dom _ _)) (mk_is_Some _ _ Hacc)) as Hkin.
  rewrite Hdom in Hkin.
  apply elem_of_dom in Hkin.
  destruct Hkin as [x2 Hx2].
  rewrite (map_zip_lookup_some _ _ _ _ _ Hacc Hx2).
  auto.
Qed.

Lemma map_zip_snd {K A B} `{Countable K} (m1: gmap K A) (m2: gmap K B) :
  dom (gset K) m1 = dom (gset K) m2 →
  snd <$> (map_zip m1 m2) = m2.
Proof.
  intros Hdom.
  apply map_eq.
  intros k.
  rewrite lookup_fmap.
  destruct (m2 !! k) as [x|] eqn:Hacc.
  2: rewrite (map_zip_lookup_none_2 _ _ _ Hacc) //.
  pose proof ((iffRL (elem_of_dom _ _)) (mk_is_Some _ _ Hacc)) as Hkin.
  rewrite -Hdom in Hkin.
  apply elem_of_dom in Hkin.
  destruct Hkin as [x1 Hx1].
  rewrite (map_zip_lookup_some _ _ _ _ _ Hx1 Hacc).
  auto.
Qed.

Lemma map_zip_lookup_some' {K A B} `{Countable K} (m1: gmap K A) (m2: gmap K B) k x1 x2 :
  map_zip m1 m2 !! k = Some (x1, x2) →
  m1 !! k = Some x1 ∧ m2 !! k = Some x2.
Proof.
  intros Hin.
  rewrite /map_zip /map_zip_with in Hin.
  erewrite lookup_merge in Hin.
  2: rewrite /DiagNone //.
  destruct (m1 !! k) as [x1'|] eqn:Hx1.
  2: inversion Hin.
  destruct (m2 !! k) as [x2'|] eqn:Hx2.
  2: inversion Hin.
  inversion Hin.
  subst.
  auto.
Qed.

Lemma map_zip_dom {K A B} `{Countable K} (m1: gmap K A) (m2: gmap K B) :
  dom (gset K) (map_zip m1 m2) = dom (gset K) m1 ∩ dom (gset K) m2.
Proof.
  apply gset.gset_eq.
  intros k.
  split.
  - intros Hin.
    apply elem_of_dom in Hin.
    destruct Hin as (x&Hin).
    destruct x as (x1&x2).
    apply map_zip_lookup_some' in Hin.
    apply elem_of_intersection.
    destruct Hin as [Hin1 Hin2].
    split; apply elem_of_dom; eexists _; eassumption.
  - intros Hin.
    apply elem_of_intersection in Hin.
    destruct Hin as [Hin1 Hin2].
    apply elem_of_dom.
    apply elem_of_dom in Hin1.
    apply elem_of_dom in Hin2.
    destruct Hin1 as [x1 Hin1].
    destruct Hin2 as [x2 Hin2].
    eexists _.
    apply map_zip_lookup_some; eassumption.
Qed.

Lemma map_zip_same_dom_union {K A B} `{Countable K} (m11 m21: gmap K A) (m12 m22: gmap K B) :
  dom (gset K) m11 = dom (gset K) m12 →
  dom (gset K) m21 = dom (gset K) m22 →
  (map_zip m11 m12) ∪ (map_zip m21 m22) = map_zip (m11 ∪ m21) (m12 ∪ m22).
Proof.
  intros Hdom1 Hdom2.
  apply map_eq.
  intros k.
  destruct ((m11 ∪ m21) !! k) as [x1|] eqn:Hx1.
  2: {
    rewrite (map_zip_lookup_none_1 _ _ _ Hx1).
    apply lookup_union_None.
    apply lookup_union_None in Hx1.
    rewrite -> map_zip_lookup_none_1 by intuition.
    rewrite -> map_zip_lookup_none_1 by intuition.
    auto.
  }
  destruct ((m12 ∪ m22) !! k) as [x2|] eqn:Hx2.
  2: {
    rewrite (map_zip_lookup_none_2 _ _ _ Hx2).
    apply lookup_union_None.
    apply lookup_union_None in Hx2.
    rewrite -> map_zip_lookup_none_2 by intuition.
    rewrite -> map_zip_lookup_none_2 by intuition.
    auto.
  }
  rewrite (map_zip_lookup_some _ _ _ _ _ Hx1 Hx2).
  apply lookup_union_Some_raw in Hx1.
  destruct Hx1 as [Hx11|[Hx1_None Hx1]].
  - pose proof (elem_of_dom_2 _ _ _ Hx11) as Hin11.
    rewrite Hdom1 in Hin11.
    apply elem_of_dom in Hin11.
    destruct Hin11 as [x12 Hx12].
    rewrite (lookup_union_Some_l _ _ _ _ Hx12) in Hx2.
    inversion Hx2.
    subst.
    erewrite lookup_union_Some_l.
    2: apply map_zip_lookup_some; eassumption.
    auto.
  - rewrite lookup_union_r in Hx2.
    2: {
      apply not_elem_of_dom.
      rewrite -Hdom1.
      apply not_elem_of_dom.
      assumption.
    }
    rewrite lookup_union_r.
    2: {
      apply map_zip_lookup_none_1.
      apply Hx1_None.
    }
    apply map_zip_lookup_some; eassumption.
Qed.

Lemma big_sepM2_same_to_sepM {K A} `{Countable K} (m: gmap K A) (Φ: K → A → A → iProp Σ) :
  ([∗ map] k ↦ x1; x2 ∈ m; m, Φ k x1 x2)%I ≡
  ([∗ map] k ↦ x ∈ m, Φ k x x)%I.
Proof.
  iSplit.
  - iIntros "Hsep".
    iApply big_sepM2_sepM_1 in "Hsep".
    iApply big_sepM_mono in "Hsep".
    2: iFrame.
    iIntros (k x Hacc) "Φ".
    iDestruct "Φ" as (x') "[%Hacc' Φ]".
    rewrite Hacc' in Hacc.
    inversion Hacc.
    subst x'.
    iFrame.
  - iIntros "Hsep".
    iAssert ([∗ map] k↦x ∈ m, True)%I as "Hsep'".
    1: auto.
    iDestruct (big_sepM_sepM2_merge with "[$Hsep $Hsep']") as "Hsep".
    1: reflexivity.
    iApply big_sepM2_mono.
    2: iFrame.
    iIntros (k x1 x2 Hacc1 Hacc2) "H".
    rewrite Hacc2 in Hacc1.
    inversion Hacc1.
    subst x2.
    iDestruct "H" as "[H _]".
    iFrame.
Qed.

Lemma big_sepM_zip_sepM2_equiv {K A B} `{Countable K} (m1: gmap K A) (m2: gmap K B) (Φ: K → A → B → iProp Σ) :
  dom (gset K) m1 = dom (gset K) m2 →
  ([∗ map] k ↦ x ∈ map_zip m1 m2, Φ k x.1 x.2)%I ≡
  ([∗ map] k ↦ x1; x2 ∈ m1; m2, Φ k x1 x2)%I.
Proof.
  iIntros (Hdom).
  replace ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2)%I
    with (
      let m1' := fst <$> map_zip m1 m2 in
      let m2' := snd <$> map_zip m1 m2 in
      [∗ map] k↦x1;x2 ∈ m1';m2', Φ k x1 x2
    )%I
    by rewrite /= (map_zip_fst _ _ Hdom) (map_zip_snd _ _ Hdom) //.
  rewrite /= big_sepM2_fmap_l big_sepM2_fmap_r big_sepM2_same_to_sepM //.
Qed.

Lemma big_sepM_zip_to_sepM2 {K A B} `{Countable K} (m1: gmap K A) (m2: gmap K B) (Φ: K → (A * B) → iProp Σ) :
  dom (gset K) m1 = dom (gset K) m2 →
  ([∗ map] k ↦ x ∈ map_zip m1 m2, Φ k x)%I -∗
  ([∗ map] k ↦ x1; x2 ∈ m1; m2, Φ k (x1, x2))%I.
Proof.
  iIntros (Hdom) "Hsep".
  iApply (big_sepM_zip_sepM2_equiv _ _ _ Hdom).
  iApply big_sepM_mono.
  2: iFrame.
  iIntros (k x _) "HΦ".
  rewrite -surjective_pairing.
  iFrame.
Qed.

Lemma big_sepM2_to_sepM_zip {K A B} `{Countable K} (m1: gmap K A) (m2: gmap K B) (Φ: K → A → B → iProp Σ) :
  ([∗ map] k ↦ x1; x2 ∈ m1; m2, Φ k x1 x2)%I -∗
  ([∗ map] k ↦ x ∈ map_zip m1 m2, Φ k x.1 x.2)%I.
Proof.
  iIntros "Hsep".
  iDestruct (big_sepM2_dom with "Hsep") as "%Hdom".
  rewrite -big_sepM_zip_sepM2_equiv //.
Qed.

Lemma set_union_comm {A} `{Countable A} (s1 s2: gset A) :
  s1 ∪ s2 = s2 ∪ s1.
Proof.
  set_solver.
Qed.

Lemma map_disjoint_comm {K A} `{Countable K} (m1 m2: gmap K A) :
  m1 ##ₘ m2 → m2 ##ₘ m1.
Proof.
  set_solver.
Qed.

Theorem wp_twophase__acquireNoCheck (l: loc) mt_buftxn γ dinit metamap (blkno: u64):
  {{{
    "Htwophase" ∷ is_twophase l mt_buftxn γ dinit metamap ∗
    "%Hblkno_wf" ∷ ⌜blkno ∈ get_disk_blknos dinit⌝ ∗
    "%Hblkno_in_metamap" ∷ ⌜blkno ∈ get_addr_map_blknos metamap⌝ ∗
    "%Hblkno_not_locked" ∷ ⌜blkno ∉ get_addr_map_blknos mt_buftxn⌝
  }}}
    TwoPhase__acquireNoCheck #l #blkno
  {{{
    RET #();
    ∃ mt_buftxn',
      "%Hmt_buftxn'_blknos" ∷ ⌜
        get_addr_map_blknos mt_buftxn' =
        get_addr_map_blknos mt_buftxn ∪ {[blkno]}
      ⌝ ∗
      "Htwophase" ∷ is_twophase l mt_buftxn' γ dinit metamap
  }}}.
Proof.
  wp_start.
  wp_call.
  iNamed "Htwophase".
  iNamed "Htwophase".
  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hlocks]").
  1: iPureIntro; assumption.
  iIntros "[Hlinv Hlocked]".
  iNamed "Hlinv".

  iDestruct (linv_lift with "[$Hbuftxn $Hlinv]") as "> Hlinv".
  1: auto.
  iDestruct "Hlinv" as (?) "[? Hptstos_new]".
  iDestruct (from_named with "Hptstos_new") as "Hptstos_new".
  iNamed.
  replace ([∗ map] a↦γa;v ∈ _;mt_new, _)%I
    with ([∗ map] a↦γa;v ∈
      filter_addr_map_by_blk {[blkno]} metamap;
      committed <$> (obj_to_vobj <$> mt_new),
        "Hptsto" ∷ a [[γa]]↦ v
    )%I.
  2: {
    f_equal.
    rewrite -map_fmap_compose.
    rewrite (map_fmap_ext _ id).
    1: rewrite map_fmap_id //.
    intros _ x _.
    destruct x.
    rewrite /obj_to_vobj /committed //=.
  }
  rewrite big_sepM2_fmap_r.
  iDestruct (big_sepM2_dom with "Hptstos") as "%Hptstos_dom".
  iDestruct (big_sepM2_dom with "Hptstos_new") as "%Hptstos_new_dom".
  rewrite big_sepM2_to_sepM_zip big_sepM2_to_sepM_zip.
  assert (mt_buftxn ##ₘ (obj_to_vobj <$> mt_new)) as Hdisj.
  {
    apply map_disjoint_dom_2.
    rewrite -Hptstos_dom -Hptstos_new_dom.
    apply map_disjoint_dom_1.
    apply map_disjoint_alt.
    intros k.
    destruct (decide (addrBlock k = blkno)) as [Hk_blk|Hk_blk].
    - left.
      apply filter_by_key_lookup_notin.
      rewrite Hk_blk.
      set_solver.
    - right.
      apply filter_by_key_lookup_notin.
      set_solver.
  }
  rewrite (map_union_comm _ _ (map_disjoint_comm _ _ Hdisj)).
  unshelve (iDestruct ((equiv_entails_sym _ _ (big_sepM_union _ _ _ _)) with "[$Hptstos $Hptstos_new]") as "Hptstos").
  {
    apply map_disjoint_dom_2.
    rewrite map_zip_dom map_zip_dom Hptstos_dom Hptstos_new_dom.
    rewrite -> subseteq_intersection_1 by set_solver.
    rewrite -> subseteq_intersection_1 by set_solver.
    apply map_disjoint_dom_1.
    apply Hdisj.
  }
  rewrite (map_zip_same_dom_union _ _ _ _ Hptstos_dom Hptstos_new_dom).
  iDestruct (big_sepM_zip_to_sepM2 with "Hptstos") as "Hptstos".
  1: rewrite dom_union_L dom_union_L Hptstos_dom Hptstos_new_dom //.
  rewrite -filter_addr_map_by_blk_union /=.
  assert (
    get_addr_map_blknos (obj_to_vobj <$> mt_new) = {[blkno]}
  ) as Hmt_new_blknos.
  {
    rewrite /get_addr_map_blknos.
    eapply elem_of_equiv_L.
    intros blkno'.
    split.
    - intros Hin.
      apply elem_of_dom in Hin.
      apply gmap_addr_by_block_lookup_is_Some in Hin.
      destruct Hin as [off Hin].
      apply elem_of_dom in Hin.
      rewrite -Hptstos_new_dom in Hin.
      apply filter_addr_map_by_blk_dom_in in Hin.
      destruct Hin as [_ Hin].
      simpl in Hin.
      assumption.
    - intros Hin.
      apply elem_of_singleton_1 in Hin.
      subst blkno.
      rewrite -(gmap_addr_by_block_dom_eq Hptstos_new_dom)
        gmap_addr_by_block_filter_by_blk.
      apply map_filter_elem_of_dom.
      rewrite /get_addr_map_blknos in Hblkno_in_metamap.
      apply elem_of_dom in Hblkno_in_metamap.
      destruct Hblkno_in_metamap as [metamap_blk Hmetamap_blk].
      eexists _.
      split; first by eassumption.
      simpl.
      set_solver.
  }
  assert (
    get_addr_map_blknos (mt_buftxn ∪ (obj_to_vobj <$> mt_new))
      =
    list_to_set locks_held ∪ {[blkno]}
  ) as Hlocked_blknos'.
  {
    rewrite /get_addr_map_blknos gmap_addr_by_block_dom_union.
    f_equal.
    1: rewrite Hlocks_held //.
    apply Hmt_new_blknos.
  }
  rewrite -Hmt_new_blknos.
  rewrite -gmap_addr_by_block_dom_union.

  wp_loadField.
  wp_apply (wp_SliceAppend (V:=u64) with "[$Hacquired_s]").
  iIntros (acquired_s') "Hacquired_s".
  wp_apply (wp_storeField with "Htwophase.acquired").
  1: rewrite /field_ty /=; val_ty.
  iIntros "Htwophase.acquired".
  iApply "HΦ".

  iExists _.
  iSplit.
  2: {
    iExists _.
    iSplit.
    2: {
      iExists _, _, _, _, _.
      iFrame (Hmetamap_blknos_wf) "∗ #".
      rewrite list_to_set_app_L /= set_union_empty_r.
      iSplitL "Hlocked_blknos Hlocked".
      {
        rewrite set_union_comm big_sepS_insert.
        1: iFrame.
        rewrite Hlocks_held.
        assumption.
      }
      iPureIntro.
      split.
      {
        rewrite -Hlocked_blknos'.
        set_solver.
      }
      split.
      {
        apply union_least.
        1: assumption.
        apply elem_of_subseteq_singleton.
        assumption.
      }
      apply NoDup_app.
      split; first by assumption.
      split.
      2: apply NoDup_singleton.
      intros blkno' Hin His.
      apply elem_of_list_singleton in His.
      subst blkno.
      apply (iffRL (@elem_of_list_to_set _ (gset u64) _ _ _ _ _ _ _)) in Hin.
      rewrite Hlocks_held in Hin.
      contradiction.
    }
    iPureIntro.
    rewrite list_to_set_app_L /= set_union_empty_r.
    symmetry.
    apply Hlocked_blknos'.
  }
  iPureIntro.
  rewrite Hlocked_blknos' Hlocks_held //.
Qed.

Theorem wp_twophase__Acquire (l: loc) mt_buftxn γ dinit metamap (blkno: u64):
  {{{
    "Htwophase" ∷ is_twophase l mt_buftxn γ dinit metamap ∗
    "%Hblkno_wf" ∷ ⌜blkno ∈ get_disk_blknos dinit⌝ ∗
    "%Hblkno_in_metamap" ∷ ⌜blkno ∈ get_addr_map_blknos metamap⌝
  }}}
    TwoPhase__Acquire #l #blkno
  {{{
    RET #();
    ∃ mt_buftxn',
      "%Hmt_buftxn'_blknos" ∷ ⌜
        get_addr_map_blknos mt_buftxn' =
        get_addr_map_blknos mt_buftxn ∪ {[blkno]}
      ⌝ ∗
      "Htwophase" ∷ is_twophase l mt_buftxn' γ dinit metamap
  }}}.
Proof.
  wp_start.
  wp_call.
  wp_apply wp_ref_to; first by auto.
  iIntros (already_acquired_l) "Halready_acquired_l".
  iNamed "Htwophase".
  iNamed "Htwophase".
  wp_loadField.
  iDestruct (is_slice_small_read with "Hacquired_s") as "[Hacquired_s Hacquired_s_wrap]".
  wp_apply (wp_forSlicePrefix (λ done todo,
    let already_acquired_val := bool_decide (blkno ∈ done) in
    "Halready_acquired_l" ∷ already_acquired_l ↦[boolT] #already_acquired_val
  )%I (V:=u64) with "[] [$Hacquired_s Halready_acquired_l]").
  2: {
    rewrite bool_decide_eq_false_2; first by iFrame.
    apply not_elem_of_nil.
  }
  {
    iIntros (i x done todo Harr Φ0).
    iModIntro.
    iNamed 1.
    iIntros "HΦ".
    wp_if_destruct.
    {
      wp_apply (wp_StoreAt with "[$Halready_acquired_l]").
      1: auto.
      iIntros "Halready_acquired_l".
      iApply "HΦ".
      rewrite bool_decide_eq_true_2; first by iFrame.
      apply elem_of_app.
      right.
      apply (iffRL (elem_of_list_singleton _ _)).
      reflexivity.
    }
    iApply "HΦ".
    destruct (decide (blkno ∈ done)).
    - rewrite bool_decide_eq_true_2.
      2: assumption.
      rewrite bool_decide_eq_true_2; first by iFrame.
      apply elem_of_app.
      left.
      assumption.
    - rewrite bool_decide_eq_false_2.
      2: assumption.
      rewrite bool_decide_eq_false_2; first by iFrame.
      apply not_elem_of_app.
      split; first by assumption.
      intro Hin.
      apply elem_of_list_singleton in Hin.
      apply Heqb.
      f_equal.
      f_equal.
      apply Hin.
  }
  iIntros "[Hacquired_s ?]".
  iNamed.
  iApply "Hacquired_s_wrap" in "Hacquired_s".
  wp_apply (wp_LoadAt with "[$Halready_acquired_l]").
  iIntros "Halready_acquired_l".
  wp_if_destruct.
  2: {
    iApply "HΦ".
    iExists mt_buftxn.
    apply (@elem_of_list_to_set _ (gset u64) _ _ _ _ _) in Heqb.
    rewrite Hlocks_held in Heqb.
    iSplit; first by (iPureIntro; set_solver).
    iExists locks_held.
    iSplit; first by (iPureIntro; assumption).
    iExists _, _, _, _, _.
    iFrame "∗ # %".
  }
  rewrite bool_decide_eq_false_2.
  2: assumption.
  wp_apply (wp_twophase__acquireNoCheck with "[
    Htwophase.buftxn Htwophase.locks Htwophase.acquired
    Hbuftxn Hlocked_blknos Hptstos Hacquired_s
  ]").
  {
    apply (@not_elem_of_list_to_set _ (gset u64) _ _ _ _ _) in Heqb.
    rewrite Hlocks_held in Heqb.
    iFrame (Hblkno_wf Hblkno_in_metamap Heqb).
    iExists locks_held.
    iSplit; first by (iPureIntro; assumption).
    iExists _, _, _, _, _.
    iFrame "∗ # %".
  }
  iIntros "Hpost".
  iNamed "Hpost".
  iApply "HΦ".
  iExists _.
  iFrame (Hmt_buftxn'_blknos) "∗".
Qed.

Theorem wp_twophase__Release (l: loc) locked_blknos blkno γ dinit metamap:
  {{{
    "Htwophase" ∷ is_twophase_inner l ∅ (locked_blknos ++ [blkno]) γ dinit metamap ∗
    "Hlinv" ∷ linv γ metamap blkno
  }}}
    TwoPhase__Release #l
  {{{
    RET #();
    is_twophase_inner l ∅ locked_blknos γ dinit metamap
  }}}.
Proof.
  wp_start.
  wp_call.
  iNamed "Htwophase".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_loadField.
  iDestruct (is_slice_small_read with "Hacquired_s") as "[Hacquired_s Hacquired_s_wrap]".
  iDestruct (is_slice_small_sz with "Hacquired_s") as "%Hacquired_s_sz".
  assert ((locked_blknos ++ [blkno]) !! (length locked_blknos) = Some blkno) as Hlocked_blknos_acc.
  {
    rewrite -> lookup_app_r by lia.
    rewrite Nat.sub_diag //.
  }
  rewrite app_length /= in Hacquired_s_sz.
  assert (int.nat acquired_s.(Slice.sz) > 0) as Hacquired_s_sz_gt by lia.
  wp_apply (wp_SliceGet (V:=u64) with "[$Hacquired_s]").
  {
    iPureIntro.
    replace (int.nat (word.sub _ 1)) with ((int.nat acquired_s.(Slice.sz)) - 1)%nat by word.
    rewrite -Hacquired_s_sz Nat.add_sub.
    apply Hlocked_blknos_acc.
  }
  iIntros "Hacquired_s".
  wp_loadField.
  rewrite list_to_set_app_L.
  iDestruct (big_sepS_union with "Hlocked_blknos") as "[Hlocked_blknos Hlocked]".
  {
    (* this can be a lemma *)
    apply NoDup_app in Hlocks_held_NoDup.
    destruct Hlocks_held_NoDup as (_ & Hdisj & _).
    apply elem_of_disjoint.
    intros x.
    intros Hin1 Hin2.
    apply elem_of_list_to_set in Hin1.
    apply elem_of_list_to_set in Hin2.
    apply Hdisj in Hin1.
    contradiction.
  }
  rewrite /= set_union_empty_r big_sepS_singleton.
  wp_apply (wp_LockMap__Release with "[$Hlocks $Hlocked $Hlinv]").
  wp_loadField.
  wp_apply (wp_SliceTake uint64T).
  1: word.
  wp_apply (wp_storeField with "Htwophase.acquired").
  1: rewrite /field_ty /=; val_ty.
  iIntros "Htwophase.acquired".
  iApply "HΦ".
  iExists _, _, _, _, _.
  iApply "Hacquired_s_wrap" in "Hacquired_s".
  iFrame "∗ #".
  iSplitL "Hacquired_s".
  {
    iApply (is_slice_take_cap _ _ _ (word.sub acquired_s.(Slice.sz) 1)) in "Hacquired_s".
    1: rewrite fmap_length app_length /=; word.
    replace (int.nat (word.sub _ 1)) with ((int.nat acquired_s.(Slice.sz)) - 1)%nat by word.
    rewrite -fmap_take -Hacquired_s_sz Nat.add_sub take_app.
    iFrame.
  }
  iPureIntro.
  rewrite get_addr_map_blknos_nil.
  split; first by set_solver.
  split; first by set_solver.
  split; first by assumption.
  apply NoDup_app in Hlocks_held_NoDup.
  intuition.
Qed.

Theorem wp_twophase__ReleaseAll (l: loc) locked_blknos γ dinit metamap:
  {{{
    "Htwophase" ∷ is_twophase_inner l ∅ locked_blknos γ dinit metamap ∗
    "Hlinvs" ∷ [∗ list] blkno ∈ locked_blknos, (
      "Hlinv" ∷ linv γ metamap blkno
    )
  }}}
    TwoPhase__ReleaseAll #l
  {{{
    RET #();
    is_twophase_inner l ∅ [] γ dinit metamap
  }}}.
Proof.
  wp_start.
  wp_call.
  wp_apply (wp_forBreak_cond (λ b,
    ∃ locked_blknos',
      "Htwophase" ∷ is_twophase_inner l ∅ locked_blknos' γ dinit metamap ∗
      "Hlinvs" ∷ ([∗ list] blkno ∈ locked_blknos', (
        "Hlinv" ∷ linv γ metamap blkno
      )) ∗
      "%Hb" ∷ ⌜b = false → locked_blknos' = []⌝
  )%I with "[] [Htwophase Hlinvs]").
  2: {
    iExists (locked_blknos).
    iFrame.
    auto.
  }
  {
    iModIntro.
    iIntros (Φ') "Hloop HΦ'".
    clear locked_blknos.
    iDestruct "Hloop" as (locked_blknos) "(?&?&?)".
    iNamed.
    iNamed "Htwophase".
    wp_loadField.
    wp_apply wp_slice_len.
    iDestruct (is_slice_sz with "Hacquired_s") as "%Hlocked_blknos_len".
    wp_if_destruct.
    2: {
      iApply "HΦ'".
      iExists locked_blknos.
      rewrite Heqb in Hlocked_blknos_len.
      replace (int.nat 0) with 0%nat in Hlocked_blknos_len by word.
      apply nil_length_inv in Hlocked_blknos_len.
      subst locked_blknos.
      iSplitL.
      2: auto.
      iExists _, _, _, _, _.
      iFrame "∗ #".
      rewrite get_addr_map_blknos_nil list_to_set_nil.
      iPureIntro.
      split; first by set_solver.
      split; first by set_solver.
      split; first by assumption.
      apply NoDup_nil_2.
    }
    iAssert (is_twophase_inner l ∅ locked_blknos γ dinit metamap) with
      "[Htwophase.buftxn Htwophase.locks Htwophase.acquired
      Hbuftxn Hacquired_s Hlocked_blknos Hptstos]"
    as "Htwophase".
    {
      iExists _, _, _, _, _.
      iFrame "∗ # %".
    }
    apply u64_val_ne in Heqb.
    replace (int.Z 0) with 0 in Heqb by word.
    assert (int.nat acquired_s.(Slice.sz) ≠ 0%nat) as Hacquired_s_sz by word.
    rewrite -Hlocked_blknos_len in Hacquired_s_sz.
    assert (0 < length locked_blknos)%nat as Hlocked_blknos by lia.
    apply length_nonzero_neq_nil in Hlocked_blknos.
    apply exists_last in Hlocked_blknos.
    destruct Hlocked_blknos as (locked_blknos'&locked_tail&->).
    iDestruct (big_sepL_app with "Hlinvs") as "[Hlinvs Hlinv]".
    iDestruct (big_sepL_cons with "Hlinv") as "[? _]".
    iNamed.
    wp_apply (wp_twophase__Release with "[$Htwophase $Hlinv]").
    iIntros "Htwophase".
    wp_pures.
    iApply "HΦ'".
    iExists _.
    iFrame.
    auto.
  }
  iIntros "Hloop".
  clear locked_blknos.
  iDestruct "Hloop" as (locked_blknos) "(?&?&?)".
  iNamed.
  pose proof (Hb eq_refl) as Hlocked_blknos.
  subst.
  iApply "HΦ".
  iFrame.
Qed.
