From RecordUpdate Require Import RecordSet.
From Perennial.algebra Require Import deletable_heap.
From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.goose_nfsd Require Import twophase.
From Perennial.program_proof Require Import buftxn.sep_buftxn_proof.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof txn.txn_proof.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.Helpers Require Import PropRestore.
From Perennial.algebra Require Import auth_map.
From Perennial.program_logic Require Import na_crash_inv.

Context `{!buftxnG Σ}.
Context `{!heapG Σ}.
Definition Nbuftxn := nroot .@ "buftxn".

Definition get_addr_set_blknos (s: gset addr): gset u64 :=
  set_map addrBlock s.

Definition get_addr_map_blknos {A} (m: gmap addr A): gset u64 :=
  set_map addrBlock (dom (gset addr) m).

Definition get_disk_blknos (d: disk): gset u64 :=
  set_map (λ x, U64 (x / (block_bytes * 8))) (dom (gset Z) d).

Lemma get_addr_map_blknos_nil {A} :
  get_addr_map_blknos (∅: gmap addr A) = ∅.
Proof.
  set_solver.
Qed.

Definition addr_wf (dinit: disk) a :=
  is_Some (dinit !! (addr2flat_z a)) ∧ int.nat (addrOff a) < block_bytes * 8.

Definition addr_wf' (dinit: disk) a :=
  (addrBlock a) ∈ get_disk_blknos dinit ∧ int.nat (addrOff a) < block_bytes * 8.

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

Section map_filter.
  Context {K A} (P : K * A → Prop) `{!∀ x, Decision (P x)}.

  Lemma map_filter_always_false `{FinMap K M} (m: M A) :
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

  Lemma map_filter_always_true `{FinMap K M} (m: M A) :
    (∀ k x, m !! k = Some x → P (k, x)) →
    filter P m = m.
  Proof.
    intros HP.
    apply map_eq.
    intros k.
    destruct (m !! k) as [v|] eqn:Hacc.
    2: apply map_filter_lookup_None_2; intuition.
    apply map_filter_lookup_Some_2; intuition.
  Qed.

  Lemma map_filter_Forall_false `{FinMap K M} (m: M A) :
    map_Forall (λ k x, ¬ P (k, x)) m →
    filter P m = ∅.
  Proof.
    eapply map_filter_always_false.
  Qed.
End map_filter.

Definition filter_by_key `{FinMap K M} (Pk: K → Prop) `{!∀ k, Decision (Pk k)} {A} (m: M A) :=
  filter (λ x, Pk x.1) m.

Section map_filter_by_key.
  Context `{FinMap K M}.
  Implicit Types (Pk: K → Prop).
  Context `{!∀ k, Decision (Pk k)}.
  Context {A} (m: M A).

  Lemma filter_by_key_lookup_notin k :
    ¬ Pk k → filter_by_key Pk m !! k = None.
  Proof.
    intros Hnotin.
    apply map_filter_lookup_None_2.
    right.
    intros x Hacc.
    auto.
  Qed.

  Lemma filter_by_key_lookup_in k :
    Pk k → filter_by_key Pk m !! k = m !! k.
  Proof.
    intros Hin.
    destruct (m !! k) as [x|] eqn:Hlookup.
    2: {
      apply map_filter_lookup_None_2.
      auto.
    }
    apply (map_filter_lookup_Some_2 _ _ _ _ Hlookup).
    auto.
  Qed.

  Lemma filter_by_key_Forall_false :
    map_Forall (λ k _, ¬ Pk k) m →
    filter_by_key Pk m = ∅.
  Proof.
    intros HForall.
    eapply map_filter_always_false.
    1: assumption.
    intros k x Hacc.
    apply (map_Forall_lookup_1 _ _ k x HForall) in Hacc.
    assumption.
  Qed.

  Lemma filter_by_key_Forall_true :
    map_Forall (λ k _, Pk k) m →
    filter_by_key Pk m = m.
  Proof.
    intros HForall.
    eapply map_filter_always_true.
    1: assumption.
    intros k x Hacc.
    apply (map_Forall_lookup_1 _ _ k x HForall) in Hacc.
    assumption.
  Qed.
End map_filter_by_key.

Lemma filter_by_key_union_or {K A} `{Countable K} P1 P2 `{!∀ x, Decision (P1 x)} `{!∀ x, Decision (P2 x)} (m: gmap K A):
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
    2: apply (filter_by_key_lookup_notin _ _ Hnotin1).
    apply filter_by_key_lookup_in.
    set_solver.
  }
  destruct (m !! k) as [x|] eqn:Hlookup.
  2: {
    apply (iffRL (lookup_union_None _ _ _)).
    split; apply map_filter_lookup_None_2; auto.
  }
  erewrite lookup_union_Some_l; first by auto.
  rewrite -Hlookup.
  apply (filter_by_key_lookup_in _ _ Hin1).
Qed.

Lemma set_filter_iff `{FinSet K Ct} `{!LeibnizEquiv Ct} P1 P2 `{!∀ x, Decision (P1 x)} `{!∀ x, Decision (P2 x)} (s: Ct):
  (∀ x, P1 x ↔ P2 x) → filter P1 s = filter P2 s.
Proof.
  intros Hiff.
  rewrite /filter /set_filter.
  f_equal.
  apply list_filter_iff.
  assumption.
Qed.

Lemma filter_union_or `{FinSet K Ct} `{!LeibnizEquiv Ct} P1 P2 `{!∀ x, Decision (P1 x)} `{!∀ x, Decision (P2 x)} (s: Ct):
  filter (λ k, P1 k ∨ P2 k) s =
    filter P1 s ∪ filter P2 s.
Proof.
  apply set_eq.
  intros x.
  split.
  - intros Hin.
    apply elem_of_filter in Hin.
    apply elem_of_union.
    destruct Hin as ([HP1|HP2]&Hin).
    + left.
      apply elem_of_filter.
      intuition.
    + right.
      apply elem_of_filter.
      intuition.
  - intros Hin.
    apply elem_of_filter.
    apply elem_of_union in Hin.
    destruct Hin as [HP1|HP2].
    + apply elem_of_filter in HP1.
      intuition.
    + apply elem_of_filter in HP2.
      intuition.
Qed.

Lemma map_subseteq_alt {K A} `{Countable K} `{FinMap K M} (m1 m2: M A) :
  m1 ⊆ m2 ↔
  (∀ k v, m1 !! k = Some v → m2 !! k = Some v).
Proof.
  rewrite /subseteq /map_subseteq /map_included
    /map_relation /option_relation.
  split.
  - intros Hsubseteq k v.
    specialize (Hsubseteq k).
    destruct (m1 !! k) as [v1|].
    2: intros Hc; inversion Hc.
    intros Hv1.
    inversion Hv1.
    subst v1.
    destruct (m2 !! k) as [v2|].
    2: contradiction.
    subst v2.
    reflexivity.
  - intros Halt k.
    specialize (Halt k).
    destruct (m1 !! k) as [v1|].
    2: destruct (m2 !! k); trivial.
    rewrite (Halt _ (eq_refl _)).
    reflexivity.
Qed.

Lemma set_filter_always_false `{Countable K} (s: gset K) P `{!∀ x, Decision (P x)} :
  (∀ k, k ∈ s → ¬ P k) →
  filter P s = ∅.
Proof.
  intros HP.
  apply gset.gset_elem_is_empty.
  intros k Hin.
  apply elem_of_filter in Hin.
  specialize (HP k).
  intuition.
Qed.

Definition filter_addr_set_by_blk (s_blk: gset u64) (s: gset addr) :=
  filter (λ a, addrBlock a ∈ s_blk) s.

Lemma filter_addr_set_by_blk_empty (s: gset addr) :
  filter_addr_set_by_blk (∅: gset u64) s = ∅.
Proof.
  rewrite /filter_addr_set_by_blk.
  apply set_filter_always_false.
  intros k _.
  set_solver.
Qed.

Lemma filter_addr_set_by_blk_union (s1 s2: gset u64) (s: gset addr) :
  filter_addr_set_by_blk (s1 ∪ s2) s =
    filter_addr_set_by_blk s1 s ∪ filter_addr_set_by_blk s2 s.
Proof.
  rewrite -filter_union_or.
  apply set_filter_iff.
  set_solver.
Qed.

Lemma filter_addr_set_by_blk_disjoint (s1 s2: gset u64) (s: gset addr) :
  s1 ## s2 →
  filter_addr_set_by_blk s1 s ## filter_addr_set_by_blk s2 s.
Proof.
  intros Hdisj a Hin1 Hin2.
  specialize (Hdisj (addrBlock a)).
  destruct (decide (addrBlock a ∈ s1)) as [Hin|Hnotin].
  - apply elem_of_filter in Hin2.
    intuition.
  - apply elem_of_filter in Hin1.
    intuition.
Qed.

Definition filter_addr_map_by_blk {A} (s: gset u64) (m: gmap addr A) :=
  filter_by_key (λ a, addrBlock a ∈ s) m.

Lemma filter_addr_map_by_blk_empty {A} (m: gmap addr A) :
  filter_addr_map_by_blk (∅: gset u64) m = ∅.
Proof.
  eapply map_filter_always_false.
  1: apply gmap_finmap.
  set_solver.
Qed.

Lemma filter_addr_map_by_blk_subseteq {A} (s: gset u64) (m: gmap addr A) :
  filter_addr_map_by_blk s m ⊆ m.
Proof.
  apply map_subseteq_alt.
  intros k v Hacc.
  apply (map_filter_lookup_Some_1_1 _ _ _ _ Hacc).
Qed.

Lemma filter_addr_map_by_blk_union {A} (s1 s2: gset u64) (m: gmap addr A) :
  filter_addr_map_by_blk (s1 ∪ s2) m =
    filter_addr_map_by_blk s1 m ∪ filter_addr_map_by_blk s2 m.
Proof.
  rewrite -filter_by_key_union_or.
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

Lemma filter_addr_map_by_blk_lookup_notin {A} (s: gset u64) (m: gmap addr A) a :
  addrBlock a ∉ s →
  filter_addr_map_by_blk s m !! a = None.
Proof.
  intros Hnotin.
  apply filter_by_key_lookup_notin.
  assumption.
Qed.

Lemma filter_addr_map_by_blk_disjoint {A} (s1 s2: gset u64) (m: gmap addr A) :
  s1 ## s2 →
  filter_addr_map_by_blk s1 m ##ₘ filter_addr_map_by_blk s2 m.
Proof.
  intros Hdisj.
  apply map_disjoint_alt.
  pose proof ((iffLR (elem_of_disjoint _ _)) Hdisj) as Hdisj_alt.
  intros a.
  destruct (decide (addrBlock a ∈ s1)) as [Hin|Hnotin].
  - right.
    specialize (Hdisj_alt _ Hin).
    apply filter_addr_map_by_blk_lookup_notin.
    intuition.
  - left.
    apply filter_addr_map_by_blk_lookup_notin.
    assumption.
Qed.

Lemma filter_addr_map_by_blk_dom_in {A} (s: gset u64) (m: gmap addr A) a :
  a ∈ dom (gset addr) (filter_addr_map_by_blk s m) →
  is_Some (m !! a) ∧ addrBlock a ∈ s.
Proof.
  intros Hin.
  apply mspec.map_filter_elem_of_dom in Hin.
  destruct Hin as [obj [Hacc Ha]].
  apply mk_is_Some in Hacc.
  simpl in Ha.
  intuition.
Qed.

Lemma filter_addr_map_by_blk_set_dom {A} (s: gset u64) (m: gmap addr A):
  dom (gset addr) (filter_addr_map_by_blk s m) =
  filter_addr_set_by_blk s (dom (gset addr) m).
Proof.
  apply dom_filter_L.
  intros a.
  split.
  - intros Hin.
    destruct ((iffLR (elem_of_filter _ _ _)) Hin)
      as [Hblk Hdom].
    apply elem_of_dom in Hdom.
    destruct Hdom as [v Hdom].
    eexists _.
    split; first by eassumption.
    simpl.
    assumption.
  - intros Hspec.
    destruct Hspec as [v [Hacc Hin]].
    simpl in Hin.
    apply elem_of_filter.
    split; first by assumption.
    apply elem_of_dom.
    eexists _.
    eassumption.
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

Implicit Types γ : @buftxn_names Σ.
Implicit Types dinit : disk.
Implicit Types objs_dom : gset addr.
Implicit Types mt_changed : gmap addr versioned_object.
Implicit Types mt_all : gmap addr object.
Implicit Types mt_committed : gmap addr object.
Implicit Types blkno : u64.
Implicit Types inst : nat.
Implicit Types γdurable_map : gmap nat gname.
Implicit Types locked_by_map : gmap u64 (option nat).

Definition modified := mspec.modified.
Definition committed := mspec.committed.

Definition get_lockset_opt locked_by_map inst_opt :=
  dom (gset u64) (filter (λ x, x.2 = inst_opt) locked_by_map).

Definition filter_locked_by locked_by_map mt_all inst_opt :=
  filter_addr_map_by_blk (get_lockset_opt locked_by_map inst_opt) mt_all.

Lemma filter_locked_by_alt locked_by_map mt_all inst_opt :
  filter_locked_by locked_by_map mt_all inst_opt =
  filter_by_key
    (λ a, locked_by_map !! (addrBlock a) = Some inst_opt)
    mt_all.
Proof.
  apply map_eq.
  intros a.
  destruct (decide (locked_by_map !! addrBlock a = Some inst_opt))
    as [Hacc|Hacc].
  2: {
    rewrite filter_by_key_lookup_notin.
    2: assumption.
    rewrite filter_addr_map_by_blk_lookup_notin; first by reflexivity.
    intros Hin.
    rewrite /get_lockset_opt in Hin.
    apply elem_of_dom in Hin.
    destruct Hin as [inst_opt' Hinst_opt'].
    apply map_filter_lookup_Some in Hinst_opt'.
    destruct Hinst_opt' as [Hacc' Heq].
    simpl in Heq.
    subst inst_opt'.
    contradiction.
  }
  rewrite filter_by_key_lookup_in.
  2: assumption.
  rewrite filter_addr_map_by_blk_lookup_in; first by reflexivity.
  apply elem_of_dom.
  exists inst_opt.
  apply map_filter_lookup_Some_2.
  1: assumption.
  auto.
Qed.

(*
Definition buftxn_durable_mapsto γbuftxn inst_state : iProp Σ :=
  is_buftxn_durable γbuftxn inst_state.(twophase_inst_γdurable)
    (λ mapsto,
      [∗ map] a ↦ obj ∈ inst_state.(twophase_inst_mt_committed),
        mapsto a obj
    )%I.

Definition twophase_durable_inv_inner γ mt_all : iProp Σ :=
  ∃ inst_map locked_by_map,
    let mt_unused := filter_locked_by locked_by_map mt_all None in
    "Hinst_map_ctx" ∷ map_ctx γ.(twophase_inst_map_name) 1 inst_map ∗
    "Hlocked_by_ctx" ∷ map_ctx γ.(twophase_locked_by_map_name) 1 locked_by_map ∗
    "Hmt_used" ∷ (
      [∗ map] inst ↦ inst_state ∈ inst_map,
      (
        "Hbuftxn_durable" ∷ buftxn_durable_mapsto
          γ inst_state
      )
    ) ∗
    "Hmt_unused" ∷ (
      [∗ map] a ↦ obj ∈ mt_unused,
        durable_mapsto γ a obj
    ) ∗
    "%Hmt_committed_map" ∷ ⌜map_Forall (λ inst inst_state,
      inst_state.(twophase_inst_mt_committed) =
      filter_locked_by locked_by_map mt_all (Some inst)
    ) inst_map⌝ ∗
    "%Hlocked_by_wf" ∷ ⌜map_Forall (λ _ inst_opt,
      ∀ inst, (
        inst_opt = Some inst →
        is_Some (inst_map !! inst)
      )
    ) locked_by_map⌝.

Definition twophase_durable_inv γ obj_dom P `{!∀ mt_all, Timeless (P mt_all)} : iProp Σ :=
  ∃ mt_all,
    "%Hmt_all_dom" ∷ ⌜dom (gset addr) mt_all = obj_dom⌝ ∗
    "Htwophase_durable_inv" ∷ twophase_durable_inv_inner γ mt_all ∗
    "HP" ∷ P mt_all.

Global Instance twophase_durable_inv_timeless γ obj_dom P `{!∀ mt_all, Timeless (P mt_all)} :
  Timeless (twophase_durable_inv γ obj_dom P) := _.
*)

Definition twophase_linv γ objs_dom blkno : iProp Σ :=
  "Htokens" ∷ [∗ set] a ∈ filter_addr_set_by_blk {[blkno]} objs_dom, (
    "Htoken" ∷ modify_token γ a
  ).

Definition is_twophase_locks (l: loc) γ objs_dom (locks_held: list u64) : iProp Σ :=
  ∃ (locksl: loc) acquired_s ghs,
    let objs_dom_blknos := get_addr_set_blknos objs_dom in
    let locked_blknos: gset u64 := list_to_set locks_held in
    "Htwophase.locks" ∷ l ↦[TwoPhase.S :: "locks"] #locksl ∗
    "Htwophase.acquired" ∷
      l ↦[TwoPhase.S :: "acquired"] (slice_val acquired_s) ∗
    "Hacquired_s" ∷ is_slice acquired_s uint64T 1 locks_held ∗
    "Hlocked_blknos" ∷ ([∗ set] blkno ∈ locked_blknos,
      "Hlocked" ∷ Locked ghs blkno
    ) ∗
    "#HlockMap" ∷ is_lockMap locksl ghs objs_dom_blknos
      (twophase_linv γ objs_dom) ∗
    "%Hlocks_held_NoDup" ∷ ⌜NoDup locks_held⌝.

Definition is_twophase_buftxn (l: loc) γ γtxn dinit mt_committed : iProp Σ :=
  ∃ (buftxnl: loc) γdurable,
    "Htwophase.buftxn" ∷ l ↦[TwoPhase.S :: "buftxn"] #buftxnl ∗
    "Hbuftxn_mem" ∷ is_buftxn_mem
      Nbuftxn buftxnl γ dinit γtxn γdurable ∗
    "Hbuftxn_durable_frag" ∷ map_ctx γdurable (1/2) mt_committed.

Definition twophase_locked_mapstos γ locked_addrs mt_committed : iProp Σ :=
  "Hunlifted_mapstos" ∷ (
    [∗ set] a ∈ locked_addrs ∖ dom (gset addr) mt_committed,
      "Htoken" ∷ modify_token γ a
  ) ∗
  "Hlifted_mapstos" ∷ (
    [∗ map] a ↦ obj ∈ mt_committed,
      "Hdurable_mapsto" ∷ durable_mapsto γ a obj
  ).

Definition is_twophase_raw l γ γtxn dinit objs_dom mt_committed : iProp Σ :=
  ∃ locks_held,
    let locked_blknos: gset u64 := list_to_set locks_held in
    let locked_addrs := filter_addr_set_by_blk locked_blknos objs_dom in
    "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held ∗
    "Hbuftxn" ∷ is_twophase_buftxn l γ γtxn dinit mt_committed ∗
    "Hlocked_mapstos" ∷ twophase_locked_mapstos γ locked_addrs mt_committed ∗
    "%Hmt_dom" ∷ ⌜dom (gset addr) mt_committed ⊆ locked_addrs⌝
  .

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

Definition set_max `{FinSet nat Ct} (s: Ct) := list_max (elements s).

Lemma set_in_le_max `{FinSet nat Ct} (s: Ct) x:
  x ∈ s → x ≤ set_max s.
Proof.
  intros Hin.
  unshelve (epose proof (
    (iffLR (list_max_le (elements s) (set_max s))) _
  ) as Hthm).
  1: rewrite /set_max; lia.
  eapply (iffLR (Forall_forall _ _)) in Hthm.
  2: apply elem_of_elements; eassumption.
  assumption.
Qed.

Theorem wp_TwoPhase__Begin_raw (txnl locksl: loc) γ dinit ghs objs_dom :
  {{{
    let objs_dom_blknos := get_addr_set_blknos objs_dom in
    "#Htxn" ∷ (
      invariant.is_txn txnl γ.(buftxn_txn_names) dinit ∗
      is_txn_system Nbuftxn γ
    ) ∗
    "#Hlocks" ∷ is_lockMap locksl ghs objs_dom_blknos (twophase_linv γ objs_dom)
  }}}
    Begin #txnl #locksl
  {{{
    (l : loc) γtxn, RET #l;
      "Htwophase_raw" ∷ is_twophase_raw l γ γtxn dinit objs_dom ∅
  }}}.
Proof.
  simpl.
  wp_start.
  wp_call.
  wp_apply (wp_BufTxn__Begin' with "Htxn").
  iIntros (? ? buftxnl) "(?&?)".
  iNamed.
  wp_apply (wp_NewSlice _ _ uint64T).
  iIntros (acquired_s) "Hacquired_s".
  wp_apply wp_allocStruct; first by auto.
  iIntros (l) "Hl".
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_pures.
  iApply "HΦ".

  iExists [].
  iDestruct (struct_fields_split with "Hl") as "(?&?&?&_)".
  iNamed.
  iSplitL "locks acquired Hacquired_s".
  {
    iExists _, _, _.
    rewrite list_to_set_nil big_sepS_empty.
    iFrame "∗ #".
    iPureIntro.
    apply NoDup_nil_2.
  }
  iSplitL.
  {
    iExists _, _.
    iFrame.
  }
  rewrite filter_addr_set_by_blk_empty
    /twophase_locked_mapstos big_sepM_empty
    dom_empty_L difference_empty_L big_sepS_empty //.
Qed.

Section map_zip.
  Context {K A B: Type} `{Countable K} (m1: gmap K A) (m2: gmap K B).

  Lemma map_zip_fst :
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

  Lemma map_zip_snd :
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

  Lemma map_zip_lookup_some' k x1 x2 :
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

  Lemma map_zip_dom :
    dom (gset K) (map_zip m1 m2) = dom (gset K) m1 ∩ dom (gset K) m2.
  Proof.
    apply set_eq.
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
End map_zip.

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

Lemma map_union_least {K A} `{Countable K} `{FinMap K M} (m1 m2 m3: M A) :
  m1 ⊆ m3 ∧ m2 ⊆ m3 → m1 ∪ m2 ⊆ m3.
Proof.
  intros (Hm1&Hm2).
  apply map_subseteq_union in Hm1.
  rewrite -Hm1.
  apply map_union_mono_l.
  assumption.
Qed.

Lemma map_filter_mono `{Countable K} `{FinMap K M} {A} (m: M A) P Q `{!∀ x, Decision (P x)} `{!∀ x, Decision (Q x)} :
  (∀ k v, m !! k = Some v → P (k, v) → Q (k, v)) →
  filter P m ⊆ filter Q m.
Proof.
  intros Hmono.
  eapply (iffRL (map_subseteq_alt _ _)).
  intros k v Hfilter_acc.
  assert (m !! k = Some v) as Hacc by (
    eapply map_filter_lookup_Some_1_1; eassumption
  ).
  apply (map_filter_lookup_Some_2 _ _ _ _ Hacc).
  apply (Hmono _ _ Hacc).
  apply (map_filter_lookup_Some_1_2 _ _ _ _ Hfilter_acc).
Qed.

Lemma set_filter_mono `{FinSet K Ct} (s: Ct) P Q `{!∀ x, Decision (P x)} `{!∀ x, Decision (Q x)} :
  (∀ k, k ∈ s → P k → Q k) →
  filter P s ⊆ filter Q s.
Proof.
  intros Hmono.
  intros k HinP.
  apply elem_of_filter in HinP.
  apply elem_of_filter.
  intuition.
Qed.

Lemma set_disjoint_weaken_l `{FinSet K Ct} (s1 s1' s2: Ct) :
  s1' ## s2 → s1 ⊆ s1' → s1 ## s2.
Proof.
  set_solver.
Qed.

Lemma subseteq_trans `{FinSet K Ct} (s1 s2 s3: Ct) :
  s1 ⊆ s2 → s2 ⊆ s3 → s1 ⊆ s3.
Proof.
  set_solver.
Qed.

Theorem wp_TwoPhase__acquireNoCheck (l: loc) γ (blkno: u64) objs_dom locks_held:
  blkno ∈ get_addr_set_blknos objs_dom →
  blkno ∉ locks_held →
  {{{
    "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held
  }}}
    TwoPhase__acquireNoCheck #l #blkno
  {{{
    RET #();
    "Hlocks" ∷ is_twophase_locks l γ objs_dom (locks_held ++ [blkno]) ∗
    "Hlinv" ∷ twophase_linv γ objs_dom blkno
  }}}.
Proof.
  intros Hblkno_wf Hblkno_not_locked.
  wp_start.
  wp_call.
  iNamed "Hlocks".
  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$HlockMap]").
  1: iPureIntro; assumption.
  iIntros "[Hlinv Hlocked]".
  wp_loadField.
  wp_apply (wp_SliceAppend (V:=u64) with "[$Hacquired_s]").
  iIntros (acquired_s') "Hacquired_s".
  wp_apply (wp_storeField with "Htwophase.acquired").
  1: rewrite /field_ty /=; val_ty.
  iIntros "Htwophase.acquired".
  iApply "HΦ".

  iFrame "Hlinv".
  iExists _, _, _.
  iFrame "∗ #".
  iSplit.
  {
    rewrite list_to_set_app_L
      (leibniz_equiv _ _ (list_to_set_singleton _)).
    iApply big_sepS_union.
    2: iFrame; iApply big_sepS_singleton; iFrame.
    intros blkno' Hin1 Hin2.
    apply (iffLR (elem_of_singleton _ _)) in Hin2.
    subst blkno'.
    apply elem_of_list_to_set in Hin1.
    contradiction.
  }
  iPureIntro.
  apply NoDup_app.
  split; first by assumption.
  split.
  2: apply NoDup_singleton.
  intros blkno' Hin1 Hin2.
  apply elem_of_list_singleton in Hin2.
  subst blkno'.
  contradiction.
Qed.

Theorem wp_TwoPhase__isAlreadyAcquired (l: loc) γ objs_dom locks_held blkno :
  {{{
    "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held
  }}}
    TwoPhase__isAlreadyAcquired #l #blkno
  {{{
    RET #(bool_decide (blkno ∈ locks_held));
    "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held
  }}}.
Proof.
  wp_start.
  wp_call.
  wp_apply wp_ref_to; first by auto.
  iIntros (already_acquired_l) "Halready_acquired_l".
  iNamed "Hlocks".
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
  iApply "HΦ".
  iExists _, _, _.
  iFrame "∗ # %".
Qed.

Theorem wp_TwoPhase__Acquire (l: loc) γ objs_dom locks_held (blkno: u64):
  blkno ∈ get_addr_set_blknos objs_dom →
  {{{
    "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held
  }}}
    TwoPhase__Acquire #l #blkno
  {{{
    RET #();
    if (decide (blkno ∈ locks_held)) then
      "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held
    else (
      "Hlocks" ∷ is_twophase_locks l γ objs_dom (locks_held ++ [blkno]) ∗
      "Hlinv" ∷ twophase_linv γ objs_dom blkno
    )
  }}}.
Proof.
  intros Hwf.
  wp_start.
  wp_call.
  wp_apply (wp_TwoPhase__isAlreadyAcquired with "Hlocks").
  iNamed 1.
  wp_if_destruct.
  2: {
    iApply "HΦ".
    rewrite (decide_True _ _ Heqb).
    iFrame.
  }
  wp_apply (wp_TwoPhase__acquireNoCheck with "Hlocks").
  1-2: assumption.
  iNamed 1.
  iApply "HΦ".
  rewrite (decide_False _ _ Heqb).
  iFrame.
Qed.

Lemma twophase_locked_mapstos_add γ locked_blknos mt_committed objs_dom blkno :
  dom (gset addr) mt_committed ⊆
    filter_addr_set_by_blk locked_blknos objs_dom →
  blkno ∉ locked_blknos →
  "Hmapstos" ∷ twophase_locked_mapstos
    γ (filter_addr_set_by_blk locked_blknos objs_dom) mt_committed -∗
  "Hlinv" ∷ twophase_linv γ objs_dom blkno -∗
    "Hmapstos" ∷ twophase_locked_mapstos
      γ (filter_addr_set_by_blk (locked_blknos ∪ {[blkno]}) objs_dom)
      mt_committed.
Proof.
  iIntros (Hmt_dom Hnew) "??".
  iNamed.
  iDestruct "Hmapstos" as "(?&?)".
  iNamed.
  iFrame.
  rewrite filter_addr_set_by_blk_union difference_union_distr_l_L.
  iApply big_sepS_union.
  {
    apply disjoint_difference_l2.
    apply disjoint_difference_r2.
    apply filter_addr_set_by_blk_disjoint.
    apply disjoint_singleton_r.
    assumption.
  }
  iFrame.
  rewrite difference_disjoint_L.
  2: {
    apply disjoint_sym.
    eapply set_disjoint_weaken_l; last by eassumption.
    apply filter_addr_set_by_blk_disjoint.
    apply disjoint_singleton_r.
    assumption.
  }
  iFrame.
Qed.

Theorem wp_TwoPhase__Acquire_merge (l: loc) γ objs_dom locks_held mt_committed (blkno: u64):
  dom (gset addr) mt_committed ⊆
    filter_addr_set_by_blk (list_to_set locks_held) objs_dom →
  blkno ∈ get_addr_set_blknos objs_dom →
  {{{
    "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held ∗
    "Hmapstos" ∷ twophase_locked_mapstos
      γ (filter_addr_set_by_blk
      (list_to_set locks_held) objs_dom) mt_committed
  }}}
    TwoPhase__Acquire #l #blkno
  {{{
    RET #();
    let locks_held' := (
      if (decide (blkno ∈ locks_held)) then
        locks_held
      else
        locks_held ++ [blkno]
    ) in
    "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held' ∗
    "Hmapstos" ∷ twophase_locked_mapstos
      γ (filter_addr_set_by_blk
      (list_to_set locks_held') objs_dom) mt_committed
  }}}.
Proof.
  iIntros (Hmt_dom Hwf).
  wp_start.
  wp_apply (wp_TwoPhase__Acquire with "Hlocks");
    first by assumption.
  destruct (decide (blkno ∈ locks_held)) as [Hlocked|Hnot_locked].
  {
    iNamed 1.
    iApply "HΦ".
    iFrame.
  }
  iNamed 1.

  iApply "HΦ".
  iDestruct (twophase_locked_mapstos_add with "Hmapstos Hlinv")
    as "?"; [by assumption|apply not_elem_of_list_to_set; assumption|].
  iNamed.
  rewrite list_to_set_app_L
    (leibniz_equiv _ _ (list_to_set_singleton _)).
  iFrame.
Qed.

Lemma is_twophase_buftxn_not_in_map l γ γtxn dinit mt_committed a obj :
  "Hbuftxn" ∷ is_twophase_buftxn l γ γtxn dinit mt_committed -∗
  "Hold_vals" ∷ (
    [∗ map] a ↦ obj ∈ mt_committed,
      "Hdurable_mapsto" ∷ durable_mapsto γ a obj
  ) -∗
  "Hdurable_mapsto" ∷ durable_mapsto γ a obj -∗
  ⌜mt_committed !! a = None⌝.
Proof.
  iIntros "???".
  iNamed.
  iNamed "Hbuftxn".
  iNamed "Hbuftxn_mem".
  iDestruct (map_ctx_agree with "Hbuftxn_durable_frag Hdurable") as %<-.
  iApply (
    is_buftxn_durable_not_in_map with
    "Hdurable_mapsto [Hbuftxn_durable_frag Hold_vals] Hdurable"
  ).
  iExists _.
  iFrame.
  iModIntro.
  iIntros (?) "Hmapstos".
  trivial.
Qed.

Theorem twophase_lift l γ dinit γtxn locked_addrs mt_committed a obj :
  a ∈ locked_addrs →
  "Hbuftxn" ∷ is_twophase_buftxn l γ γtxn dinit mt_committed -∗
  "Hmapstos" ∷ twophase_locked_mapstos γ locked_addrs mt_committed -∗
  "Hdurable_mapsto" ∷ durable_mapsto γ a obj
  -∗ |NC={⊤}=>
  "Hbuftxn" ∷ is_twophase_buftxn
    l γ γtxn dinit (<[a:=obj]>mt_committed) ∗
  "Hmapstos" ∷ twophase_locked_mapstos
    γ locked_addrs (<[a:=obj]>mt_committed) ∗
  "Hbuftxn_maps_to" ∷ buftxn_maps_to γtxn a obj.
Proof.
  iIntros (Hlocked) "???".
  iNamed.
  iNamed "Hmapstos".
  iDestruct (
    is_twophase_buftxn_not_in_map with
    "Hbuftxn Hlifted_mapstos Hdurable_mapsto"
  ) as "%Hnotin".
  iNamed "Hbuftxn".
  apply not_elem_of_dom in Hnotin.
  iDestruct (big_sepS_delete _ _ a with "Hunlifted_mapstos")
    as "[? Hunlifted_mapstos]";
    first by set_solver.
  iNamed.
  iMod (lift_into_txn' with "
    Hbuftxn_mem Hbuftxn_durable_frag Hlifted_mapstos
    [Hdurable_mapsto Htoken]
  ") as "(?&?&?&?&?)".
  1-3: solve_ndisj.
  1: iFrame.
  iNamed.
  iModIntro.
  iFrame "Hbuftxn_maps_to".
  iSplitL "Htwophase.buftxn Hbuftxn_mem Hdurable_frag";
   first by (iExists _, _; iFrame).
 iFrame.
 rewrite dom_insert_L set_union_comm -difference_difference_L.
 iFrame.
Qed.

Theorem twophase_lift_if_needed l γ dinit γtxn locked_addrs mt_committed a obj :
  a ∈ locked_addrs →
  "Hbuftxn" ∷ is_twophase_buftxn l γ γtxn dinit mt_committed -∗
  "Hmapstos" ∷ twophase_locked_mapstos γ locked_addrs mt_committed -∗
  "Hmapsto" ∷ (
    match mt_committed !! a with
    | Some _ => buftxn_maps_to γtxn a obj
    | None => durable_mapsto γ a obj
    end
  )
  -∗ |NC={⊤}=>
  let mt_committed' :=
    match mt_committed !! a with
    | Some _ => mt_committed
    | None => <[a:=obj]>mt_committed
    end
  in
  "Hbuftxn" ∷ is_twophase_buftxn l γ γtxn dinit mt_committed' ∗
  "Hmapstos" ∷ twophase_locked_mapstos γ locked_addrs mt_committed' ∗
  "Hbuftxn_maps_to" ∷ buftxn_maps_to γtxn a obj.
Proof.
  iIntros (Hlocked) "???".
  iNamed.
  destruct (mt_committed !! a) as [old_obj|] eqn:Hlookup_old;
    first by (iModIntro; iFrame).
  iMod (twophase_lift with "Hbuftxn Hmapstos Hmapsto") as "(?&?&?)";
    first by assumption.
  iNamed.
  iModIntro.
  iFrame.
Qed.

Theorem wp_TwoPhase__Acquire_lift (l: loc) γ γtxn dinit objs_dom mt_committed a obj:
  a ∈ objs_dom →
  {{{
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit objs_dom mt_committed ∗
    "Hmapsto" ∷ (
      match mt_committed !! a with
      | Some _ => buftxn_maps_to γtxn a obj
      | None => durable_mapsto γ a obj
      end
    )
  }}}
    TwoPhase__Acquire #l #(addrBlock a)
  {{{
    RET #();
    let mt_committed' :=
      match mt_committed !! a with
      | Some _ => mt_committed
      | None => <[a:=obj]>mt_committed
      end
    in
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit objs_dom mt_committed' ∗
    "Hmapsto" ∷ buftxn_maps_to γtxn a obj
  }}}.
Proof.
  iIntros (Hwf).
  wp_start.
  iNamed "Htwophase".
  iApply wp_ncfupd.
  wp_apply (wp_TwoPhase__Acquire_merge with "[$Hlocks $Hlocked_mapstos]");
    [assumption|apply elem_of_map_2; assumption|].
  iNamed 1.
  iMod (twophase_lift_if_needed with "Hbuftxn Hmapstos Hmapsto")
    as "(?&?&?)".
  {
    apply elem_of_filter.
    split; last by assumption.
    apply elem_of_list_to_set.
    destruct (decide (addrBlock a ∈ locks_held)); first by assumption.
    apply elem_of_app.
    right.
    apply elem_of_list_singleton.
    reflexivity.
  }
  iNamed.
  iModIntro.
  iApply "HΦ".
  iFrame "Hbuftxn_maps_to".
  iExists _.
  iFrame.
  iPureIntro.
  destruct (mt_committed !! a) as [old_obj|] eqn:Hlookup_old.
  {
    apply mk_is_Some in Hlookup_old.
    rewrite decide_True; first by assumption.
    apply elem_of_dom in Hlookup_old.
    specialize (Hmt_dom a Hlookup_old).
    apply elem_of_filter in Hmt_dom.
    destruct Hmt_dom as [Hlocked Hwf_strong].
    apply elem_of_list_to_set in Hlocked.
    apply Hlocked.
  }
  rewrite dom_insert.
  destruct (decide (addrBlock a ∈ locks_held)) as [Hlocked|Hnot_locked].
  {
    apply union_least; last by assumption.
    apply elem_of_subseteq_singleton.
    apply elem_of_filter.
    split; last by assumption.
    apply elem_of_list_to_set.
    assumption.
  }
  rewrite list_to_set_app_L
    (leibniz_equiv _ _ (list_to_set_singleton _))
    filter_addr_set_by_blk_union
    union_comm.
  apply union_mono; first by assumption.
  apply elem_of_subseteq_singleton.
  apply elem_of_filter.
  split; last by assumption.
  set_solver.
Qed.

Theorem wp_TwoPhase__Release (l: loc) γ locks_held blkno objs_dom :
  {{{
    "Hlocks" ∷ is_twophase_locks
      l γ objs_dom (locks_held ++ [blkno]) ∗
    "Hlinv" ∷ twophase_linv γ objs_dom blkno
  }}}
    TwoPhase__Release #l
  {{{
    RET #();
    "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held
  }}}.
Proof.
  wp_start.
  wp_call.
  iNamed "Hlocks".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_loadField.
  iDestruct (is_slice_small_read with "Hacquired_s") as "[Hacquired_s Hacquired_s_wrap]".
  iDestruct (is_slice_small_sz with "Hacquired_s") as "%Hacquired_s_sz".
  assert ((locks_held ++ [blkno]) !! (length locks_held) = Some blkno)
    as Hlocked_blknos_acc.
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
  iApply "Hacquired_s_wrap" in "Hacquired_s".
  wp_loadField.
  rewrite list_to_set_app_L.
  iDestruct (big_sepS_union with "Hlocked_blknos")
    as "[Hlocked_blknos Hlocked]".
  {
    apply NoDup_app in Hlocks_held_NoDup.
    destruct Hlocks_held_NoDup as (_ & Hdisj & _).
    set_solver.
  }
  rewrite /= union_empty_r_L big_sepS_singleton.
  iNamed "Hlocked".
  wp_apply (wp_LockMap__Release with "[$HlockMap $Hlocked $Hlinv]").
  wp_loadField.
  wp_apply (wp_SliceTake uint64T).
  1: word.
  wp_apply (wp_storeField with "Htwophase.acquired").
  1: rewrite /field_ty /=; val_ty.
  iIntros "Htwophase.acquired".

  iApply "HΦ".
  iExists _, _, _.
  iFrame "∗ #".
  iSplit.
  2: apply NoDup_app in Hlocks_held_NoDup; intuition.
  iApply (is_slice_take_cap _ _ _ (word.sub acquired_s.(Slice.sz) 1)) in
    "Hacquired_s".
  1: rewrite fmap_length app_length /=; word.
  replace (int.nat (word.sub _ 1)) with ((int.nat acquired_s.(Slice.sz)) - 1)%nat by word.
  rewrite -fmap_take -Hacquired_s_sz Nat.add_sub take_app.
  iFrame.
Qed.

Lemma big_sepM_list_to_map `{Countable K} {A} l (Φ: K → A → iProp Σ) :
  NoDup l.*1 →
  ([∗ list] x ∈ l, Φ x.1 x.2) -∗
  ([∗ map] k↦v ∈ list_to_map l, Φ k v).
Proof.
  induction l as [|x].
  {
    iIntros (HNoDup) "Hsep".
    rewrite list_to_map_nil.
    iApply big_sepM_empty.
    auto.
  }
  iIntros (HNoDup) "Hsep".
  destruct x as [k v].
  rewrite list_to_map_cons.
  iDestruct (big_sepL_cons with "Hsep") as "[Hx Hsep]".
  rewrite fmap_cons in HNoDup.
  apply NoDup_cons in HNoDup.
  destruct HNoDup as [Hnotin HNoDup].
  iApply big_sepM_insert.
  {
    apply not_elem_of_list_to_map_1.
    auto.
  }
  simpl.
  iFrame.
  iApply ((IHl HNoDup) with "Hsep").
Qed.

Theorem wp_TwoPhase__ReleaseAll (l: loc) γ objs_dom locks_held :
  {{{
    "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held ∗
    "Hlinvs" ∷ ([∗ list] blkno ∈ locks_held, (
      "Hlinv" ∷ twophase_linv γ objs_dom blkno
    ))
  }}}
    TwoPhase__ReleaseAll #l
  {{{
    RET #(); True
  }}}.
Proof.
  wp_start.
  wp_call.
  wp_apply (wp_forBreak_cond (λ b,
    ∃ i,
      "Hlocks" ∷ is_twophase_locks
        l γ objs_dom (take i locks_held) ∗
      "Hlinvs" ∷ ([∗ list] blkno ∈ take i locks_held, (
        "Hlinv" ∷ twophase_linv γ objs_dom blkno
      )) ∗
      "%Hi" ∷ ⌜i ≤ length locks_held⌝ ∗
      "%Hb" ∷ ⌜b = false → drop i locks_held = locks_held⌝
  )%I with "[] [Hlocks Hlinvs]").
  2: {
    iExists (length locks_held).
    rewrite firstn_all drop_all.
    iFrame.
    iSplit; first by auto.
    auto.
  }
  {
    iModIntro.
    iIntros (Φ') "Hloop HΦ'".
    iDestruct "Hloop" as (i) "(?&?&?&?)".
    iNamed.
    iNamed "Hlocks".
    wp_loadField.
    wp_apply wp_slice_len.
    iDestruct (is_slice_sz with "Hacquired_s") as "%Hlocked_blknos_len".
    wp_if_destruct.
    2: {
      iApply "HΦ'".
      iExists 0%nat.
      rewrite Heqb in Hlocked_blknos_len.
      replace (int.nat 0) with 0%nat in Hlocked_blknos_len by word.
      apply nil_length_inv in Hlocked_blknos_len.
      pose proof (take_drop i locks_held) as Htake_drop.
      rewrite Hlocked_blknos_len app_nil_l in Htake_drop.
      rewrite Hlocked_blknos_len take_0 drop_0.
      iFrame.
      iSplit.
      2: {
        iPureIntro.
        split.
        2: auto.
        lia.
      }
      iExists _, _, _.
      iFrame "∗ #".
      iPureIntro.
      apply NoDup_nil_2.
    }

    iAssert (is_twophase_locks l γ objs_dom (take i locks_held))
      with
        "[Htwophase.locks Htwophase.acquired
        Hacquired_s Hlocked_blknos]"
      as "Htwophase".
    {
      iExists _, _, _.
      iFrame "∗ # %".
    }
    destruct i.
    {
      rewrite take_0 /= in Hlocked_blknos_len.
      apply u64_val_ne in Heqb.
      replace (int.Z 0%Z) with 0%Z in Heqb by word.
      word.
    }
    assert (i < length locks_held) as Hi_bounds by lia.
    apply list_lookup_lt in Hi_bounds.
    destruct Hi_bounds as [curr_lock Hcurr_lock].
    rewrite (take_S_r _ _ _ Hcurr_lock).
    iDestruct (big_sepL_app with "Hlinvs") as "[Hlinvs Hlinv]".
    iDestruct (big_sepL_cons with "Hlinv") as "[? _]".
    iNamed.
    wp_apply (wp_TwoPhase__Release with "[$Htwophase $Hlinv]").
    iNamed 1.

    wp_pures.
    iApply "HΦ'".
    iExists _.
    iFrame.
    iPureIntro.
    split; first by lia.
    intros Hc.
    inversion Hc.
  }
  iIntros "Hloop".
  iDestruct "Hloop" as (?) "(?&?&?&?)".
  iNamed.
  pose proof (Hb eq_refl) as Hlocked_blknos.

  iApply "HΦ".
  auto.
Qed.

Theorem wpc_TwoPhase__CommitNoRelease_raw {k} l γ γ' γtxn dinit objs_dom mt_committed mt_modified :
  dom (gset addr) mt_committed = dom (gset addr) mt_modified →
  {{{
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit objs_dom mt_committed ∗
    "Hbuftxn_mapstos" ∷ ([∗ map] a ↦ obj ∈ mt_modified,
      "Hbuftxn_mapsto" ∷ buftxn_maps_to γtxn a obj
    ) ∗
    "#Htxn_cinv" ∷ txn_cinv Nbuftxn γ γ'
  }}}
    TwoPhase__CommitNoRelease #l @ S k; ⊤
  {{{
    (ok:bool) locks_held, RET #ok;
    let locked_blknos: gset u64 := list_to_set locks_held in
    let locked_addrs := filter_addr_set_by_blk locked_blknos objs_dom in
    "Hlocks" ∷ is_twophase_locks l γ objs_dom locks_held ∗
    "Htokens" ∷ (
      [∗ set] a ∈ locked_addrs,
        "Htoken" ∷ modify_token γ a
    ) ∗
    "Hdurable_mapstos" ∷ (
      [∗ map] a ↦ obj ∈ (if ok then mt_modified else mt_committed),
        "Hdurable_mapsto" ∷ durable_mapsto γ a obj
    ) ∗
    "%Hmt_dom" ∷ ⌜dom (gset addr) mt_committed ⊆ locked_addrs⌝
  }}}
  {{{
    (
      [∗ map] a ↦ obj ∈ mt_modified,
        "Hdurable_mapsto" ∷ durable_mapsto γ' a obj
    ) ∨ (
      [∗ map] a ↦ obj ∈ mt_committed,
        "Hdurable_mapsto" ∷ durable_mapsto γ' a obj
    )
  }}}.
Proof.
  remember (
    [∗ map] a ↦ obj ∈ mt_committed, _
  )%I as old_vals_durable.
  remember (
    [∗ map] a ↦ obj ∈ mt_modified, _
  )%I as new_vals_durable.

  iIntros (Hdom Φ Φc) "(?&?&?) HΦ".
  iNamed.
  iNamed "Htwophase".
  iNamed "Hlocked_mapstos".
  iNamed "Hbuftxn".
  iApply wpc_cfupd.
  rewrite /TwoPhase__CommitNoRelease.
  wpc_pures.
  {
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iMod (
      exchange_durable_mapsto with "[$Htxn_cinv $Hlifted_mapstos]"
    ) as "Hmapstos".
    iModIntro.
    iApply "HΦc".
    iRight.
    subst.
    iApply (big_sepM_mono with "Hmapstos").
    iIntros (a obj Hin) "(?&?)".
    iFrame.
  }
  iCache (<disc> |C={⊤}_S k=> Φc)%I with "Hlifted_mapstos HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iMod (
      exchange_durable_mapsto with "[$Htxn_cinv $Hlifted_mapstos]"
    ) as "Hmapstos".
    iModIntro.
    iApply "HΦc".
    iRight.
    subst.
    iApply (big_sepM_mono with "Hmapstos").
    iIntros (a obj Hin) "(?&?)".
    iFrame.
  }
  wpc_frame_seq.
  wp_apply util_proof.wp_DPrintf.
  iNamed 1.
  wpc_pures.
  wpc_bind (struct.loadF _ _ _).
  wpc_frame "HΦ Hlifted_mapstos".
  wp_loadField.
  iNamed 1.
  wpc_apply (wpc_BufTxn__CommitWait' with "[
    $Hbuftxn_mem Hbuftxn_durable_frag Hlifted_mapstos Hbuftxn_mapstos
    Htxn_cinv
  ]").
  1-3: solve_ndisj.
  1: subst; iFrame "∗ #".
  iSplit.
  {
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iIntros "Hmapstos".
    iModIntro.
    subst.
    iDestruct "Hmapstos" as "[Hmapstos|Hmapstos]".
    - iApply "HΦc".
      iRight.
      iApply (big_sepM_mono with "Hmapstos").
      iIntros (a obj Hin) "(?&?)".
      iFrame.
    - iApply "HΦc".
      iLeft.
      iApply (big_sepM_mono with "Hmapstos").
      iIntros (a obj Hin) "(?&?)".
      iFrame.
  }
  iIntros (?) "!> Hmapstos".
  iApply "HΦ".
  iFrame (Hmt_dom) "Hlocks".
  iDestruct (big_sepM_sep with "Hmapstos") as "[Htokens Hmapstos]".
  iFrame "Hmapstos".
  iDestruct (big_sepM_dom with "Htokens") as "Htokens".
  remember (filter_addr_set_by_blk _ _) as locked_addrs.
  replace ([∗ set] _ ∈ locked_addrs, _)%I with (
    [∗ set] a ∈
      locked_addrs ∖
        dom (gset addr) mt_committed ∪
        dom (gset addr) mt_committed,
      modify_token γ a
  )%I by (f_equal; rewrite difference_union_L; set_solver).
  rewrite Hdom.
  iApply (big_sepS_union with "[Hunlifted_mapstos Htokens]");
    first by set_solver.
  replace (dom _ (if ok then _ else _)) with (dom (gset addr) mt_modified);
    last (destruct ok; rewrite ?Hdom //).
  iFrame.
Qed.

Theorem wp_TwoPhase__readBufNoAcquire (l: loc) γ γtxn dinit objs_dom mt_committed a obj (sz: u64) :
  is_Some (mt_committed !! a) →
  bufSz (objKind obj) = int.nat sz →
  {{{
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit objs_dom mt_committed ∗
    "Hmapsto" ∷ buftxn_maps_to γtxn a obj
  }}}
    TwoPhase__readBufNoAcquire #l (addr2val a) #sz
  {{{
    data_s data, RET (slice_val data_s);
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit objs_dom mt_committed ∗
    "Hmapsto" ∷ buftxn_maps_to γtxn a obj ∗
    "Hdata_s" ∷ is_slice data_s byteT 1 data ∗
    "%Hdata" ∷ ⌜data_has_obj data a obj⌝
  }}}.
Proof.
  iIntros (Hlifted Hsz).
  wp_start.
  wp_call.
  iNamed "Htwophase".
  iNamed "Hbuftxn".
  wp_loadField.
  wp_apply (wp_BufTxn__ReadBuf with "[$Hbuftxn_mem $Hmapsto]");
    first by assumption.
  iIntros (??) "[Hbuf Hrestore]".
  wp_apply (wp_buf_loadField_data with "Hbuf").
  iIntros (?) "[Hbuf_data Hbuf_without_data]".
  iDestruct (is_buf_data_has_obj with "Hbuf_data")
    as (data) "[Hslice %Hdata]".
  wp_apply (util_proof.wp_CloneByteSlice with "Hslice").
  iIntros (s') "[Hslice Hclone]".
  iDestruct (data_has_obj_to_buf_data with "Hslice") as "Hbuf_data";
    first by eassumption.
  iMod ("Hrestore" with "[Hbuf_data Hbuf_without_data] []")
    as "[Hbuftxn_mem Hmapsto]";
    [by (iExists _; iFrame)|by intuition|].
  wp_pures.
  iApply "HΦ".
  iFrame (Hdata) "Hclone".
  destruct obj.
  simpl.
  iFrame "Hmapsto".
  iExists _.
  iFrame (Hmt_dom) "Hlocks Hlocked_mapstos".
  iExists _, _.
  iFrame.
Qed.

Theorem wp_TwoPhase__ReadBuf_raw (l: loc) γ γtxn dinit objs_dom mt_committed a obj (sz: u64) :
  a ∈ objs_dom →
  bufSz (objKind obj) = int.nat sz →
  {{{
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit objs_dom mt_committed ∗
    "Hmapsto" ∷ (
      match mt_committed !! a with
      | Some _ => buftxn_maps_to γtxn a obj
      | None => durable_mapsto γ a obj
      end
    )
  }}}
    TwoPhase__ReadBuf #l (addr2val a) #sz
  {{{
    data_s data, RET (slice_val data_s);
    let mt_committed' := (
      match mt_committed !! a with
      | Some _ => mt_committed
      | None => <[a:=obj]>mt_committed
      end
    ) in
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit objs_dom mt_committed' ∗
    "Hmapsto" ∷ buftxn_maps_to γtxn a obj ∗
    "Hdata_s" ∷ is_slice data_s byteT 1 data ∗
    "%Hdata" ∷ ⌜data_has_obj data a obj⌝
  }}}.
Proof.
  iIntros (Hwf Hsz).
  wp_start.
  wp_call.
  wp_apply (wp_TwoPhase__Acquire_lift with "[$Htwophase $Hmapsto]");
    first by assumption.
  iNamed 1.
  wp_apply (wp_TwoPhase__readBufNoAcquire with "[
    $Htwophase $Hmapsto
  ]"); [|assumption|].
  {
    destruct (mt_committed !! a) as [obj'|] eqn:Hlookup_old;
      first by (rewrite Hlookup_old; eauto).
    rewrite lookup_insert; eauto.
  }
  iIntros (??).
  iNamed 1.
  iApply "HΦ".
  iFrame "∗ %".
Qed.

Theorem wp_TwoPhase__OverWrite_raw l γ γtxn dinit objs_dom mt_committed a (sz: u64) data_s data obj obj' :
  bufSz (objKind obj') = int.nat sz →
  data_has_obj data a obj' →
  objKind obj' = objKind obj →
  a ∈ objs_dom →
  {{{
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit objs_dom mt_committed ∗
    "Hdata_s" ∷ is_slice_small data_s byteT 1 data ∗
    "Hmapsto" ∷ (
      match mt_committed !! a with
      | Some _ => buftxn_maps_to γtxn a obj
      | None => durable_mapsto γ a obj
      end
    )
  }}}
    TwoPhase__OverWrite #l (addr2val a) #sz (slice_val data_s)
  {{{
    RET #();
    let mt_committed' := (
      match mt_committed !! a with
      | Some _ => mt_committed
      | None => <[a:=obj]>mt_committed
      end
    ) in
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit objs_dom mt_committed' ∗
    "Hmapsto" ∷ buftxn_maps_to γtxn a obj'
  }}}.
Proof.
  iIntros (Hsz Hdata Hkind Hwf).
  wp_start.
  wp_call.
  wp_apply (wp_TwoPhase__Acquire_lift with "[$Htwophase $Hmapsto]");
    first by assumption.
  iNamed 1.
  iNamed "Htwophase".
  iNamed "Hbuftxn".
  wp_loadField.
  wp_apply (wp_BufTxn__OverWrite with "[$Hbuftxn_mem Hmapsto Hdata_s]").
  1-3: by eassumption.
  1: by iFrame.
  iIntros "[Hbuftxn_mem Hmapsto]".

  iApply "HΦ".
  iFrame "Hmapsto".
  iExists _.
  iFrame (Hmt_dom) "Hlocks Hlocked_mapstos".
  iExists _, _.
  iFrame.
Qed.
