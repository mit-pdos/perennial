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

Section proof.
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
  apply map_filter_ext.
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
Implicit Types tracked_addrs : gset addr.
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
  ex_mapsto is the upper layer ex_mapsto fact used for unification,
  in our case jrnl_mapsto
*)

Definition twophase_crash_inv ex_mapsto k γ a obj : iProp Σ :=
  na_crash_inv
    (S k)
    (
      "Hex_mapsto" ∷ ex_mapsto a obj ∗
      "Hdurable" ∷ durable_mapsto γ a obj
    )%I
    (∃ obj',
      "Hex_mapsto" ∷ ex_mapsto a obj' ∗
      "Hdurable" ∷ durable_mapsto γ a obj'
    )%I.

Definition twophase_linv ex_mapsto k γ a : iProp Σ :=
  ∃ obj,
    "Htoken" ∷ modify_token γ a ∗
    "Hcrash_inv" ∷ twophase_crash_inv ex_mapsto k γ a obj.

Definition twophase_linv_flat ex_mapsto k tracked_addrs γ flat_addr : iProp Σ :=
  ∃ a,
    "Hlinv" ∷ twophase_linv ex_mapsto k γ a ∗
    "%Ha" ∷ ⌜addr2flat a = flat_addr⌝ ∗
    "%Ha_tracked" ∷ ⌜a ∈ tracked_addrs⌝.

Definition is_twophase_locks_valid tracked_addrs locks_held : iProp Σ :=
  "%Hlocks_held_NoDup" ∷ ⌜NoDup locks_held⌝ ∗
  "%Hlocks_tracked" ∷ ⌜
    (list_to_set locks_held: gset u64) ⊆
    set_map addr2flat tracked_addrs
  ⌝ ∗
  "%Htracked_valid" ∷ ⌜set_Forall valid_addr tracked_addrs⌝.

Definition is_twophase_locks (l: loc) γ ex_mapsto k tracked_addrs (locks_held: list u64) : iProp Σ :=
  ∃ (locksl: loc) acquired_s ghs,
    "Htwophase.locks" ∷ l ↦[TwoPhase.S :: "locks"] #locksl ∗
    "Htwophase.acquired" ∷
      l ↦[TwoPhase.S :: "acquired"] (slice_val acquired_s) ∗
    "Hacquired_s" ∷ is_slice acquired_s uint64T 1 locks_held ∗
    "Hlockeds" ∷ ([∗ list] flat_a ∈ locks_held,
      "Hlocked" ∷ Locked ghs flat_a
    ) ∗
    "#HlockMap" ∷ is_lockMap locksl ghs (set_map addr2flat tracked_addrs)
      (twophase_linv_flat ex_mapsto k tracked_addrs γ) ∗
    "#Hlocks_valid" ∷ is_twophase_locks_valid tracked_addrs locks_held.

Definition is_twophase_buftxn (l: loc) γ dinit mt_changed : iProp Σ :=
  ∃ (buftxnl: loc) γtxn γdurable,
    "Htwophase.buftxn" ∷ l ↦[TwoPhase.S :: "buftxn"] #buftxnl ∗
    "Hbuftxn_mem" ∷ is_buftxn_mem
      Nbuftxn buftxnl γ dinit γtxn γdurable ∗
    "Hbuftxn_durable_frag" ∷ map_ctx
      γdurable (1/2) (committed <$> mt_changed) ∗
    "Hbuftxn_maps_tos" ∷ ([∗ map] a ↦ vobj ∈ mt_changed,
      buftxn_maps_to γtxn a (modified vobj)
    ).

Definition is_twophase_raw l γ dinit ex_mapsto k tracked_addrs mt_changed : iProp Σ :=
  ∃ locks_held,
    "Hlocks" ∷ is_twophase_locks l γ ex_mapsto k tracked_addrs locks_held ∗
    "Hbuftxn" ∷ is_twophase_buftxn l γ dinit mt_changed ∗
    "Hcrash_invs" ∷ (
      [∗ map] a ↦ vobj ∈ mt_changed,
        "Hcrash_inv" ∷ twophase_crash_inv ex_mapsto k γ a (committed vobj)
    ) ∗
    "%Hmt_dom" ∷ ⌜
      set_map addr2flat (dom (gset addr) mt_changed) =
      (list_to_set locks_held: gset u64)
    ⌝ ∗
    "%Hmt_tracked" ∷ ⌜dom (gset addr) mt_changed ⊆ tracked_addrs⌝
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

Theorem wp_TwoPhase__Begin_raw (txnl locksl: loc) γ dinit k ex_mapsto ghs tracked_addrs :
  set_Forall valid_addr tracked_addrs →
  {{{
    "#Htxn" ∷ (
      invariant.is_txn txnl γ.(buftxn_txn_names) dinit ∗
      is_txn_system Nbuftxn γ
    ) ∗
    "#HlockMap" ∷ is_lockMap locksl ghs (set_map addr2flat tracked_addrs)
      (twophase_linv_flat ex_mapsto k tracked_addrs γ)
  }}}
    Begin #txnl #locksl
  {{{
    (l : loc), RET #l;
      "Htwophase_raw" ∷
        is_twophase_raw l γ dinit ex_mapsto k tracked_addrs ∅
  }}}.
Proof.
  intros Htracked_addrs_wf.
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
    rewrite big_sepL_nil.
    iFrame "∗ #".
    iPureIntro.
    rewrite list_to_set_nil.
    split; first by apply NoDup_nil_2.
    set_solver.
  }
  iSplitL.
  {
    iExists _, _, _.
    rewrite fmap_empty big_sepM_empty.
    iFrame.
  }
  rewrite big_sepM_empty
    dom_empty_L list_to_set_nil set_map_empty //.
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

Theorem is_twophase_locks_get_locks_valid (l: loc) γ ex_mapsto k tracked_addrs locks_held :
  "Hlocks" ∷ is_twophase_locks l γ ex_mapsto k tracked_addrs locks_held
  -∗
  "#Hlocks_valid" ∷ is_twophase_locks_valid tracked_addrs locks_held.
Proof.
  iNamed 1.
  iNamed "Hlocks".
  iFrame "#".
Qed.

Theorem wp_TwoPhase__acquireNoCheck (l: loc) γ ex_mapsto k tracked_addrs locks_held (a: addr):
  a ∈ tracked_addrs →
  addr2flat a ∉ locks_held →
  {{{
    "Hlocks" ∷ is_twophase_locks l γ ex_mapsto k tracked_addrs locks_held
  }}}
    TwoPhase__acquireNoCheck #l (addr2val a)
  {{{
    RET #();
    "Hlocks" ∷ is_twophase_locks
      l γ ex_mapsto k tracked_addrs (locks_held ++ [addr2flat a]) ∗
    "Hlinv" ∷ twophase_linv ex_mapsto k γ a
  }}}.
Proof.
  intros Haddr_wf Haddr_not_locked.
  wp_start.
  wp_call.
  iNamed "Hlocks".
  iNamed "Hlocks_valid".
  wp_apply wp_Addr__Flatid;
    first by (iPureIntro; apply (Htracked_valid a Haddr_wf)).
  iIntros (flat_addr) "->".
  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$HlockMap]");
    first by (iPureIntro; apply elem_of_map_2; assumption).
  iIntros "[Hlinv Hlocked]".
  wp_loadField.
  wp_apply (wp_SliceAppend (V:=u64) with "[$Hacquired_s]").
  iIntros (acquired_s') "Hacquired_s".
  wp_apply (wp_storeField with "Htwophase.acquired").
  1: rewrite /field_ty /=; val_ty.
  iIntros "Htwophase.acquired".

  iApply "HΦ".
  iDestruct "Hlinv" as (a') "Hlinv".
  iNamed "Hlinv".
  apply addr2flat_eq in Ha.
  2-3: apply Htracked_valid; assumption.
  subst a'.
  iFrame "Hlinv".
  iExists _, _, _.
  iFrame "∗ #".
  iSplit; first by iApply big_sepL_nil.
  iPureIntro.
  split.
  {
    apply NoDup_app.
    split; first by assumption.
    split.
    2: apply NoDup_singleton.
    intros addr' Hin1 Hin2.
    apply elem_of_list_singleton in Hin2.
    subst addr'.
    contradiction.
  }
  split; last by assumption.
  rewrite list_to_set_app list_to_set_singleton.
  apply union_least; first by assumption.
  apply elem_of_subseteq_singleton.
  apply elem_of_map_2.
  assumption.
Qed.

Theorem wp_TwoPhase__isAlreadyAcquired (l: loc) γ ex_mapsto k tracked_addrs locks_held a :
  a ∈ tracked_addrs →
  {{{
    "Hlocks" ∷ is_twophase_locks l γ ex_mapsto k tracked_addrs locks_held
  }}}
    TwoPhase__isAlreadyAcquired #l (addr2val a)
  {{{
    RET #(bool_decide (addr2flat a ∈ locks_held));
    "Hlocks" ∷ is_twophase_locks l γ ex_mapsto k tracked_addrs locks_held
  }}}.
Proof.
  intros Haddr_wf.
  wp_start.
  wp_call.
  iDestruct (is_twophase_locks_get_locks_valid with "Hlocks")
    as "#Hlocks_valid".
  iNamed.
  iNamed "Hlocks_valid".
  wp_apply wp_Addr__Flatid;
    first by (iPureIntro; apply (Htracked_valid a Haddr_wf)).
  iIntros (flat_addr) "->".
  wp_apply wp_ref_to; first by auto.
  iIntros (already_acquired_l) "Halready_acquired_l".
  iNamed "Hlocks".
  wp_loadField.
  iDestruct (is_slice_small_read with "Hacquired_s") as "[Hacquired_s Hacquired_s_wrap]".
  wp_apply (wp_forSlicePrefix (λ done todo,
    let already_acquired_val := bool_decide (addr2flat a ∈ done) in
    "Halready_acquired_l" ∷
      already_acquired_l ↦[boolT] #already_acquired_val
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
    destruct (decide (addr2flat a ∈ done)).
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

Theorem wp_TwoPhase__Acquire (l: loc) γ ex_mapsto k tracked_addrs locks_held (a: addr):
  a ∈ tracked_addrs →
  {{{
    "Hlocks" ∷ is_twophase_locks l γ ex_mapsto k tracked_addrs locks_held
  }}}
    TwoPhase__Acquire #l (addr2val a)
  {{{
    RET #();
    let a_locked := addr2flat a ∈ locks_held in
    "Hlocks" ∷ is_twophase_locks l γ ex_mapsto k tracked_addrs (
      if decide (a_locked) then locks_held
      else locks_held ++ [addr2flat a]
    ) ∗
    "Hlinv" ∷ (
      if decide (a_locked)
      then True
      else twophase_linv ex_mapsto k γ a
    )
  }}}.
Proof.
  intros Hwf.
  wp_start.
  wp_call.
  wp_apply (wp_TwoPhase__isAlreadyAcquired with "Hlocks");
    first by assumption.
  iNamed 1.
  wp_if_destruct.
  2: {
    iApply "HΦ".
    rewrite !(decide_True _ _ Heqb).
    iFrame.
  }
  wp_apply (wp_TwoPhase__acquireNoCheck with "Hlocks").
  1-2: assumption.
  iNamed 1.
  iApply "HΦ".
  rewrite !(decide_False _ _ Heqb).
  iFrame.
Qed.

(*
Lemma twophase_locked_mapstos_add γ locked_blknos mt_committed tracked_addrs blkno :
  dom (gset addr) mt_committed ⊆
    filter_addr_set_by_blk locked_blknos tracked_addrs →
  blkno ∉ locked_blknos →
  "Hmapstos" ∷ twophase_locked_mapstos
    γ (filter_addr_set_by_blk locked_blknos tracked_addrs) mt_committed -∗
  "Hlinv" ∷ twophase_linv γ tracked_addrs blkno -∗
    "Hmapstos" ∷ twophase_locked_mapstos
      γ (filter_addr_set_by_blk (locked_blknos ∪ {[blkno]}) tracked_addrs)
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

Theorem wp_TwoPhase__Acquire_merge (l: loc) γ tracked_addrs locks_held mt_committed (blkno: u64):
  dom (gset addr) mt_committed ⊆
    filter_addr_set_by_blk (list_to_set locks_held) tracked_addrs →
  blkno ∈ get_addr_set_blknos tracked_addrs →
  {{{
    "Hlocks" ∷ is_twophase_locks l γ tracked_addrs locks_held ∗
    "Hmapstos" ∷ twophase_locked_mapstos
      γ (filter_addr_set_by_blk
      (list_to_set locks_held) tracked_addrs) mt_committed
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
    "Hlocks" ∷ is_twophase_locks l γ tracked_addrs locks_held' ∗
    "Hmapstos" ∷ twophase_locked_mapstos
      γ (filter_addr_set_by_blk
      (list_to_set locks_held') tracked_addrs) mt_committed
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
 *)

Lemma is_twophase_buftxn_not_in_map l γ dinit mt_changed a obj :
  "Hbuftxn" ∷ is_twophase_buftxn l γ dinit mt_changed -∗
  "Hold_vals" ∷ (
    [∗ map] a ↦ vobj ∈ mt_changed,
      "Hdurable_mapsto" ∷ durable_mapsto γ a (committed vobj)
  ) -∗
  "Hdurable_mapsto" ∷ durable_mapsto γ a obj -∗
  ⌜mt_changed !! a = None⌝.
Proof.
  iIntros "???".
  iNamed.
  iNamed "Hbuftxn".
  iNamed "Hbuftxn_mem".
  iDestruct (map_ctx_agree with "Hbuftxn_durable_frag Hdurable") as %<-.
  iDestruct (
    is_buftxn_durable_not_in_map with
    "Hdurable_mapsto [Hbuftxn_durable_frag Hold_vals] Hdurable"
  ) as "%Hnotin".
  2: {
    iPureIntro.
    rewrite lookup_fmap in Hnotin.
    apply fmap_None in Hnotin.
    assumption.
  }
  iExists _.
  iFrame.
  iSplitL; first by (iApply big_sepM_fmap; iFrame).
  iModIntro.
  iIntros (?) "Hmapstos".
  trivial.
Qed.

(*
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
 *)

Theorem twophase_lift l γ dinit mt_changed ex_mapsto `{!∀ a obj, Timeless (ex_mapsto a obj)} k a :
  mt_changed !! a = None →
  "Hbuftxn" ∷ is_twophase_buftxn l γ dinit mt_changed -∗
  "Hcrash_invs" ∷ (
    [∗ map] a' ↦ vobj' ∈ mt_changed,
      "Hcrash_inv" ∷ twophase_crash_inv ex_mapsto k γ a' (committed vobj')
  ) -∗
  "Hlinv" ∷ twophase_linv ex_mapsto k γ a
  -∗ |NC={⊤}=> (∃ obj,
    let mt_changed' := <[a:=object_to_versioned obj]>mt_changed in
    "Hbuftxn" ∷ is_twophase_buftxn l γ dinit mt_changed' ∗
    "Hcrash_invs" ∷ (
      [∗ map] a' ↦ vobj' ∈ mt_changed',
        "Hcrash_inv" ∷ twophase_crash_inv ex_mapsto k γ a' (committed vobj')
    )
  ).
Proof.
  iIntros (Hnotin) "???".
  iNamed.
  iNamed "Hlinv".
  iNamed "Hbuftxn".
  iMod (
    na_crash_inv_open_modify_ncfupd _ _ _ _
    (
      "Hex_mapsto" ∷ ex_mapsto a obj ∗
      "Hdurable" ∷ durable_mapsto γ a obj
    )%I
    (
      "Hbuftxn_mem" ∷ is_buftxn_mem
        Nbuftxn buftxnl γ dinit γtxn γdurable ∗
      "Hbuftxn_durable_frag" ∷ map_ctx
        γdurable (1/2) (<[a:=obj]>(committed <$> mt_changed)) ∗
      "Hbuftxn_maps_to" ∷ buftxn_maps_to γtxn a obj
    )%I
    with "Hcrash_inv [Htoken Hbuftxn_mem Hbuftxn_durable_frag]")
    as "[(?&?&?) Hcrash_inv]".
  {
    iIntros "HQ".
    iMod "HQ" as "[? ?]".
    iNamed.
    iMod (lift_into_txn' with "
      Hbuftxn_mem Hbuftxn_durable_frag [$Hdurable $Htoken]
    ") as "(?&?&?&?&?)".
    1-3: solve_ndisj.
    iNamed.
    iFrame.
    iIntros "!> !> HQ'".
    iMod "HQ'" as "[? ?]".
    iNamed.
    iIntros "!> !>".
    iExists _.
    iFrame.
  }
  iNamed.
  iModIntro.
  iExists _.
  iSplitR "Hcrash_inv Hcrash_invs".
  {
    iExists _, _, _.
    rewrite fmap_insert /committed committed_to_versioned.
    iFrame "Hbuftxn_mem Htwophase.buftxn Hbuftxn_durable_frag".
    iApply big_sepM_insert; first by assumption.
    rewrite /modified modified_to_versioned.
    iFrame.
  }
  iApply big_sepM_insert; first by assumption.
  rewrite /committed committed_to_versioned.
  iFrame.
Qed.

Theorem twophase_lift_if_needed l γ dinit mt_changed ex_mapsto `{!∀ a obj, Timeless (ex_mapsto a obj)} k a :
  "Hbuftxn" ∷ is_twophase_buftxn l γ dinit mt_changed -∗
  "Hcrash_invs" ∷ (
    [∗ map] a' ↦ vobj' ∈ mt_changed,
      "Hcrash_inv" ∷ twophase_crash_inv ex_mapsto k γ a' (committed vobj')
  ) -∗
  "Hlinv" ∷ (
    match mt_changed !! a with
    | Some _ => True
    | None => "Hlinv" ∷ twophase_linv ex_mapsto k γ a
    end
  )
  -∗ |NC={⊤}=> (∃ obj,
    let mt_changed' := (
      match mt_changed !! a with
      | Some _ => mt_changed
      | None => <[a:=object_to_versioned obj]>mt_changed
      end
    ) in
    "Hbuftxn" ∷ is_twophase_buftxn l γ dinit mt_changed' ∗
    "Hcrash_invs" ∷ (
      [∗ map] a' ↦ vobj' ∈ mt_changed',
        "Hcrash_inv" ∷ twophase_crash_inv ex_mapsto k γ a' (committed vobj')
    )
  ).
Proof.
  iIntros "???".
  iNamed.
  destruct (mt_changed !! a) as [vobj|] eqn:Hacc;
    first by (iExists (committed vobj); iModIntro; iFrame).
  iMod (twophase_lift with "Hbuftxn Hcrash_invs Hlinv")
    as (?) "(?&?)"; first by assumption.
  iNamed.
  iModIntro.
  iExists _.
  iFrame.
Qed.

Lemma decide_is_Some {A B} (x: option A) (P Q: B) :
  (if decide (is_Some x) then P else Q) =
  (match x with | Some _ => P | None => Q end).
Proof.
  destruct x; rewrite //=.
Qed.

Theorem wp_TwoPhase__Acquire_lift (l: loc) γ dinit ex_mapsto `{!∀ a obj, Timeless (ex_mapsto a obj)} k tracked_addrs mt_changed a:
  a ∈ tracked_addrs →
  {{{
    "Htwophase" ∷ is_twophase_raw
      l γ dinit ex_mapsto k tracked_addrs mt_changed
  }}}
    TwoPhase__Acquire #l (addr2val a)
  {{{
    obj, RET #();
    let mt_changed' :=
      match mt_changed !! a with
      | Some _ => mt_changed
      | None => <[a:=object_to_versioned obj]>mt_changed
      end
    in
    "Htwophase" ∷ is_twophase_raw
      l γ dinit ex_mapsto k tracked_addrs mt_changed'
  }}}.
Proof.
  iIntros (Hwf).
  wp_start.
  iNamed "Htwophase".
  iDestruct (is_twophase_locks_get_locks_valid with "Hlocks")
    as "#Hlocks_valid".
  iNamed.
  iNamed "Hlocks_valid".
  iApply wp_ncfupd.
  wp_apply (wp_TwoPhase__Acquire with "Hlocks");
    first by assumption.
  iNamed 1.
  assert (addr2flat a ∈ locks_held ↔ is_Some (mt_changed !! a))
    as Hlocked_iff.
  {
    split.
    - intros Hlocked.
      apply elem_of_dom.
      assert (addr2flat a ∈ (list_to_set locks_held: gset u64))
        as Hlocked'
        by (apply elem_of_list_to_set; assumption).
      rewrite -Hmt_dom in Hlocked'.
      apply elem_of_map_1 in Hlocked'.
      destruct Hlocked' as (a'&Ha_eq&Ha').
      pose proof ((iffLR (elem_of_subseteq _ _)) Hmt_tracked _ Ha')
        as Ha'_tracked.
      apply Htracked_valid in Ha'_tracked.
      apply Htracked_valid in Hwf.
      apply addr2flat_eq in Ha_eq;
        [subst a'; assumption|assumption|assumption].
    - intros Hin.
      apply elem_of_dom in Hin.
      apply (elem_of_map_2 addr2flat) in Hin.
      rewrite Hmt_dom in Hin.
      apply elem_of_list_to_set in Hin.
      assumption.
  }
  rewrite !(decide_iff _ _ _ _ Hlocked_iff) !decide_is_Some.
  iMod (twophase_lift_if_needed with "Hbuftxn Hcrash_invs Hlinv")
    as (?) "(?&?)".
  iNamed.
  iModIntro.

  iApply "HΦ".
  iExists _.
  iFrame.
  iPureIntro.
  destruct (mt_changed !! a) as [old_vobj|] eqn:Hlookup_old;
    first by (split; assumption).
  rewrite dom_insert_L.
  split;
    first by rewrite set_map_union_L
    list_to_set_app_L union_comm_L
    set_map_singleton_L (leibniz_equiv _ _ (list_to_set_singleton _))
    Hmt_dom //.
  apply union_least; last by assumption.
  apply elem_of_subseteq_singleton.
  assumption.
Qed.

Theorem wp_TwoPhase__Release (l: loc) γ ex_mapsto k locks_held tracked_addrs flat_a :
  {{{
    "Hlocks" ∷ is_twophase_locks
      l γ ex_mapsto k tracked_addrs (locks_held ++ [flat_a]) ∗
    "Hlinv" ∷ twophase_linv_flat ex_mapsto k tracked_addrs γ flat_a
  }}}
    TwoPhase__Release #l
  {{{
    RET #();
    "Hlocks" ∷ is_twophase_locks l γ ex_mapsto k tracked_addrs locks_held
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
  assert (
    (locks_held ++ [flat_a]) !! (length locks_held) = Some flat_a
  ) as Hlockeds_acc.
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
    apply Hlockeds_acc.
  }
  iIntros "Hacquired_s".
  iApply "Hacquired_s_wrap" in "Hacquired_s".
  wp_loadField.
  iDestruct (big_sepL_app with "Hlockeds")
    as "[Hlockeds Hlocked]".
  rewrite big_sepL_singleton.
  iNamed.
  wp_apply (wp_LockMap__Release with "[$HlockMap $Hlocked Hlinv]").
  {
    iFrame.
    (*
    iPureIntro.
    split; first by reflexivity.
    rewrite list_to_set_app_L in Hlocks_tracked.
    apply union_subseteq in Hlocks_tracked.
    destruct Hlocks_tracked as [_ Ha_tracked].
    rewrite (leibniz_equiv _ _ (list_to_set_singleton _)) in Ha_tracked.
    apply elem_of_subseteq_singleton in Ha_tracked.
    apply elem_of_map_1 in Ha_tracked.
    destruct Ha_tracked as (a'&Ha'_eq&Ha'_in).
    specialize (Htracked_valid _ Ha'_in).
    apply addr2flat_eq in Ha'_eq.
    2-3: assumption.
    subst a'.
    assumption.
    *)
  }
  wp_loadField.
  wp_apply (wp_SliceTake uint64T); first by word.
  wp_apply (wp_storeField with "Htwophase.acquired");
    first by (rewrite /field_ty /=; val_ty).
  iIntros "Htwophase.acquired".

  iApply "HΦ".
  iExists _, _, _.
  iFrame "∗ #".
  iSplit.
  {
    iApply (is_slice_take_cap _ _ _ (word.sub acquired_s.(Slice.sz) 1)) in
      "Hacquired_s".
    1: rewrite fmap_length app_length /=; word.
    replace (int.nat (word.sub _ 1))
      with ((int.nat acquired_s.(Slice.sz)) - 1)%nat by word.
    rewrite -fmap_take -Hacquired_s_sz Nat.add_sub take_app.
    iFrame.
  }
  iNamed "Hlocks_valid".
  iPureIntro.
  apply NoDup_app in Hlocks_held_NoDup.
  rewrite list_to_set_app_L in Hlocks_tracked.
  apply union_subseteq in Hlocks_tracked.
  intuition.
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

Theorem wp_TwoPhase__ReleaseAll (l: loc) γ ex_mapsto k tracked_addrs locks_held :
  {{{
    "Hlocks" ∷ is_twophase_locks l γ ex_mapsto k tracked_addrs locks_held ∗
    "Hlinvs" ∷ ([∗ list] flat_a ∈ locks_held, (
      "Hlinv" ∷ twophase_linv_flat ex_mapsto k tracked_addrs γ flat_a
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
        l γ ex_mapsto k tracked_addrs (take i locks_held) ∗
      "Hlinvs" ∷ ([∗ list] blkno ∈ take i locks_held, (
        "Hlinv" ∷ twophase_linv_flat ex_mapsto k tracked_addrs γ blkno
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
    }

    iAssert (
      is_twophase_locks l γ ex_mapsto k tracked_addrs (take i locks_held)
    ) with
        "[Htwophase.locks Htwophase.acquired
        Hacquired_s Hlockeds]"
      as "Htwophase";
      first by (iExists _, _, _; iFrame "∗ # %").
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

Lemma na_crash_inv_status_wand_sepM {A} `{Countable K} (m: gmap K A) k Q P :
  ([∗ map] i ↦ x ∈ m, na_crash_inv k (Q i x) (P i x)) -∗
  □ (
    ▷ ([∗ map] i ↦ x ∈ m, Q i x) -∗
   |C={⊤}_Init.Nat.pred k=>
    ▷ ([∗ map] i ↦ x ∈ m, P i x)
  ).
Proof.
  iInduction m as [|i x m] "IH" using map_ind;
    first by (iIntros "_ !> _ !>"; auto).
  iIntros "Hcrash_invs".
  iDestruct (big_sepM_insert with "Hcrash_invs")
    as "[Hcrash_inv Hcrash_invs]";
    first by assumption.
  iDestruct ("IH" with "Hcrash_invs") as "#Hstatuses".
  iDestruct (na_crash_inv_status_wand with "Hcrash_inv") as "#Hstatus".
  iIntros "!> HQs".
  iDestruct (big_sepM_insert with "HQs")
    as "[HQ HQs]"; first by assumption.
  iMod ("Hstatus" with "HQ") as "HP".
  iMod ("Hstatuses" with "HQs") as "HPs".
  iIntros "!> !>".
  iApply (big_sepM_insert with "[HP HPs]"); first by assumption.
  iFrame.
Qed.

Lemma wpc_na_crash_inv_open_modify_sepM {A} `{Countable K} Qnew  k k' k'' E1 e Φ Φc
      {HL: AbsLaterable Φc} Q P `{!∀ i x, Discretizable (Q i x)} (m: gmap K A) :
  (S k'') ≤ k' →
  (S k'') ≤ (S k) →
  S k ≤ k' →
  (* This assumption shouldn't be needed, but I (JDT) don't see how to prove it without it
     given some limitations of the current rules *)
  (□ (∀ i x, ⌜ m !! i = Some x ⌝ → ▷ Q i x -∗ |C={E1}_(S k)=> ▷ P i x)) -∗
  ([∗ map] i ↦ v ∈ m, na_crash_inv (S k') (Q i v) (P i v)) -∗
  (<disc> Φc ∧
   (▷ ([∗ map] i ↦ v ∈ m, Q i v) -∗
      WPC e @ (S k''); E1
      {{λ retv,
        ▷ ([∗ map] i ↦ v ∈ m, Qnew retv i v) ∗
          (* This assumption is weaker than the analogous version for 1 na_crash_inv, where we get |C={⊤}_k'
             given some limitations of the current rules *)
          ([∗ map] i ↦ v ∈ m, □ (▷ Qnew retv i v -∗ |C={E1}_k''=> ▷ P i v)) ∗
         (<disc> (|C={E1}_k''=> Φc) ∧ (([∗ map] i ↦ v ∈ m, na_crash_inv (S k') (Qnew retv i v) (P i v)) -∗ (Φ retv)))
      }}
      {{Φc ∗ ▷ ([∗ map] i ↦ v ∈ m, P i v)}}) -∗
  WPC e @ NotStuck; (S k); E1 {{ Φ }} {{ Φc }}).
Proof.
  iIntros (Hle1 Hle2 Hle3) "#Hstatuses Hcrash_invs Hwpc". iApply (wpc_idx_mono (S k'')); auto.
  iInduction m as [|i x m] "IH" using map_ind forall (k'' Φ Φc HL Hle1 Hle2 Hle3).
  {
    iDestruct "Hwpc" as "[_ Hwpc]".
    iDestruct ("Hwpc" with "[]") as "Hwpc"; first by auto.
    iDestruct (wpc_subscript_mono _ _ _ _ _ E1 with "Hwpc") as "Hwpc";
      [auto| |auto|].
    { reflexivity. }
    iApply (wpc_mono with "Hwpc").
    {
      iIntros (v) "/= (_&_&(_&Hcrash))".
      iDestruct ("Hcrash" with "[//]") as "$".
    }
    iIntros "[$ _]".
  }
  iDestruct (big_sepM_insert with "Hcrash_invs") as "(Hcrash_inv&Hcrash_invs)"; auto.
  iApply (
    wpc_na_crash_inv_open_modify' (λ v, Qnew v i x) _ _ _ (S k'')
    with "Hcrash_inv [Hwpc Hcrash_invs]"
  ).
  1-3: lia.
  iSplit.
  { iDestruct "Hwpc" as "[H _]". iModIntro. iFrame. }
  iIntros "HQ".
  iDestruct "Hwpc" as "[_ Hwpc]".
  iApply wpc_fupd.
  iApply ("IH" $! k'' _ (Φc ∗ ▷ P i x)%I with "[] [//] [//] [//] [] Hcrash_invs [HQ Hwpc]").
  { iPureIntro. apply _. }
  { iModIntro. iIntros. iApply "Hstatuses".
    - iPureIntro. rewrite lookup_insert_ne; congruence.
    - eauto. }
  {
    iSplit.
    { admit. }
    iIntros "HQs".
    iDestruct ("Hwpc" with "[HQs HQ]") as "Hwpc".
    {
      iApply big_sepM_insert; first by assumption.
      iFrame.
    }
    iApply (wpc_strong_mono with "Hwpc"); auto.
    iSplit.
    {
      iIntros (v) "(Hnew&Hstatuses'&HΦc)".
      iDestruct (big_sepM_insert with "Hstatuses'")
        as "[#Hstatus Hstatuses']"; first by assumption.
      iDestruct (big_sepM_insert with "Hnew") as "(HnewQ&HnewQs)"; first by assumption.
      iFrame "Hstatuses' HnewQs".
      iMod (fupd_later_to_disc with "HnewQ") as "HnewQ".
      iModIntro.
      iSplit.
      { iLeft in "HΦc". iModIntro.
        iMod "HΦc". iFrame. iApply "Hstatus". eauto.
      }
      iIntros "Hcrashes".
      iMod (own_disc_fupd_elim with "HnewQ") as "HnewQ".
      iFrame. iModIntro.
      iSplitL "".
      {
        iModIntro. iIntros. iSpecialize ("Hstatus" with "[$]").
        iMod (cfupd_weaken_all with "Hstatus"); auto.
        lia.
      }
      iIntros "Hcrash".
      iModIntro. iSplit.
      { iLeft in "HΦc". eauto. }
      iRight in "HΦc". iApply "HΦc".
      iApply big_sepM_insert; auto. iFrame.
    }
    iModIntro. iIntros "($&H)".
    iModIntro. iDestruct (big_sepM_insert with "H") as "($&$)". auto.
  }
Admitted.

(*
Lemma wpc_na_crash_inv_open_modify_sepM' {A} `{Countable K} Qnew s k k' k'' E1 e Φ Φc
      {HL: AbsLaterable Φc} Q P `{!∀ i x, Discretizable (Q i x)} (m: gmap K A) :
  k'' ≤ k' →
  k'' ≤ (S k) →
  S k ≤ k' →
  (* This assumption shouldn't be needed, but I (JDT) don't see how to prove it without it
     given some limitations of the current rules *)
  (□ (∀ i x, ⌜ m !! i = Some x ⌝ → ▷ Q i x -∗ |C={E1}_(S k)=> ▷ P i x)) -∗
  ([∗ map] i ↦ v ∈ m, na_crash_inv (S k') (Q i v) (P i v)) -∗
  (<disc> Φc ∧
   (▷ ([∗ map] i ↦ v ∈ m, Q i v) -∗
      WPC e @ k''; E1
      {{λ retv,
        ▷ ([∗ map] i ↦ v ∈ m, Qnew retv i v) ∗
          (* This assumption is weaker than the analogous version for 1 na_crash_inv, where we get |C={⊤}_k'
             given some limitations of the current rules *)
          ([∗ map] i ↦ v ∈ m, □ (▷ Qnew retv i v -∗ |C={E1}_k=> ▷ P i v)) ∗
          (([∗ map] i ↦ v ∈ m, na_crash_inv (S k') (Qnew retv i v) (P i v)) -∗ (<disc> Φc ∧ Φ retv))
      }}
      {{Φc ∗ ▷ ([∗ map] i ↦ v ∈ m, P i v)}}) -∗
  WPC e @ s; (S k); E1 {{ Φ }} {{ Φc }}).
Proof.
  iInduction m as [|i x m] "IH" using map_ind forall (k'').
  {
    iIntros (Hk''_leq_k' Hk''_leq_Sk HSk_leq_k') "_ _ Hwpc".
    iDestruct "Hwpc" as "[_ Hwpc]".
    iDestruct ("Hwpc" with "[]") as "Hwpc"; first by auto.
    iDestruct (wpc_subscript_mono _ s _ _ _ E1 with "Hwpc") as "Hwpc";
      [auto|apply Hk''_leq_Sk|auto|].
    iApply (wpc_mono with "Hwpc").
    {
      iIntros (v) "/= (_&_&Hcrash)".
      iDestruct ("Hcrash" with "[//]") as "[_ $]".
    }
    iIntros "[$ _]".
  }
  iIntros (Hk''_leq_k' Hk''_leq_Sk HSk_leq_k') "#Hstatuses Hcrash_invs Hwpc".
  iDestruct (big_sepM_insert with "Hcrash_invs")
    as "[Hcrash_inv Hcrash_invs]";
    first by assumption.
  iApply ("IH" $! (S k) with "[//] [//] [//] [] Hcrash_invs").
  { iModIntro. iIntros. iApply "Hstatuses".
    - iPureIntro. rewrite lookup_insert_ne; congruence.
    - eauto. }
  iSplit; first by iDestruct "Hwpc" as "[$ _]".
  iIntros "HsepM".
  iMod (fupd_later_to_disc with "HsepM") as "HsepM".
  iApply (wpc_strong_mono _ _ _ _ _ _ _ _ _
                          (Φc ∗ ▷ ([∗ map] i0↦v ∈ m, P i0 v ∨ Q i0 v))%I with "[-] []"); auto; last first.
  { iSplit.
   { iIntros (?) "H". iModIntro. iExact "H". }
   iModIntro. iIntros "($&HsepM)". iFrame.
   
setoid_rewrite big_sepM_later.
   iApply (big_sepM_impl_cfupd with "HsepM").
   iModIntro. iIntros (?? Hlookup) "[HP|HQ]".
   { iModIntro. eauto. }
   iApply "Hstatuses"; eauto.
   iPureIntro. rewrite lookup_insert_ne; congruence.
  }
  iApply (
    wpc_na_crash_inv_open_modify' _ _ _ _ k''
    with "Hcrash_inv [Hwpc HsepM]"
  ).
  1-3: assumption.
  iSplit.
  { iDestruct "Hwpc" as "[H _]". iModIntro. iFrame. iNext. iApply (big_sepM_mono with "HsepM"). eauto. }
  iIntros "HQ".
  iDestruct "Hwpc" as "[_ Hwpc]".
  iMod (own_disc_fupd_elim with "HsepM") as "HsepM".
  iDestruct ("Hwpc" with "[HsepM HQ]") as "Hwpc".
  {
    iApply big_sepM_insert; first by assumption.
    iFrame.
  }
  iApply (wpc_mono with "Hwpc").
  {
    iIntros (v) "/= (HQnew&#Hstatuses&Hcrash)".
    iDestruct (big_sepM_insert with "Hstatuses")
      as "[Hstatus Hstatuses']"; first by assumption.
    iDestruct (big_sepM_insert with "HQnew") as "[HQnew HQnews]";
      first by assumption.
    iFrame "HQnew".
    iSplit.
    {
      iIntros "!> HQnew".
      iApply "Hstatus" in "HQnew".
      iFrame.
      iMod (cfupd_weaken_all with "HQnew"); eauto.
    }
    iIntros "Hcrash_inv".
    iMod (fupd_later_to_disc with "HQnews") as "HQnews".
    iModIntro.
    iSplit.
    {
      iDestruct ("Hcrash" with "Hcrash
      iModIntro.
      admit.
    }
    iFrame "∗ #".
    iIntros "Hcrash_invs".
    iApply "Hcrash".
    iApply big_sepM_insert; first by assumption.
    iFrame.
  }
  iIntros "[HΦc HPs]".
  iFrame.
  iDestruct (big_sepM_insert with "HPs") as "[HP HPs]";
    first by assumption.
  iFrame.
  iNext.
  iApply (big_sepM_mono with "HPs"); eauto.
Admitted.
*)

Theorem wpc_TwoPhase__CommitNoRelease_raw l γ γ' dinit ex_mapsto k tracked_addrs mt_changed :
  {{{
    "Htwophase" ∷ is_twophase_raw
      l γ dinit ex_mapsto k tracked_addrs mt_changed ∗
    "#Htxn_cinv" ∷ txn_cinv Nbuftxn γ γ'
  }}}
    TwoPhase__CommitNoRelease #l @ S k; ⊤
  {{{
    (ok:bool) locks_held, RET #ok;
    let locked_blknos: gset u64 := list_to_set locks_held in
    let locked_addrs := filter_addr_set_by_blk locked_blknos tracked_addrs in
    "Hlocks" ∷ is_twophase_locks
      l γ ex_mapsto k tracked_addrs locks_held ∗
    "Hlinvs" ∷ (
      [∗ set] a ∈ locked_addrs,
        "Hlinv" ∷ twophase_linv ex_mapsto k γ a
    ) ∗
    "%Hmt_dom" ∷ ⌜dom (gset addr) mt_changed ⊆ locked_addrs⌝
  }}}
  {{{
    (
      "Hcrash_invs" ∷ [∗ map] a ↦ vobj ∈ mt_changed, (
        "Hex_mapsto" ∷ ex_mapsto a (committed vobj) ∗
        "Hdurable" ∷ durable_mapsto γ a (committed vobj)
        (* "Hcrash_inv" ∷ twophase_crash_inv ex_mapsto k γ a (committed vobj) *)
      )%I
    ) ∨ (
      "Hcrash_invs" ∷ [∗ map] a ↦ vobj ∈ mt_changed,
        "Hex_mapsto" ∷ ex_mapsto a (modified vobj) ∗
        "Hdurable" ∷ durable_mapsto γ a (modified vobj)
        (* "Hcrash_inv" ∷ twophase_crash_inv ex_mapsto k γ a (modified vobj) *)
    )
  }}}.
Proof.
  iIntros (Φ Φc) "(?&?) HΦ".
  iNamed.
  iNamed "Htwophase".
  iNamed "Hbuftxn".
  iApply wpc_cfupd.
  wpc_call.
  {
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    admit.
    (*
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
    *)
  }
  iCache (<disc> |C={⊤}_S k=> Φc)%I with "HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    admit.
    (*
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
    *)
  }
  wpc_frame_seq.
  wp_apply util_proof.wp_DPrintf.
  iNamed 1.
  wpc_pures.
  wpc_bind (struct.loadF _ _ _).
  wpc_frame "HΦ".
  wp_loadField.
  iNamed 1.
  wpc_apply (wpc_BufTxn__CommitWait' with "[
    $Hbuftxn_mem Hbuftxn_durable_frag Hbuftxn_maps_tos
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

Theorem wp_TwoPhase__readBufNoAcquire (l: loc) γ γtxn dinit tracked_addrs mt_committed a obj (sz: u64) :
  is_Some (mt_committed !! a) →
  bufSz (objKind obj) = int.nat sz →
  {{{
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit tracked_addrs mt_committed ∗
    "Hmapsto" ∷ buftxn_maps_to γtxn a obj
  }}}
    TwoPhase__readBufNoAcquire #l (addr2val a) #sz
  {{{
    data_s data, RET (slice_val data_s);
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit tracked_addrs mt_committed ∗
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

Theorem wp_TwoPhase__ReadBuf_raw (l: loc) γ γtxn dinit tracked_addrs mt_committed a obj (sz: u64) :
  a ∈ tracked_addrs →
  bufSz (objKind obj) = int.nat sz →
  {{{
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit tracked_addrs mt_committed ∗
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
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit tracked_addrs mt_committed' ∗
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

Theorem wp_TwoPhase__OverWrite_raw l γ γtxn dinit tracked_addrs mt_committed a (sz: u64) data_s data obj obj' :
  bufSz (objKind obj') = int.nat sz →
  data_has_obj data a obj' →
  objKind obj' = objKind obj →
  a ∈ tracked_addrs →
  {{{
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit tracked_addrs mt_committed ∗
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
    "Htwophase" ∷ is_twophase_raw l γ γtxn dinit tracked_addrs mt_committed' ∗
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

End proof.
