From RecordUpdate Require Import RecordUpdate.

From Perennial.algebra Require Import mono_nat.

From Goose.github_com.mit_pdos.go_journal Require Import wal.

From Perennial.algebra Require Import log_heap.
From Perennial.base_logic Require Import ghost_map.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import Transitions List range_set gset.

From Perennial.program_proof Require Import wal.abstraction wal.specs.
From Perennial.program_proof Require Import wal.heapspec_lib.
From Perennial.program_proof Require Import disk_prelude disk_lib.

Inductive heap_block :=
| HB (installed_block : Block) (blocks_since_install : list Block)
.

Class walheapG (Σ: gFunctors) : Set :=
  { walheap_u64_heap_block :> ghost_mapG Σ u64 heap_block;
    walheap_disk_txns :> ghost_varG Σ (gmap Z Block * list (u64 * list update.t));
    walheap_mono_nat :> mono_natG Σ;
    walheap_asyncCrashHeap :> ghost_varG Σ (async (gmap u64 Block));
    walheap_wal :> walG Σ
  }.

Definition walheapΣ : gFunctors :=
  #[ ghost_mapΣ u64 heap_block;
   ghost_varΣ (gmap Z Block * list (u64 * list update.t));
   mono_natΣ;
   ghost_varΣ (async (gmap u64 Block));
   walΣ ].

#[global]
Instance subG_walheapΣ Σ : subG walheapΣ Σ → walheapG Σ.
Proof. solve_inG. Qed.

Section heap.

Context `{!walheapG Σ}.
Context `{!heapGS Σ}.

(* Invariant and definitions *)

Definition wal_heap_inv_addr (ls : log_state.t) (a : u64) (b : heap_block) : iProp Σ :=
  ⌜ addr_wf a ls.(log_state.d) /\
    match b with
    | HB installed_block blocks_since_install =>
      ∃ (txn_id : nat),
      (* TODO: why is this _less than_ the installed lower-bound? *)
        (txn_id ≤ ls.(log_state.installed_lb))%nat ∧
        disk_at_txn_id txn_id ls !! uint.Z a = Some installed_block ∧
        updates_since txn_id a ls = blocks_since_install
    end ⌝.

Definition hb_latest_update (hb : heap_block) :=
  match hb with
  | HB installed bs => latest_update installed bs
  end.

Record wal_heap_gnames := {
  wal_heap_h : gname;
    (* current heap *)
  wal_heap_crash_heaps : gname;
    (* possible crashes; latest has the same contents as current heap *)
  wal_heap_durable_lb : gname;
  wal_heap_txns : gname;
  wal_heap_installed : gname;
  wal_heap_walnames : wal_names;
}.

Implicit Types (γ:wal_heap_gnames).

Global Instance wal_heap_gnames_eta : Settable _ :=
  settable! Build_wal_heap_gnames <wal_heap_h; wal_heap_crash_heaps; wal_heap_durable_lb;
                                   wal_heap_txns; wal_heap_installed; wal_heap_walnames>.

Definition wal_heap_inv_crash (crashheap : gmap u64 Block)
      (base : disk) (txns_prefix : list (u64 * list update.t)) : iProp Σ :=
  let txn_disk := apply_upds (txn_upds txns_prefix) base in
    "%Hcrashheap_contents" ∷ ⌜ ∀ (a : u64), crashheap !! a = txn_disk !! uint.Z a ⌝.

Definition wal_heap_inv_crashes (heaps : async (gmap u64 Block)) (ls : log_state.t) : iProp Σ :=
  "%Hcrashes_complete" ∷ ⌜ length (possible heaps) = length ls.(log_state.txns) ⌝ ∗
  "Hpossible_heaps" ∷ [∗ list] i ↦ asyncelem ∈ possible heaps,
    let txn_id := (1 + i)%nat in
    wal_heap_inv_crash asyncelem ls.(log_state.d) (take txn_id ls.(log_state.txns)).

Definition wal_heap_inv (γ : wal_heap_gnames) (ls : log_state.t) : iProp Σ :=
  ∃ (gh : gmap u64 heap_block) (crash_heaps : async (gmap u64 Block)),
    "%Hgh_complete" ∷ ⌜set_map uint.Z (dom gh) = dom ls.(log_state.d)⌝ ∗
    "Hctx" ∷ ghost_map_auth γ.(wal_heap_h) 1 gh ∗
    "Hgh" ∷ ( [∗ map] a ↦ b ∈ gh, wal_heap_inv_addr ls a b ) ∗
    "Htxns" ∷ ghost_var γ.(wal_heap_txns) (1/2) (ls.(log_state.d), ls.(log_state.txns)) ∗
    "Hinstalled" ∷ mono_nat_auth_own γ.(wal_heap_installed) 1 ls.(log_state.installed_lb) ∗
    "%Hwf" ∷ ⌜ wal_wf ls ⌝ ∗
    "Hcrash_heaps_own" ∷ ghost_var γ.(wal_heap_crash_heaps) (1/4) crash_heaps ∗
    "Hcrash_heaps" ∷ wal_heap_inv_crashes crash_heaps ls ∗
    "Hcrash_heaps_lb" ∷ mono_nat_auth_own γ.(wal_heap_durable_lb) 1 ls.(log_state.durable_lb).

Record locked_walheap := {
  locked_wh_σd : disk;
  locked_wh_σtxns : list (u64 * list update.t);
}.

Definition is_locked_walheap γ (lwh : locked_walheap) : iProp Σ :=
  ghost_var γ.(wal_heap_txns) (1/2) (lwh.(locked_wh_σd), lwh.(locked_wh_σtxns)).

Definition heapspec_init_ghost_state γ : iProp Σ :=
  "wal_heap_h" ∷ ghost_map_auth γ.(wal_heap_h) 1 (∅: gmap u64 heap_block) ∗
  "wal_heap_crash_heaps" ∷ ghost_var γ.(wal_heap_crash_heaps) 1 (Build_async (∅ : gmap u64 Block) []) ∗
  "wal_durable_lb" ∷ mono_nat_auth_own γ.(wal_heap_durable_lb) 1 0%nat ∗
  "wal_heap_txns" ∷ ghost_var γ.(wal_heap_txns) 1 (∅ : disk, @nil (u64 * list update.t)) ∗
  "wal_heap_installed" ∷ mono_nat_auth_own γ.(wal_heap_installed) 1 0%nat.

Lemma alloc_heapspec_init_ghost_state γwal_names :
  ⊢ |==> ∃ γ', "%Hwal_names" ∷ ⌜γ'.(wal_heap_walnames) = γwal_names⌝ ∗
               "Hinit" ∷ heapspec_init_ghost_state γ'.
Proof.
  iMod (ghost_map_alloc (∅: gmap u64 heap_block)) as (wal_heap_h) "[? _]".
  iMod (ghost_var_alloc (Build_async (∅ : gmap u64 Block) _)) as (wal_heap_crash_heaps) "?".
  iMod (mono_nat_own_alloc 0) as (wal_heap_durable_lb) "[? _]".
  iMod (ghost_var_alloc (∅ : disk, @nil (u64 * list update.t))) as (wal_heap_txns) "?".
  iMod (mono_nat_own_alloc 0) as (wal_heap_installed) "[? _]".

  iModIntro.
  iExists (Build_wal_heap_gnames _ _ _ _ _ _); simpl.
  rewrite /heapspec_init_ghost_state /named /=.
  iFrame.
  eauto.
Qed.

Lemma lookup_list_to_map_1 K `{Countable K} A (l: list (K * A)) k v :
  list_to_map (M:=gmap K A) l !! k = Some v → (k, v) ∈ l.
Proof.
  induction l; simpl.
  - inversion 1.
  - destruct (decide (k = a.1)); subst.
    + rewrite lookup_insert.
      inversion 1; subst.
      destruct a; simpl.
      constructor.
    + rewrite lookup_insert_ne //.
      intros Hin%IHl.
      apply elem_of_list_further; auto.
Qed.

Lemma lookup_list_to_map_2 K `{Countable K} A (l: list (K * A)) k v :
  NoDup l.*1 →
  (k, v) ∈ l → list_to_map (M:=gmap K A) l !! k = Some v.
Proof.
  intros Hnodup.
  induction l; simpl.
  - inversion 1.
  - rewrite fmap_cons in Hnodup.
    inversion Hnodup; subst; clear Hnodup.
    intros Hin.
    apply elem_of_cons in Hin as [<-|Hin]; simpl.
    + rewrite lookup_insert //.
    + rewrite lookup_insert_ne.
      { eauto. }
      intros <-.
      contradiction H2.
      apply elem_of_list_fmap.
      exists (a.1, v); auto.
Qed.

Lemma lookup_list_to_map K `{Countable K} A (l: list (K * A)) k v :
  NoDup l.*1 →
  list_to_map (M:=gmap K A) l !! k = Some v ↔ (k, v) ∈ l.
Proof.
  intros.
  split; eauto using lookup_list_to_map_1, lookup_list_to_map_2.
Qed.

Definition gh_heapblock0 (bs: list Block) : gmap u64 heap_block :=
  list_to_map (imap (λ (i:nat) b, (W64 (513 + i), HB b [])) bs).

Definition crash_heap0 (bs: list Block) : gmap u64 Block :=
  list_to_map (imap (λ (i:nat) b, (W64 (513 + i), b)) bs).

Lemma fst_imap {A B C} (f: nat → B) (g: A → C) (l: list A) :
  (imap (λ i x, (f i, g x)) l).*1 = f <$> seq 0 (length l).
Proof.
  rewrite fmap_imap.
  change (λ n, fst ∘ _) with (λ n (_:A), f n).
  cut (∀ i, imap (λ n _, f (i + n)%nat) l = f <$> seq i (length l)).
  { intros H; rewrite -H //. }
  induction l; simpl; auto; intros.
  replace (i + 0)%nat with i by lia.
  f_equal.
  fold (f <$> (seq (S i) (length l))).
  rewrite -IHl.
  apply imap_ext; intros; simpl.
  f_equal.
  lia.
Qed.

Lemma disk_index_nodup (bs: list Block) :
  NoDup (imap (λ (i : nat) (x : Block), (513 + i, x)) bs).*1.
Proof.
  rewrite fst_imap.
  apply NoDup_fmap.
  - intros i1 i2; lia.
  - apply NoDup_seq.
Qed.

Local Hint Resolve  disk_index_nodup : core.

Lemma lookup_init_disk (bs: list Block) (idx: nat) b :
  513 + Z.of_nat (length bs) < 2^64 →
  bs !! idx = Some b →
  list_to_map (M:=gmap _ _) (imap (λ (i0 : nat) (x0 : Block), (513 + i0, x0)) bs) !! uint.Z (W64 (513 + idx)) = Some b.
Proof.
  intros Hbound Hlookup.
  pose proof (lookup_lt_Some _ _ _ Hlookup) as Hlt.
  apply lookup_list_to_map_2; auto.
  apply elem_of_lookup_imap.
  exists idx, b; intuition eauto.
  f_equal.
  word.
Qed.

Lemma addr_wf_init:
  ∀ bs : list Block,
    513 + length bs < 2 ^ 64
    → ∀ (idx : nat) (b: Block),
      bs !! idx = Some b →
      addr_wf (513 + idx)
                (list_to_map (imap (λ (i : nat) (x : Block), (513 + i, x)) bs)).
Proof.
  intros bs Hbound idx b Hlookup.
  pose proof (lookup_lt_Some _ _ _ Hlookup) as Hlt.
  rewrite /addr_wf.
  split; [ word | ].
  exists b.
  erewrite lookup_init_disk; eauto.
Qed.

Lemma wal_heap_inv_init (γwalnames: wal_names) bs :
  513 + Z.of_nat (length bs) < 2^64 →
  ⊢ |==> ∃ γheapnames, "%Hwalnames" ∷ ⌜γheapnames.(wal_heap_walnames) = γwalnames⌝ ∗
                       "#Hheap_lb" ∷ mono_nat_lb_own γheapnames.(wal_heap_durable_lb) 0 ∗
                       "Hheap_inv" ∷ wal_heap_inv γheapnames (log_state0 bs) ∗
                       "wal_heap_locked" ∷ is_locked_walheap γheapnames
                         {| locked_wh_σd := (log_state0 bs).(log_state.d);
                            locked_wh_σtxns := [(W64 0, [])]|} ∗
                       "wal_heap_h_pointsto" ∷ ([∗ map] l↦v ∈ gh_heapblock0 bs,
                          l ↪[γheapnames.(wal_heap_h)] v) ∗
                       "wal_heap_crash_heaps" ∷ ghost_var γheapnames.(wal_heap_crash_heaps)
                              (3 / 4) (Build_async (crash_heap0 bs) [])
.
Proof.
  intros Hbound.
  rewrite /wal_heap_inv /is_locked_walheap.

  set (gh:= gh_heapblock0 bs).
  set (crash_heaps:=Build_async (crash_heap0 bs) []).

  iMod (alloc_heapspec_init_ghost_state γwalnames) as (γheapnames Heq1) "?"; iNamed.
  iNamed "Hinit".

  iMod (ghost_map_insert_big gh with "wal_heap_h") as "(wal_heap_h & wal_heap_pointsto)".
  { apply map_disjoint_empty_r. }
  rewrite right_id_L.
  iMod (ghost_var_update (list_to_map (imap (λ (i : nat) (x : Block), (513 + i, x)) bs), [(W64 0, [])])
       with "wal_heap_txns") as "[wal_heap_txns1 wal_heap_txns2]".
  iMod (ghost_var_update crash_heaps with "wal_heap_crash_heaps")
       as "H".
  iEval (rewrite -Qp.three_quarter_quarter) in "H".
  iDestruct "H" as "[wal_heap_crash_heaps1 wal_heap_crash_heaps2]".
  iDestruct (mono_nat_lb_own_get with "wal_durable_lb") as "#Hlb".

  iModIntro.

  simpl.
  iExists γheapnames; iFrame.
  iSplit; first by done.
  iFrame "Hlb".
  iSplit.
  { iPureIntro.
    rewrite dom_blocks_to_map_u64.
    rewrite dom_blocks_to_map_Z.
    apply set_eq; intros.
    rewrite elem_of_map.
    rewrite elem_of_list_to_set.
    rewrite elem_of_seqZ.
    split; intros.
    - destruct H as [i [-> Hlookup]].
      apply rangeSet_lookup in Hlookup; word.
    - exists (W64 x).
      rewrite -> rangeSet_lookup by word.
      word.
  }

  iSplit.
  { iPureIntro.
    simpl.
    apply map_Forall_lookup; intros.
    apply lookup_list_to_map_1 in H.
    apply elem_of_lookup_imap in H as (idx & b & [=] & Hlookup); subst.
    split.
    { eapply addr_wf_init; eauto. }
    exists 0%nat. split; [ lia | ].
    rewrite /disk_at_txn_id /=.
    erewrite lookup_init_disk; eauto.
  }
  iSplit.
  { iPureIntro.
    apply log_state0_wf. }
  rewrite /wal_heap_inv_crashes /=.
  iSplit; first by auto.
  rewrite /wal_heap_inv_crash.

  rewrite right_id.
  iPureIntro.
  intros.
  simpl.
  rewrite /crash_heap0.
  apply option_eq; intros.
  rewrite !lookup_list_to_map //.
  { rewrite !elem_of_lookup_imap.
    split.
    - destruct 1 as (i & b & [=] & Hlookup); subst.
      pose proof (lookup_lt_Some _ _ _ Hlookup).
      exists i, b; split; auto.
      f_equal.
      word.
    - destruct 1 as (i & b & [=] & Hlookup); subst.
      exists i, b; split; auto.
      f_equal.
      word. }
  rewrite fst_imap.
  apply NoDup_fmap_2_strong; auto using NoDup_seq.
  intros i1 i2.
  rewrite !elem_of_seq => Hi1 Hi2 /(f_equal uint.Z).
  word.
Qed.

Lemma wal_heap_inv_crashes_crash crash_heaps crash_txn ls ls' :
  ls'.(log_state.d) = ls.(log_state.d) →
  ls'.(log_state.txns) = take (S crash_txn) ls.(log_state.txns) →
  wal_heap_inv_crashes crash_heaps ls -∗
  wal_heap_inv_crashes (list_to_async
      (take (S crash_txn) (possible crash_heaps))) ls'.
Proof.
  rewrite /wal_heap_inv_crashes.
  intros -> ->.
  iNamed 1.
  iSplit.
  - iPureIntro.
    rewrite possible_list_to_async //; len.
    rewrite length_possible.
    lia.
  - rewrite possible_list_to_async //; last first.
    { len.
      rewrite length_possible; lia. }
    rewrite -{1}(take_drop (S crash_txn) (possible crash_heaps)).
    iDestruct (big_sepL_app with "Hpossible_heaps") as "[Hpre _]".
    iApply (big_sepL_mono with "Hpre").
    intros.
    apply lookup_take_Some in H as [Hlookup Hbound].
    iIntros "H".
    rewrite take_take.
    rewrite -> Nat.min_l by lia; auto.
Qed.

Lemma wal_heap_inv_addr_crash ls k x crash_txn :
  (ls.(log_state.installed_lb) ≤ crash_txn)%nat →
  let ls' := (set log_state.txns (take (S crash_txn)) ls)
                <| log_state.durable_lb := crash_txn |> in
  wal_heap_inv_addr ls k x -∗
  wal_heap_inv_addr ls' k x.
Proof.
  intros Hbound.
  rewrite /wal_heap_inv_addr //=.
  iPureIntro.
  intros [? Hinstalled].
  split; [done|].
  destruct x as [installed_block blocks_since_install].
  destruct Hinstalled as (txn_id & ?&?&?).
  exists txn_id.
  split_and!; [done | | ].
  - rewrite /disk_at_txn_id /=.
    rewrite -> take_take, Nat.min_l by lia.
    assumption.
  - rewrite /updates_since /=.
    (* TODO(tej): not true, blocks since install change when we take a
    prefix of transactions (x won't be the same) *)
Abort.

(* TODO(tej): drop_end is a useless notion; I originally thought the
blocks_since_install could be computed by removing the right number of blocks
from the old blocks_since_install, but this is the filtered set of updates to a
particular address. We need to know the existential txn_id being used to say how
that list gets prefixed on crash. *)

Definition drop_end {A} (n: nat) (l: list A) :=
  take (length l - n) l.

Lemma drop_end_to_take {A} n (l: list A) :
  (n ≤ length l)%nat →
  drop_end (length l - n) l = take n l.
Proof.
  intros.
  rewrite /drop_end.
  auto with f_equal lia.
Qed.

Lemma drop_drop_end {A} n m (l: list A) :
  drop n (drop_end m l) = drop_end m (drop n l).
Proof.
  rewrite /drop_end.
  rewrite take_drop_commute.
  rewrite drop_length.
  destruct (decide (n + m ≤ length l)).
  - auto with f_equal lia.
  - rewrite !drop_ge //; len.
Qed.

Definition heap_block_blocks_since_install (hb: heap_block) :=
  let 'HB _ blocks_since_install := hb in blocks_since_install.

Instance list_fmap_respects_prefix_of {A B} (f: A → B) : Proper (prefix ==> prefix) (fmap f).
Proof.
  intros l1 l2 [l' ->].
  eexists.
  rewrite fmap_app //.
Qed.

Instance list_filter_respects_prefix_of {A} (f: A → Prop) `{!∀ x, Decision (f x)} :
  Proper (prefix ==> prefix) (filter f).
Proof.
  intros l1 l2 [l' ->].
  eexists.
  rewrite filter_app //.
Qed.

Instance concat_respects_prefix {A} : Proper (prefix ==> prefix) (concat (A:=A)).
Proof.
  intros l1 l2 [l' ->].
  eexists.
  rewrite concat_app //.
Qed.

Lemma take_prefix {A} (l1 l2: list A) n :
  l1 `prefix_of` l2 →
  take n l1 `prefix_of` l2.
Proof.
  intros [l' ->].
  exists (drop n l1 ++ l').
  rewrite app_assoc.
  rewrite take_drop //.
Qed.

Lemma wal_heap_inv_addr_crash ls a b crash_txn :
  (ls.(log_state.installed_lb) ≤ crash_txn < length ls.(log_state.txns))%nat →
  let ls' := (set log_state.txns (take (S crash_txn)) ls)
                <| log_state.durable_lb := crash_txn |> in
  wal_heap_inv_addr ls a b ⊢@{_}
  ∃ b', ⌜heap_block_blocks_since_install b' `prefix_of` heap_block_blocks_since_install b⌝ ∗
         wal_heap_inv_addr ls' a b'.
Proof.
  intros Hbound.
  rewrite /wal_heap_inv_addr //=.
  iPureIntro.
  intros [? Hinstalled].
  destruct b as [installed_block blocks_since_install].
  destruct Hinstalled as (txn_id & ?&?&?).
  eexists (HB installed_block _).
  split_and!; [ | done | ].
  2: {
    exists txn_id.
    split_and!; [done | | ].
    - rewrite /disk_at_txn_id /=.
      rewrite -> take_take, Nat.min_l by lia.
      assumption.
    - rewrite //=.
  }
  simpl.
  rewrite /updates_since /= in H2 |- *.
  rewrite skipn_firstn_comm.
  rewrite -H2.
  rewrite /updates_for_addr.
  f_equiv.
  f_equiv.
  rewrite /txn_upds.
  f_equiv.
  f_equiv.
  apply take_prefix.
  reflexivity.
Qed.

Lemma wal_heap_inv_addr_latest_update ls a hb :
  wal_wf ls →
  wal_heap_inv_addr ls a hb -∗
  ⌜last_disk ls !! uint.Z a = Some (hb_latest_update hb)⌝.
Proof.
  iIntros (Hwf [Ha_wf Hinv]).
  iPureIntro.
  destruct hb as [installed_block blocks_since_install].
  destruct Hinv as (txn_id & Hbound & Hlookup_install & Hupdates_since).
  simpl.
  apply updates_since_to_last_disk in Hlookup_install; auto.
  rewrite Hupdates_since in Hlookup_install.
  auto.
Qed.

Lemma wal_heap_gh_crash (γ: gname) crash_txn (gh: gmap u64 heap_block) ls :
  (ls.(log_state.installed_lb) ≤ crash_txn < length ls.(log_state.txns))%nat →
  let ls' := (set log_state.txns (take (S crash_txn)) ls)
                <| log_state.durable_lb := crash_txn |> in
  ghost_map_auth γ 1 ∅ ⊢@{_}
  ([∗ map] a↦b ∈ gh, wal_heap_inv_addr ls a b) -∗
  |==> ∃ gh',
      ⌜dom gh' = dom gh⌝ ∗
      ghost_map_auth γ 1 gh' ∗
      (* TODO: something has been lost along the way about how these values
      relate to the old ones; probably the exchanger is the only thing that can
      contain that information *)
      [∗ map] a↦b ∈ gh', wal_heap_inv_addr ls' a b ∗ a ↪[γ] b.
Proof using walheapG0.
  intros Hbound.
  cbn zeta.
  iIntros "Hctx #Hinv".
  iInduction gh as [|a b gh] "IH" using map_ind.
  - iModIntro.
    iExists ∅.
    rewrite dom_empty_L.
    rewrite !big_sepM_empty.
    by iFrame.
  - rewrite big_sepM_insert //.
    iDestruct "Hinv" as "[Ha Hinv]".
    iMod ("IH" with "Hinv Hctx") as (gh' Hdom) "[Hctx Hinv']".
    iDestruct (wal_heap_inv_addr_crash _ _ _ crash_txn with "Ha") as (b' Hprefix) "Ha'".
    { lia. }
    assert (gh' !! a = None).
    { apply not_elem_of_dom.
      rewrite Hdom.
      apply not_elem_of_dom; done. }
    iMod (ghost_map_insert a b' with "Hctx") as "[Hctx Hmapsto]"; first by auto.
    iModIntro.
    iExists (<[a:=b']> gh').
    iFrame.
    rewrite !dom_insert_L //.
    iSplit; first by (iPureIntro; congruence).
    rewrite big_sepM_insert //.
    iFrame "∗#".
Qed.

Lemma wal_heap_inv_crash_as_last_disk crash_heap ls :
  wal_heap_inv_crash crash_heap ls.(log_state.d) ls.(log_state.txns) -∗
  ⌜∀ (a: u64), crash_heap !! a = last_disk ls !! uint.Z a⌝.
Proof.
  rewrite /wal_heap_inv_crash.
  iPureIntro; intros.
  rewrite H.
  rewrite /last_disk /disk_at_txn_id.
  rewrite -> take_ge by lia.
  auto.
Qed.

Lemma apply_upds_dom_eq upds d :
  dom (apply_upds upds d) =
  list_to_set ((λ u, uint.Z u.(update.addr)) <$> upds) ∪ dom d.
Proof.
  apply set_eq.
  intros.
  rewrite elem_of_union.
  rewrite elem_of_list_to_set.
  apply apply_upds_dom.
Qed.

Instance txn_upds_respect_prefix : Proper (prefix ==> prefix) txn_upds.
Proof.
  intros l1 l2 H.
  rewrite /txn_upds.
  f_equiv.
  f_equiv.
  auto.
Qed.

Lemma Forall_prefix {A} (P : A → Prop) (l1 l2: list A) :
  l1 `prefix_of` l2 →
  Forall P l2 →
  Forall P l1.
Proof.
  rewrite !Forall_lookup.
  intros [l1' ->].
  intros.
  apply (H i x).
  apply lookup_app_l_Some; auto.
Qed.

Lemma disk_at_txn_id_same_dom txn_id ls :
  wal_wf ls →
  dom (disk_at_txn_id txn_id ls) =
  dom        ls.(log_state.d).
Proof.
  intros (Haddrs_wf & _).
  rewrite /disk_at_txn_id.
  rewrite /log_state.updates /addrs_wf in Haddrs_wf.
  rewrite apply_upds_dom_eq.
  match goal with
  | |- list_to_set ?l ∪ ?s = _ =>
    cut (list_to_set l ⊆ s); [ set_solver | ]
  end.
  apply elem_of_subseteq; setoid_rewrite elem_of_list_to_set; intros.
  apply elem_of_list_fmap_2 in H as [u [-> H]].
  apply (Forall_prefix _ (txn_upds $ take (S txn_id) ls.(log_state.txns))) in Haddrs_wf; last first.
  { f_equiv.
    apply take_prefix.
    auto. }
  apply elem_of_list_lookup_1 in H as [i Hlookup].
  eapply Forall_lookup in Hlookup; eauto.
  simpl in Hlookup.
  destruct Hlookup as [_ (b & Hlookup)].
  apply elem_of_dom.
  eauto.
Qed.

Lemma big_sepM_sepS_exists {PROP:bi} `{Countable K} V (Φ: K → V → PROP) m :
  ([∗ map] k↦v ∈ m, Φ k v)%I ⊣⊢
  [∗ set] k ∈ dom m, ∃ v, ⌜m !! k = Some v⌝ ∧ Φ k v.
Proof.
  induction m as [|k v m] using map_ind.
  - rewrite big_sepM_empty dom_empty_L big_sepS_empty.
    auto.
  - rewrite big_sepM_insert //.
    rewrite dom_insert_L.
    rewrite big_sepS_insert; last first.
    { apply not_elem_of_dom; auto. }
    rewrite lookup_insert.
    rewrite IHm.
    f_equiv.
    + iSplit; [ iIntros "H"; iExists _; by iFrame | ].
      iDestruct 1 as (v' Heq) "H"; simplify_eq/=; iFrame.
    + iSplit; iApply big_sepS_mono; iIntros (k' Hlookup) "Hs".
      * iDestruct "Hs" as (v' Hlookup') "H".
        iExists _; iFrame.
        destruct (decide (k = k')); [ congruence | ].
        rewrite lookup_insert_ne //.
      * iDestruct "Hs" as (v' Hlookup') "H".
        iExists _; iFrame.
        apply elem_of_dom in Hlookup as [? ?].
        destruct (decide (k = k')); [ congruence | ].
        rewrite lookup_insert_ne // in Hlookup'.
        auto.
Qed.

Instance set_map_inj `{Countable A} `{Countable B} (f: A → B) :
  Inj eq eq f →
  Inj (⊆) (⊆) (set_map f : gset A → gset B).
Proof.
  intros Hinj.
  intros s1 s2 Hsub.
  set_solver.
Qed.

Lemma wal_heap_h_latest_updates γwal_heap_h crash_heaps gh ls :
  wal_wf ls →
  set_map uint.Z (dom gh) = dom ls.(log_state.d) →
  ([∗ map] a↦hb ∈ gh,
   wal_heap_inv_addr ls a hb ∗
   a ↪[γwal_heap_h] hb) -∗
  wal_heap_inv_crashes crash_heaps ls -∗
  ([∗ map] a↦b ∈ latest crash_heaps, ∃ hb,
    ⌜hb_latest_update hb = b⌝ ∗
    a ↪[γwal_heap_h] hb).
Proof.
  iIntros (Hwf Hgh_complete) "Haddr #Hcrash".
  iNamed "Hcrash".
  iDestruct (big_sepL_lookup _ _ (length (possible crash_heaps) - 1)
                             with "Hpossible_heaps") as "#Hlatest".
  { rewrite lookup_possible_latest' //. }
  rewrite -> take_ge by lia.
  iDestruct (wal_heap_inv_crash_as_last_disk with "Hlatest") as %Hlatest.
  iApply big_sepM_sepS_exists in "Haddr".
  iApply big_sepM_sepS_exists.

  (* NOTE(tej): the other direction doesn't seem guaranteed if [last_disk ls]
  maps addresses >2^64... *)
  assert (set_map uint.Z (dom crash_heaps.(latest)) ⊆
         dom (last_disk ls)).
  { apply elem_of_subseteq; intros a.
    rewrite elem_of_map.
    rewrite elem_of_dom.
    intros [x [-> Helem]].
    apply elem_of_dom in Helem.
    rewrite Hlatest in Helem; auto. }

  iApply big_sepS_mono.
  2: {
    iApply (big_sepS_subseteq with "Haddr").
    rewrite /last_disk in H.
    rewrite disk_at_txn_id_same_dom // in H.
    rewrite -Hgh_complete in H.
    apply (inj (set_map uint.Z)) in H.
    auto.
  }
  iIntros (a Helem) "H".
  iDestruct "H" as (hb Hlookup) "[#Hheap Hmapsto]".
  iDestruct (wal_heap_inv_addr_latest_update with "Hheap") as %Hlast_lookup; auto.
  rewrite -Hlatest in Hlast_lookup.
  rewrite Hlast_lookup.
  iExists _; eauto.
Qed.

Definition crash_heaps_pre_exchange γ γ' ls ls' : iProp Σ :=
  (∃ (crash_heaps: async (gmap u64 Block)),
      "%Hlenold" ∷ ⌜ length ls.(log_state.txns) = length (possible crash_heaps) ⌝ ∗
      (* the client (txn's invariant) will own 3/4 of wal_heap_crash_heaps *)
      "Hcrash_heaps_old" ∷ ghost_var γ.(wal_heap_crash_heaps) (1/4) crash_heaps ∗
      let crash_heaps' := async_take (length ls'.(log_state.txns)) crash_heaps in
      "Hcrash_heaps" ∷ ghost_var γ'.(wal_heap_crash_heaps) (3/4) crash_heaps' ∗
      ([∗ map] a↦b ∈ latest crash_heaps', ∃ hb,
        ⌜hb_latest_update hb = b⌝ ∗
        a ↪[γ'.(wal_heap_h)] hb)).

Definition crash_heaps_post_exchange γ : iProp Σ :=
  (∃ (crash_heaps: async (gmap u64 Block)),
      "Hcrash_heaps_old" ∷ ghost_var γ.(wal_heap_crash_heaps) (3/4) crash_heaps).

Definition heapspec_durable_exchanger γ bnd : iProp Σ :=
  (∃ q n (Hle: (n ≤ bnd)%nat), mono_nat_auth_own γ.(wal_heap_durable_lb) q n).

Definition heapspec_exchanger ls ls' γ γ' : iProp Σ :=
  "%Hwal_wf" ∷ ⌜ wal_wf ls' ⌝ ∗
    "%Hlb_mono" ∷ ⌜(ls.(log_state.durable_lb) ≤ ls'.(log_state.durable_lb))%nat⌝ ∗
    (* old durable_lb for purposes of exchanging lower-bounds in old generation *)
    "Hdurable_lb_old" ∷ heapspec_durable_exchanger γ ls.(log_state.durable_lb) ∗
    "#Hdurable_lb_lb" ∷ mono_nat_lb_own γ'.(wal_heap_durable_lb) ls'.(log_state.durable_lb) ∗
    "Hcrash_heaps_exchange" ∷ (crash_heaps_pre_exchange γ γ' ls ls' ∨ crash_heaps_post_exchange γ).

Global Instance heapspec_exchanger_discretizable ls ls' γ γ' : Discretizable (heapspec_exchanger ls ls' γ γ').
Proof. apply _. Qed.

Lemma heapspec_exchange_durable_lb ls ls' γ γ' lb :
  heapspec_exchanger ls ls' γ γ' -∗
  mono_nat_lb_own γ.(wal_heap_durable_lb) lb -∗
  mono_nat_lb_own γ'.(wal_heap_durable_lb) lb.
Proof.
  iNamed 1.
  iIntros "#Hold_lb_lb".
  iDestruct "Hdurable_lb_old" as (q n Hle) "Hdurable_lb_old".
  iDestruct (mono_nat_lb_own_valid with "Hdurable_lb_old [$]") as %[_ Hlb].
  iApply (mono_nat_lb_own_le with "Hdurable_lb_lb").
  lia.
Qed.

Lemma heapspec_durable_exchanger_dup γ n :
  heapspec_durable_exchanger γ n -∗
  heapspec_durable_exchanger γ n ∗
  heapspec_durable_exchanger γ n.
Proof.
  iIntros "H". iDestruct "H" as (q n' Hle) "(H1&H2)".
  iSplitL "H1"; iExists _, _; iFrame; eauto.
Qed.

Lemma heapspec_durable_exchanger_use γ n lb :
  heapspec_durable_exchanger γ n -∗
  mono_nat_lb_own γ.(wal_heap_durable_lb) lb -∗
  ⌜ lb ≤ n ⌝%nat.
Proof.
  iIntros "H1 H2".
  iDestruct "H1" as (? ? ?) "H".
  iDestruct (mono_nat_lb_own_valid with "[$] [$]") as %[_ Hlb].
  iPureIntro; lia.
Qed.

Lemma heapspec_exchange_crash_heaps ls ls' γ γ' crash_heaps :
  heapspec_exchanger ls ls' γ γ' -∗
  ghost_var γ.(wal_heap_crash_heaps) (3/4) crash_heaps -∗
  heapspec_exchanger ls ls' γ γ' ∗
  (heapspec_durable_exchanger γ (length ls'.(log_state.txns) - 1) ∗
   "%Hlenold" ∷ ⌜ length ls.(log_state.txns) = length (possible crash_heaps) ⌝ ∗
   let crash_heaps' := async_take (length ls'.(log_state.txns)) crash_heaps in
   "Hcrash_heaps" ∷ ghost_var γ'.(wal_heap_crash_heaps) (3/4) crash_heaps' ∗
   ([∗ map] a↦b ∈ latest crash_heaps', ∃ hb,
     ⌜hb_latest_update hb = b⌝ ∗
     a ↪[γ'.(wal_heap_h)] hb)).
Proof.
  iIntros "Hexch Hcrash_heaps_old34".
  iNamed "Hexch".
  iDestruct (heapspec_durable_exchanger_dup with "Hdurable_lb_old") as "(Hdurable_lb_old1&Hdurable_lb_old2)".
  iDestruct "Hcrash_heaps_exchange" as "[H|H]"; iNamed "H".
  - iDestruct (ghost_var_agree with "[$] [$]") as %<-.
    iSplitR "Hcrash_heaps H Hdurable_lb_old2".
    * iFrame "∗%#".
    * iFrame.
      { iDestruct "Hdurable_lb_old2" as (? n Hle) "H".
        iFrame "%".
        unshelve (iExists q, n, _; iFrame).
        destruct Hwal_wf. lia. }
  - by iDestruct (ghost_var_valid_2 with "Hcrash_heaps_old34 Hcrash_heaps_old") as %[Hle ?].
Qed.

Definition heapspec_resources γ γ' ls ls' :=
  (
    heapspec_exchanger ls ls' γ γ' ∗
    (* put into txn's lock invariant *)
    is_locked_walheap γ' {| locked_wh_σd := ls'.(log_state.d);
                            locked_wh_σtxns := ls'.(log_state.txns);
                        |}
  )%I.

Opaque list_to_async.

Lemma wal_heap_inv_crash_transform0 γ γ' ls ls' :
  relation.denote log_crash ls ls' () →
  wal_heap_inv γ ls -∗
  heapspec_init_ghost_state γ' -∗
  |==> ⌜wal_wf ls'⌝ ∗
       wal_heap_inv γ' ls' ∗
       mono_nat_auth_own γ.(wal_heap_durable_lb) 1 ls.(log_state.durable_lb) ∗
       mono_nat_lb_own γ'.(wal_heap_durable_lb) ls'.(log_state.durable_lb) ∗
       crash_heaps_pre_exchange γ γ' ls ls' ∗
       is_locked_walheap γ' {| locked_wh_σd := ls'.(log_state.d);
                               locked_wh_σtxns := ls'.(log_state.txns);
                            |}
.
Proof.
  iIntros (Htrans).
  iNamed 1.
  pose proof (log_crash_to_wf _ _ _ Hwf Htrans) as Hwf'.
  apply log_crash_unfold in Htrans as (crash_txn & Hbound & Hls'_eq).
  match type of Hls'_eq with
  | _ = ?ls'_val => set (ls'':=ls'_val);
                    subst ls'; rename ls'' into ls';
                    fold ls'
  end.
  set (crash_heap':=async_take (length ls'.(log_state.txns)) crash_heaps).
  assert (crash_heap' =
          list_to_async (take (S crash_txn) (possible crash_heaps))) as Hasync_take.
  { subst crash_heap'.
    simpl.
    rewrite -> take_length_le by lia.
    auto. }
  simpl.
  iNamed 1.
  (* TODO: note that this loses the old map, which makes it impossible to use
  those resources to write an exchanger for wal_heap_h pointsto facts in the old
  generation (don't know if those are useful) *)
  iMod (wal_heap_gh_crash _ crash_txn with "wal_heap_h Hgh") as
      (gh' Hdom) "[Hctx' Hgh'] {Hctx}".
  { destruct Hwf.
    lia. }

  iMod (ghost_var_update (ls.(log_state.d), ls'.(log_state.txns)) with "wal_heap_txns")
    as "[Htxns' Htxns2]".
  iMod (ghost_var_update (list_to_async (take (S crash_txn) (possible crash_heaps)))
          with "wal_heap_crash_heaps")
    as "H".
  iEval (rewrite -Qp.quarter_three_quarter) in "H".
  iDestruct "H" as "[Hcrash_heaps_own' Hcrash_heaps_own2]".
  iMod (mono_nat_own_update crash_txn with "wal_durable_lb") as "[Hcrash_heaps_lb' Hcrash_heaps_lb_lb]"; first lia.
  iMod (mono_nat_own_update ls.(log_state.installed_lb) with "wal_heap_installed")
    as "{Hinstalled} [Hinstalled #Hinstalled_lb]"; first by lia.

  iModIntro.
  rewrite /wal_heap_inv /=.
  iFrame (Hwf').

  iFrame.
  iDestruct (wal_heap_inv_crashes_crash _ crash_txn ls ls' with "Hcrash_heaps") as "#Hcrash_heaps'"; auto.
  iDestruct (big_sepM_sep with "Hgh'") as "[#Hinv_addr Hgh']".

  iSplitR "Hcrash_heaps Hcrash_heaps_own2 Hgh'"; last first.
  { simpl.
    rewrite -Hasync_take -/crash_heap'.
    iFrame "Hcrash_heaps_own2".
    iDestruct (big_sepM_sep with "[Hinv_addr Hgh']") as "Hgh'".
    { iSplitR "Hgh'"; [ iFrame "Hinv_addr" | iFrame ]. }
    simpl.
    iSplitL "Hcrash_heaps".
    { iNamed "Hcrash_heaps". eauto. }
    rewrite -/ls'.
    iApply (wal_heap_h_latest_updates _ crash_heap' with "Hgh' [Hcrash_heaps']"); auto.
    rewrite Hdom Hgh_complete.
    auto.
  }
  iFrame "#∗%".
  iPureIntro; congruence.
Qed.

Lemma wal_heap_inv_crash_transform γ γ' ls ls' :
  relation.denote log_crash ls ls' () →
  wal_heap_inv γ ls -∗
  heapspec_init_ghost_state γ' -∗
  |==> wal_heap_inv γ' ls' ∗
       heapspec_resources γ γ' ls ls'.
Proof.
  iIntros (Htrans) "Hinv Hinit".
  iMod (wal_heap_inv_crash_transform0 with "Hinv Hinit") as (Hwf') "[Hinv resources]"; eauto.
  iFrame "Hinv".
  iModIntro.
  iDestruct "resources" as "(?&?&?&?)".
  iFrame.
  iFrame "∗%".
  apply log_crash_unfold in Htrans as (crash_txn & Hbound & Hls'_eq).
  subst ls'; simpl.
  iSplit; first by (iPureIntro; lia).
  unshelve iExists _; done.
Qed.

Definition locked_wh_disk (lwh : locked_walheap) : disk :=
  apply_upds (txn_upds lwh.(locked_wh_σtxns)) lwh.(locked_wh_σd).


(* In lemmas; probably belong in one of the external list libraries *)

Theorem in_concat_list {A: Type} (l: list (list A)):
  forall l', In l' l -> forall e, In e l' -> In e (concat l).
Proof.
  intros.
  induction l.
  - simpl in *; auto.
  - rewrite concat_cons.
    apply in_or_app.
    rewrite <- elem_of_list_In in H.
    apply elem_of_cons in H.
    intuition; subst.
    + left; auto.
    + right.
      apply IHl.
      rewrite <- elem_of_list_In; auto.
Qed.

Theorem concat_list_in {A: Type} (l: list (list A)):
  forall e, In e (concat l) -> exists l', In e l' /\ In l' l.
Proof.
  intros.
  induction l.
  - simpl in *. exfalso; auto.
  - rewrite concat_cons in H.
    apply in_app_or in H.
    intuition.
    + exists a.
      split; auto.
      rewrite <- elem_of_list_In.
      apply elem_of_list_here.
    + destruct H. intuition.
      exists x.
      split; auto.
      apply in_cons; auto.
Qed.

Theorem incl_concat {A: Type} (l1 l2: list (list A)):
  incl l1 l2 ->
  incl (concat l1) (concat l2).
Proof.
  unfold incl.
  intros.
  apply concat_list_in in H0.
  destruct H0.
  intuition.
  specialize (H x).
  eapply in_concat_list; auto.
Qed.

Theorem in_drop {A} (l: list A):
  forall n e,
    In e (drop n l) -> In e l.
Proof.
  induction l.
  - intros.
    rewrite drop_nil in H.
    rewrite <- elem_of_list_In in H.
    apply not_elem_of_nil in H; auto.
  - intros.
    destruct (decide (n = 0%nat)); subst.
    + rewrite skipn_O in H; auto.
    + rewrite <- elem_of_list_In.
      assert (n = 0%nat ∨ (∃ m : nat, n = S m)) by apply Nat.zero_or_succ.
      destruct H0; subst; try congruence.
      destruct H0; subst.
      rewrite skipn_cons in H.
      specialize (IHl x e).
      apply elem_of_cons.
      right.
      rewrite elem_of_list_In; auto.
Qed.

Theorem in_drop_ge {A} (l: list A) (n0 n1: nat):
  n0 <= n1 ->
  forall e, In e (drop n1 l) -> In e (drop n0 l).
Proof.
  intros.
  replace (drop n1 l) with (drop (n1-n0) (drop n0 l)) in H0.
  1: apply in_drop  in H0; auto.
  rewrite drop_drop.
  replace ((n0 + (n1 - n0))%nat) with (n1) by lia; auto.
Qed.

(* Helper lemmas *)

Theorem is_update_cons_eq: forall l a0,
  is_update (a0 :: l) a0.(update.addr) a0.(update.b).
Proof.
  intros.
  rewrite /is_update.
  exists a0.
  split; try auto.
  apply elem_of_list_here.
Qed.

Theorem is_update_cons (l: list update.t) a b:
  forall a0, is_update l a b -> is_update (a0 :: l) a b.
Proof.
  intros.
  unfold is_update in *.
  destruct H as [u [l1 H]].
  intuition.
  exists u.
  split; auto.
  apply elem_of_list_further; auto.
Qed.

Theorem latest_update_cons installed a:
  forall bs,
    bs ≠ [] ->
    latest_update installed (a :: bs) = latest_update a bs.
Proof.
  intros.
  unfold latest_update at 1.
  simpl.
  fold latest_update.
  f_equal.
Qed.

Theorem latest_update_take_some bs v:
  forall installed (pos: nat),
    (installed :: bs) !! pos = Some v ->
    latest_update installed (take pos bs) = v.
Proof.
  induction bs.
  - intros.
    rewrite firstn_nil.
    simpl.
    assert(pos = 0%nat).
    {
      apply lookup_lt_Some in H.
      simpl in *.
      word.
    }
    rewrite H0 in H.
    simpl in *.
    inversion H; auto.
  - intros.
    destruct (decide (pos = 0%nat)).
    + rewrite e in H; simpl in *.
      inversion H; auto.
      rewrite e; simpl; auto.
    +
      assert (exists (pos':nat), pos = S pos').
      {
        exists (pred pos). lia.
      }
      destruct H0 as [pos' H0].
      rewrite H0.
      rewrite firstn_cons.
      destruct (decide ((take pos' bs) = [])).
      ++ simpl.
         specialize (IHbs a pos').
         apply IHbs.
         rewrite lookup_cons_ne_0 in H; auto.
         rewrite H0 in H; simpl in *; auto.
      ++ rewrite latest_update_cons; auto.
         {
           specialize (IHbs a pos').
           apply IHbs.
           rewrite lookup_cons_ne_0 in H; auto.
           rewrite H0 in H; simpl in *; auto.
         }
Qed.

Theorem take_drop_txns:
  forall (txn_id: nat) txns,
    txn_id <= length txns ->
    txn_upds txns = txn_upds (take txn_id txns) ++ txn_upds (drop txn_id txns).
Proof.
  induction txn_id.
  - intros.
    unfold txn_upds; simpl.
    rewrite skipn_O; auto.
  - intros. destruct txns.
    + unfold txn_upds; simpl; auto.
    + rewrite txn_upds_cons.
      rewrite firstn_cons.
      rewrite skipn_cons.
      replace (txn_upds (p :: take txn_id txns)) with (txn_upds [p] ++ txn_upds (take txn_id txns)).
      2: rewrite <- txn_upds_cons; auto.
      rewrite <- app_assoc.
      f_equal.
      rewrite <- IHtxn_id; auto.
      rewrite cons_length in H.
      lia.
Qed.

Theorem updates_for_addr_app a l1 l2:
  updates_for_addr a (l1 ++ l2) = updates_for_addr a l1 ++ updates_for_addr a l2.
Proof.
  unfold updates_for_addr.
  rewrite <- fmap_app.
  f_equal.
  rewrite filter_app //.
Qed.

Theorem updates_since_to_last_disk σ a (txn_id : nat) installed :
  wal_wf σ ->
  disk_at_txn_id txn_id σ !! uint.Z a = Some installed ->
  (txn_id ≤ σ.(log_state.installed_lb))%nat ->
  last_disk σ !! uint.Z a = Some (latest_update installed (updates_since txn_id a σ)).
Proof.
  destruct σ.
  unfold last_disk, updates_since, disk_at_txn_id.
  simpl.
  intros.
  rewrite -> take_ge by lia.
  rewrite (take_drop_txns (S txn_id) txns).
  2: {
    unfold wal_wf in H; intuition; simpl in *.
    lia.
  }
  rewrite apply_upds_app.
  generalize dependent H0.
  generalize (apply_upds (txn_upds (take (S txn_id) txns)) d).
  intros.
  generalize (txn_upds (drop (S txn_id) txns)).
  intros.
  generalize dependent d0.
  generalize dependent installed.
  induction l; simpl; intros.
  - auto.
  - destruct a0. unfold updates_for_addr.
    rewrite filter_cons; simpl.
    destruct (decide (addr = a)); subst.
    + simpl.
      erewrite <- IHl.
      { reflexivity. }
      rewrite lookup_insert. auto.
    + erewrite <- IHl.
      { reflexivity. }
      rewrite lookup_insert_ne; auto.
      intro Hx. apply n. word.
Qed.

Theorem last_disk_installed_lb σ pos :
  last_disk (@set _ _  log_state.installed_lb
      (fun (_ : forall _ : nat, nat) (x2 : log_state.t) => x2) (λ _ : nat, pos) σ) =
  last_disk σ.
Proof.
  reflexivity.
Qed.

Theorem apply_upds_txn_upds_app l0 l1 d:
  apply_upds (txn_upds (l0 ++ l1)) d = apply_upds (txn_upds l1) (apply_upds (txn_upds l0) d).
Proof.
  intros.
  unfold txn_upds.
  rewrite fmap_app.
  rewrite concat_app.
  rewrite apply_upds_app; auto.
Qed.

Theorem apply_update_ne:
  forall u1 u2 d,
  u1.(update.addr) ≠ u2.(update.addr) ->
  apply_upds [u1] (apply_upds [u2] d) = apply_upds [u2] (apply_upds [u1] d).
Proof.
  intros.
  destruct u1, u2.
  simpl in *.
  rewrite insert_commute; eauto.
  intro Hx. apply H. word.
Qed.

Theorem apply_update_eq:
  forall u1 u2 d,
  u1.(update.addr) = u2.(update.addr) ->
  apply_upds [u1] (apply_upds [u2] d) = apply_upds [u1] d.
Proof.
  intros.
  destruct u1, u2.
  simpl in *.
  subst.
  rewrite insert_insert.
  reflexivity.
Qed.

Theorem lookup_apply_update_ne a:
  forall l d u,
    u.(update.addr) ≠ a ->
    apply_upds l (apply_upds [u] d) !! uint.Z a = apply_upds l d !! uint.Z a.
Proof.
  intros.
  generalize dependent d.
  induction l.
  - intros. destruct u; simpl in *.
    rewrite lookup_insert_ne; auto.
    intro Hx. apply H. word.
  - intros.
    rewrite apply_upds_cons.
    destruct (decide (a0.(update.addr) = u.(update.addr))); subst; eauto.
    + rewrite apply_update_eq //.
    + rewrite -> apply_update_ne by auto.
      rewrite IHl.
      rewrite [apply_upds (a0::l) _]apply_upds_cons //.
Qed.

Theorem no_updates_cons (l: list update.t) a:
  forall u, no_updates (u::l) a -> no_updates l a.
Proof.
  intros.
  unfold no_updates in *.
  intros.
  specialize (H u0).
  apply H.
  rewrite elem_of_cons.
  right; auto.
Qed.

Theorem no_updates_cons_ne (l: list update.t) a:
  forall u,
    u.(update.addr) ≠ a ->
    no_updates l a ->
    no_updates (u :: l) a.
Proof.
  intros.
  unfold no_updates in *.
  intros.
  apply elem_of_cons in H1.
  intuition; subst; auto.
  specialize (H0 u0 H3); auto.
Qed.

Theorem no_updates_since_nil σ a (txn_id : nat) :
  wal_wf σ ->
  no_updates_since σ a txn_id ->
  updates_since txn_id a σ = nil.
Proof.
  unfold no_updates_since, updates_since.
  generalize σ.(log_state.txns).
  intro l.
  generalize (txn_upds (drop (S txn_id) l)).
  intros. intuition.
  unfold updates_for_addr.
  induction l0.
  - simpl; auto.
  - rewrite filter_cons.
    pose proof H0 as H0'.
    rewrite -> Forall_forall in H0'.
    specialize (H0' a0).
    destruct (decide ((a0.(update.addr) = a))).
    + exfalso.
      apply H0'; auto.
      apply elem_of_list_here.
    + apply IHl0; auto.
      apply Forall_inv_tail in H0; auto.
Qed.

Theorem apply_no_updates_since_lookup txn_id a:
  forall d l,
  Forall (λ u : update.t, u.(update.addr) = a → False) (txn_upds (drop txn_id l)) ->
  d !! uint.Z a = apply_upds (txn_upds (drop txn_id l)) d !! uint.Z a.
Proof.
  intros.
  induction (txn_upds (drop txn_id l)).
  + simpl in *; auto.
  + rewrite apply_upds_cons.
    rewrite lookup_apply_update_ne; auto.
    {
      apply IHl0; auto.
      apply Forall_inv_tail in H; auto.
    }
    rewrite -> Forall_forall in H.
    specialize (H a0).
    assert (a0.(update.addr) = a -> False).
    {
      intros.
      apply H; auto.
      apply elem_of_list_here.
    }
    congruence.
Qed.

Theorem no_updates_since_last_disk σ a (txn_id : nat) :
  wal_wf σ ->
  no_updates_since σ a txn_id ->
  disk_at_txn_id txn_id σ !! uint.Z a = last_disk σ !! uint.Z a.
Proof.
  unfold last_disk, no_updates_since, wal_wf, last_disk, disk_at_txn_id.
  generalize (σ.(log_state.txns)).
  generalize (σ.(log_state.d)).
  intros. intuition.
  clear H.
  destruct (decide (txn_id < length l)).
  2: {
    rewrite -> take_ge by lia.
    rewrite -> take_ge by lia.
    reflexivity.
  }
  replace l with (take (S txn_id) l ++ drop (S txn_id) l) at 3.
  2 : {
    rewrite firstn_skipn; eauto.
  }
  rewrite firstn_app.
  assert (length (take (S txn_id) l) = S txn_id) by len.
  rewrite H; subst.
  rewrite firstn_firstn.
  assert( (Init.Nat.min (S (Datatypes.length l)) (S txn_id)) = S txn_id) by lia.
  rewrite H3.
  assert (take (S (length l) - S txn_id) (drop (S txn_id) l) = drop (S txn_id) l).
  {
    rewrite take_ge; eauto.
    rewrite skipn_length; lia.
  }
  rewrite H5.
  rewrite apply_upds_txn_upds_app.
  erewrite apply_no_updates_since_lookup; eauto.
Qed.

Theorem lookup_apply_upds_cons_ne:
  forall l d (a: u64) u b,
    u.(update.addr) ≠ a ->
    apply_upds l (apply_upds [u] d) !! uint.Z a = Some b ->
    apply_upds l d !! uint.Z a = Some b \/ (d !! uint.Z a = Some b).
Proof.
  intros.
  generalize dependent d.
  induction l.
  - intros.
    destruct u.
    rewrite lookup_insert_ne in H0; eauto.
    simpl in *.
    intro Hx.
    apply H. word.
  - intros.
    rewrite apply_upds_cons in H0.
    rewrite apply_upds_cons.
    destruct (decide (a0.(update.addr) = u.(update.addr))).
    1: rewrite apply_update_eq in H0; eauto.
    rewrite apply_update_ne in H0; eauto.
    specialize (IHl (apply_upds [a0] d) H0).
    intuition.
    destruct (decide (a0.(update.addr) = a)).
    {
      rewrite lookup_apply_update_ne in H0; eauto.
    }
    rewrite lookup_apply_update_ne in H0; eauto.
Qed.

Theorem apply_upds_lookup_eq d (a: u64) b:
  forall a0,
    a0.(update.addr) = a ->
    apply_upds [a0] d !! uint.Z a = Some b ->
    a0.(update.b) = b.
Proof.
  intros.
  unfold apply_upds in H.
  destruct a0; simpl in *.
  subst.
  rewrite lookup_insert in H0.
  inversion H0; auto.
Qed.

Theorem apply_upds_no_updates l (a: u64):
   forall d u,
    u.(update.addr) = a ->
    no_updates l a ->
    apply_upds l (apply_upds [u] d) !! uint.Z a = apply_upds [u] d !! uint.Z a.
Proof.
  intros.
  generalize dependent d.
  induction l.
  - intros.
    destruct u.
    simpl in *; subst.
    intuition; auto.
  - intros.
    rewrite apply_upds_cons.
    destruct (decide (a0.(update.addr) = u.(update.addr))); subst.
    {
      exfalso.
      unfold no_updates in H0.
      specialize (H0 a0).
      destruct H0.
      1: apply elem_of_list_here; auto.
      auto.
    }
    apply no_updates_cons in H0 as H0'.
    rewrite apply_update_ne; auto.
    specialize (IHl H0' (apply_upds [a0] d)).
    rewrite IHl.
    assert (apply_upds [u] (apply_upds [a0] d) !! uint.Z u.(update.addr) =
            apply_upds [u] d !! uint.Z u.(update.addr)).
    1: apply lookup_apply_update_ne; auto.
    auto.
Qed.

Theorem lookup_apply_upds_cons_eq l (a: u64) b:
  forall d u,
    u.(update.addr) = a ->
    apply_upds l (apply_upds [u] d) !! uint.Z a = Some b ->
    no_updates l a \/ is_update l a b.
Proof.
  induction l.
  - intros.
    destruct u.
    simpl in *; subst.
    left; auto.
    unfold no_updates.
    intros.
    exfalso.
    apply elem_of_nil in H; auto.
  - intros.
    rewrite apply_upds_cons in H0.
    destruct (decide (a0.(update.addr) = u.(update.addr))).
    + subst.
      rewrite apply_update_eq  in H0; auto.
      specialize (IHl d a0 e H0).
      destruct (decide (a0.(update.b) = u.(update.b))).
      {
        intuition.
        ++ right.
           rewrite <- e.
           rewrite apply_upds_no_updates in H0; auto.
           apply apply_upds_lookup_eq in H0; auto.
           rewrite <- H0.
           apply is_update_cons_eq.
        ++ right.
           apply is_update_cons with (a0:=a0) in H; auto.
      }
      {
        intuition.
        ++ rewrite apply_upds_no_updates in H0; auto.
           apply apply_upds_lookup_eq in H0; auto.
           right.
           rewrite <- H0.
           rewrite <- e.
           apply is_update_cons_eq.
        ++ right.
           eapply is_update_cons with (a0 := a0) in H; auto.
      }
    + subst.
      rewrite apply_update_ne in H0; auto.
      assert (u.(update.addr) = u.(update.addr)).
      1: reflexivity.
      specialize (IHl (apply_upds [a0] d) u H).
      intuition.
      ++ left.
         apply no_updates_cons_ne with (u := a0) in H2; auto.
      ++ right.
         apply is_update_cons with (a0:=a0) in H2; auto.
Qed.

Theorem lookup_apply_upds d:
  forall l a b,
    apply_upds l d !! uint.Z a = Some b ->
    d !! uint.Z a = Some b \/ is_update l a b.
Proof.
  intros.
  induction l.
  - simpl in *.
    left; auto.
  - rewrite apply_upds_cons in H.
    destruct (decide (a0.(update.addr) = a)).
    {
      apply lookup_apply_upds_cons_eq in H as H'1; auto.
      intuition.
      {
        right.
        rewrite apply_upds_no_updates in H; auto.
        apply apply_upds_lookup_eq in H; auto.
        subst. apply is_update_cons_eq; auto.
      }
      right.
      apply is_update_cons; auto.
    }
    apply lookup_apply_upds_cons_ne in H; eauto.
    intuition.
    right.
    apply is_update_cons; auto.
Qed.

Theorem txn_ups_take_elem_of u l:
  forall (txn_id txn_id': nat),
    txn_id <= txn_id' ->
    txn_id' <= length l + txn_id ->
    u ∈ txn_upds (take (txn_id' - txn_id) l) ->
    u ∈ txn_upds l.
Proof.
  intros.
  rewrite -> elem_of_list_In in H1.
  unfold txn_upds in *.
  apply in_concat in H1.
  destruct H1 as [l0 H1].
  intuition.
  rewrite -> elem_of_list_In.
  apply in_concat.
  exists l0.
  split; auto.
  rewrite <- elem_of_list_In in H2.
  rewrite <- elem_of_list_In.
  eapply elem_of_list_fmap_2 in H2.
  destruct H2.
  intuition.
  eapply elem_of_list_fmap_1_alt; eauto.
  apply elem_of_list_lookup_1 in H4.
  destruct H4 as [i H4].
  apply lookup_lt_Some in H4 as Hlen.
  rewrite -> firstn_length_le in Hlen by lia.
  rewrite -> lookup_take in H4 by lia.
  apply elem_of_list_lookup_2 in H4; auto.
Qed.

Theorem apply_upds_since_txn_id_new d (txn_id txn_id': nat):
  forall l a b b1,
    txn_id <= txn_id' ->
    txn_id' < length l ->
    apply_upds (txn_upds (take (S txn_id) l)) d !! uint.Z a = Some b ->
    apply_upds (txn_upds (take (S txn_id') l)) d !! uint.Z a = Some b1 ->
    b ≠ b1 ->
    (exists u, u ∈ (txn_upds (drop (S txn_id) l))
          /\ u.(update.addr) = a /\ u.(update.b) = b1).
Proof using walheapG0 Σ.
  intros.
  replace (take (S txn_id') l) with (take (S txn_id) l ++ drop (S txn_id) (take (S txn_id') l)) in H2.
  2: {
    rewrite skipn_firstn_comm.
    rewrite take_take_drop.
    f_equal.
    lia.
  }
  rewrite apply_upds_txn_upds_app in H2.
  apply lookup_apply_upds in H2 as H2'; eauto.
  intuition.
  1: destruct (decide (b = b1)); congruence.
  destruct H4 as [u H4].
  exists u.
  intuition.
  rewrite skipn_firstn_comm in H5.
  apply txn_ups_take_elem_of in H5; len; auto.
Qed.

Theorem updates_since_apply_upds σ a (txn_id txn_id' : nat) installedb b :
  txn_id ≤ txn_id' ->
  txn_id' < length (log_state.txns σ) ->
  disk_at_txn_id txn_id σ !! uint.Z a = Some installedb ->
  disk_at_txn_id txn_id' σ !! uint.Z a = Some b ->
  b ∈ installedb :: updates_since txn_id a σ.
Proof using walheapG0 Σ.
  unfold updates_since, disk_at_txn_id in *.
  generalize (σ.(log_state.txns)).
  generalize (σ.(log_state.d)).
  intros.
  destruct (decide (b = installedb)).
  {
    subst.
    apply elem_of_list_here.
  }
  eapply apply_upds_since_txn_id_new with (txn_id := txn_id) (txn_id' := txn_id') in H0; eauto.
  destruct H0. destruct H0. intuition.
  assert (In b (map update.b (filter (λ u : update.t, u.(update.addr) = a) (txn_upds (drop (S txn_id) l))))).
  {
    rewrite in_map_iff.
    exists x; eauto.
    split; eauto.
    rewrite <- elem_of_list_In.
    rewrite elem_of_list_filter.
    split; eauto.
  }
  rewrite elem_of_list_In.
  apply in_cons; eauto.
Qed.

Theorem disk_at_txn_id_installed_to σ txn_id0 txn_id :
  disk_at_txn_id txn_id0 (@set _ _  log_state.installed_lb
      (fun _ (x2 : log_state.t) => x2) (λ _ : nat, txn_id) σ) =
  disk_at_txn_id txn_id0 σ.
Proof.
  destruct σ; auto.
Qed.

Theorem wal_wf_advance_durable_lb σ (txn_id:nat) :
  wal_wf σ ->
 (σ.(log_state.durable_lb) ≤ txn_id < length σ.(log_state.txns))%nat ->
  wal_wf (set log_state.durable_lb (λ _ : nat, txn_id) σ).
Proof.
  destruct σ.
  unfold wal_wf; simpl.
  intuition.
  1: lia.
  lia.
Qed.

Theorem wal_wf_advance_installed_lb σ (txn_id:nat) :
  wal_wf σ ->
  (txn_id ≤ σ.(log_state.durable_lb))%nat ->
  wal_wf (set log_state.installed_lb (λ _ : nat, txn_id) σ).
Proof.
  destruct σ.
  unfold wal_wf; simpl.
  intuition.
  lia.
Qed.

Theorem wal_wf_append_txns σ pos' bs txns :
  wal_wf σ ->
  txns = σ.(log_state.txns) ->
  addrs_wf bs σ.(log_state.d) ->
  (∀ (pos : u64) (txn_id : nat),
    is_txn σ.(log_state.txns) txn_id pos → uint.nat pos' >= uint.nat pos) ->
  wal_wf (set log_state.txns (λ _, txns ++ [(pos', bs)]) σ).
Proof.
  intros Hwf -> Haddrs_wf Hhighest.
  eapply mem_append_preserves_wf; eauto.
  intros.
  eapply Hhighest in H; word.
Qed.

Lemma updates_since_updates σ (txn_id:nat) (a:u64) pos' bs :
  wal_wf σ ->
  (txn_id ≤ σ.(log_state.installed_lb))%nat ->
  updates_since txn_id a
    (set log_state.txns
     (λ _ : list (u64 * list update.t), σ.(log_state.txns) ++ [(pos',bs)]) σ) =
  updates_since txn_id a σ ++ updates_for_addr a bs.
Proof.
  intros.
  destruct σ.
  rewrite /set //.
  rewrite /updates_since //.
  simpl.
  rewrite drop_app_le.
  2: {
    unfold wal_wf in H.
    intuition; simpl in *.
    lia.
  }
  rewrite txn_upds_app.
  rewrite updates_for_addr_app.
  f_equal.
  unfold txn_upds; simpl.
  rewrite app_nil_r; auto.
Qed.

Lemma disk_at_txn_id_append σ (txn_id : nat) pos new :
  wal_wf σ ->
  (txn_id < length σ.(log_state.txns))%nat ->
  disk_at_txn_id txn_id σ =
    disk_at_txn_id txn_id (set log_state.txns
                                 (λ upds, upds ++ [(pos,new)]) σ).
Proof.
  intros.
  rewrite /set //.
  destruct σ.
  rewrite /disk_at_txn_id //.
  unfold wal_wf in H.
  simpl in *.
  intuition.
  rewrite take_app_le /=; auto.
Qed.

Lemma updates_for_addr_notin : ∀ bs a,
  a ∉ fmap update.addr bs ->
  updates_for_addr a bs = nil.
Proof.
  induction bs; intros; eauto.
  rewrite fmap_cons in H.
  apply not_elem_of_cons in H; destruct H.
  erewrite <- IHbs; eauto.
  destruct a; rewrite /updates_for_addr filter_cons /=; simpl in *.
  destruct (decide (addr = a0)); congruence.
Qed.

Theorem updates_for_addr_in : ∀ bs u i,
  bs !! i = Some u ->
  NoDup (fmap update.addr bs) ->
  updates_for_addr u.(update.addr) bs = [u.(update.b)].
Proof.
  induction bs; intros.
  { rewrite lookup_nil in H; congruence. }
  destruct i; simpl in *.
  { inversion H; clear H; subst.
    rewrite /updates_for_addr filter_cons /=.
    destruct (decide (u.(update.addr) = u.(update.addr))); try congruence.
    inversion H0.
    apply updates_for_addr_notin in H2.
    rewrite /updates_for_addr in H2.
    rewrite fmap_cons.
    rewrite H2; eauto.
  }
  inversion H0; subst.
  erewrite <- IHbs; eauto.
  rewrite /updates_for_addr filter_cons /=.
  destruct (decide (a.(update.addr) = u.(update.addr))); eauto.
  exfalso.
  apply H3. rewrite e.
  eapply elem_of_list_lookup.
  eexists.
  rewrite list_lookup_fmap.
  erewrite H; eauto.
Qed.

(* Specs *)

Lemma wal_update_durable (gh : gmap u64 heap_block) (σ : log_state.t) new_durable :
  (σ.(log_state.durable_lb) ≤ new_durable ≤ length (log_state.txns σ))%nat ->
  ([∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr σ a1 b0) -∗
   [∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr
     (set log_state.durable_lb (λ _ : nat, new_durable) σ) a1 b0.
Proof.
  iIntros "% Hmap".
  destruct σ; simpl in *.
  rewrite /set /=.
  iDestruct (big_sepM_mono _ (wal_heap_inv_addr {|
                                  log_state.d := d;
                                  log_state.installed_lb := installed_lb;
                                  log_state.durable_lb := new_durable |}) with "Hmap") as "Hmap".
  2: iFrame.
  rewrite /wal_heap_inv_addr.
  iIntros; iPureIntro.
  destruct x; auto.
Qed.

Lemma wal_update_installed (gh : gmap u64 heap_block) (σ : log_state.t) new_installed :
  (σ.(log_state.installed_lb) ≤ new_installed ≤ σ.(log_state.durable_lb))%nat ->
  ([∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr σ a1 b0) -∗
   [∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr
     (set log_state.installed_lb (λ _ : nat, new_installed) σ) a1 b0.
Proof.
  iIntros "% Hmap".
  destruct σ eqn:sigma; simpl in *.
  rewrite /set /=.
  iDestruct (big_sepM_mono _ (wal_heap_inv_addr {|
                                  log_state.d := d;
                                  log_state.installed_lb := new_installed;
                                  log_state.durable_lb := durable_lb |})
               with "Hmap") as "Hmap".
  2: iFrame.
  rewrite /wal_heap_inv_addr.
  iIntros; iPureIntro.
  destruct x; eauto.
  intuition.
  simpl in *.
  destruct H4 as [txn_id ?].
  exists txn_id.
  intuition idtac.
  lia.
Qed.

Definition readmem_q γh (a : u64) (installed : Block) (bs : list Block) (res : option Block) : iProp Σ :=
  (
    match res with
    | Some resb =>
      a ↪[γh.(wal_heap_h)] (HB installed bs) ∗
      ⌜ resb = latest_update installed bs ⌝
    | None =>
      a ↪[γh.(wal_heap_h)] (HB (latest_update installed bs) nil)
    end
  )%I.

Lemma union_singleton_l_id `{Countable A} (a:A) (x: gset A) :
  a ∈ x →
  {[a]} ∪ x = x.
Proof. set_solver. Qed.

Theorem wal_heap_readmem E γh a (Q : option Block -> iProp Σ) :
  ( |NC={⊤ ∖ ↑walN, E}=> ∃ installed bs, a ↪[γh.(wal_heap_h)] (HB installed bs) ∗
        ( ∀ mb, readmem_q γh a installed bs mb -∗ |NC={E, ⊤ ∖ ↑walN}=> Q mb ) ) -∗
  ( ∀ σ σ' mb,
      ⌜wal_wf σ⌝ -∗
      ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗
      ( (wal_heap_inv γh) σ -∗ |NC={⊤ ∖ ↑walN}=> (wal_heap_inv γh) σ' ∗ Q mb ) ).
Proof.
  iIntros "Ha".
  iIntros (σ σ' mb) "% % Hinv".
  iNamed "Hinv".

  iMod "Ha" as (installed bs) "[Ha Hfupd]".
  iDestruct (ghost_map_lookup with "Hctx Ha") as "%".
  iDestruct (big_sepM_lookup with "Hgh") as "%"; eauto.

  destruct H2 as [? Htxn_id].
  destruct Htxn_id as [txn_id ?].
  intuition idtac.

  simpl in *; monad_inv.
  destruct x.
  - simpl in *; monad_inv.
    simpl in *; monad_inv.

    erewrite updates_since_to_last_disk in H0 by eauto.
    simpl in *; monad_inv.

    iDestruct ("Hfupd" $! (Some (latest_update installed
                                    (updates_since txn_id a σ))) with "[Ha]") as "Hfupd".
    { rewrite /readmem_q. iFrame. done. }
    iMod "Hfupd".

    iModIntro.
    iSplitL "Hctx Hgh Htxns Hinstalled Hcrash_heaps Hcrash_heaps_own Hcrash_heaps_lb".
    + iExists _, _; iFrame. done.
    + iFrame.

  - simpl in *; monad_inv.

    iMod (mono_nat_own_update new_installed with "Hinstalled") as "[Hinstalled #Hinstalledfrag]".
    { intuition. }

    iMod (mono_nat_own_update new_durable with "Hcrash_heaps_lb") as "[Hcrash_heaps_lb _]".
    { lia. }

    iMod (ghost_map_update (HB (latest_update installed (updates_since txn_id a σ)) nil) with "Hctx Ha") as "[Hctx Ha]".
    iMod ("Hfupd" $! None with "[Ha]").
    {
      rewrite /readmem_q.
      iFrame.
    }
    iModIntro.
    iSplitL "Hctx Hgh Htxns Hinstalled Hinstalledfrag Hcrash_heaps Hcrash_heaps_own Hcrash_heaps_lb".
    2: iFrame.

    iDestruct (wal_update_durable gh (set log_state.durable_lb (λ _ : nat, new_durable) σ) new_durable with "Hgh") as "Hgh".
    { rewrite /set /=; lia. }
    iDestruct (wal_update_installed gh (set log_state.durable_lb (λ _ : nat, new_durable) σ) new_installed with "Hgh") as "Hgh"; eauto.
    iDestruct (big_sepM_insert_acc with "Hgh") as "[_ Hgh]"; eauto.
    iDestruct ("Hgh" $! (HB (latest_update installed (updates_since txn_id a σ)) nil) with "[]") as "Hx".
    {
      rewrite /wal_heap_inv_addr /=.
      iPureIntro; intros.
      simpl in *.
      split; auto.
      exists new_installed. intuition try lia.
      {
        rewrite -updates_since_to_last_disk; eauto.
        1: rewrite no_updates_since_last_disk; auto.
        apply wal_wf_advance_installed_lb with (σ := (set log_state.durable_lb (λ _ : nat, new_durable) σ)).
        1: apply wal_wf_advance_durable_lb; auto.
        simpl.
        lia.
      }
      {
        rewrite no_updates_since_nil; auto.
        apply wal_wf_advance_installed_lb with (σ := (set log_state.durable_lb (λ _ : nat, new_durable) σ)).
        1: apply wal_wf_advance_durable_lb; auto.
        simpl.
        lia.
      }
    }
    rewrite /wal_heap_inv.
    iExists _, _; iFrame.

    iSplit.
    { iPureIntro.
      rewrite /= !dom_insert_L.
      rewrite union_singleton_l_id //.
      apply elem_of_dom; eauto. }

    iPureIntro.
    eapply wal_wf_advance_installed_lb.
    2: { intuition idtac. }
    eapply wal_wf_advance_durable_lb; eauto.
Qed.

Definition readinstalled_q γh (a : u64) (installed : Block) (bs : list Block) (res : Block) : iProp Σ :=
  (
    a ↪[γh] (HB installed bs) ∗
    ⌜ res ∈ installed :: bs ⌝
  )%I.

Theorem wal_heap_readinstalled E γh a (Q : Block -> iProp Σ) :
  ( |NC={⊤ ∖ ↑walN, E}=> ∃ installed bs, a ↪[γh.(wal_heap_h)] (HB installed bs) ∗
        ( ∀ b, readinstalled_q γh.(wal_heap_h) a installed bs b -∗ |NC={E, ⊤ ∖ ↑walN}=> Q b ) ) -∗
  ( ∀ σ σ' b',
      ⌜wal_wf σ⌝ -∗
      ⌜relation.denote (log_read_installed a) σ σ' b'⌝ -∗
      ( (wal_heap_inv γh) σ -∗ |NC={⊤ ∖↑ walN}=> (wal_heap_inv γh) σ' ∗ Q b' ) ).
Proof using walheapG0 Σ.
  iIntros "Ha".
  iIntros (σ σ' b') "% % Hinv".
  iNamed "Hinv".

  iMod "Ha" as (installed bs) "[Ha Hfupd]".
  iDestruct (ghost_map_lookup with "Hctx Ha") as "%".
  iDestruct (big_sepM_lookup with "Hgh") as "%"; eauto.

  simpl in *; monad_inv.
  simpl in *; monad_inv.

  match goal with
  | H : context[unwrap ?x] |- _ => destruct x eqn:?
  end.
  2: simpl in *; monad_inv; done.
  simpl in *; monad_inv.

  iDestruct ("Hfupd" $! b with "[Ha]") as "Hfupd".
  { rewrite /readinstalled_q. iFrame.
    iPureIntro.
    intuition.
    destruct H5 as [txn_id' ?]; intuition idtac. subst.
    eapply updates_since_apply_upds.
    3: eauto.
    3: eauto.
    all: simpl; try lia.
  }
  iMod "Hfupd".
  iModIntro.
  iFrame.
  destruct H1.
  intuition.
Qed.

Definition memappend_pre γh (bs : list update.t) (olds : list (Block * list Block)) : iProp Σ :=
  ([∗ list] _ ↦ u; old ∈ bs; olds,
    u.(update.addr) ↪[γh] (HB (fst old) (snd old)))%I.

Definition memappend_q γh (bs : list update.t) (olds : list (Block * list Block)) : iProp Σ :=
  ([∗ list] _ ↦ u; old ∈ bs; olds,
    u.(update.addr) ↪[γh] (HB (fst old) (snd old ++ [u.(update.b)])))%I.

Fixpoint memappend_gh (gh : gmap u64 heap_block) bs olds :=
  match bs, olds with
  | b :: bs, old :: olds =>
    memappend_gh (<[b.(update.addr) := HB old.1 (old.2 ++ [b.(update.b)])]> gh) bs olds
  | _, _ => gh
  end.

Theorem memappend_pre_in_gh γh (gh : gmap u64 heap_block) bs olds :
  ghost_map_auth γh 1 gh -∗
  memappend_pre γh bs olds -∗
  ⌜ ∀ u i,
      bs !! i = Some u ->
      ∃ old, olds !! i = Some old ∧
             gh !! u.(update.addr) = Some (HB (fst old) (snd old)) ⌝.
Proof.
  iIntros "Hctx Hmem % % %".
  rewrite /memappend_pre //.
  iDestruct (big_sepL2_lookup_1_some with "Hmem") as %Hv; eauto.
  destruct Hv.
  iDestruct (big_sepL2_lookup_acc with "Hmem") as "[Hx Hmem]"; eauto.
  iDestruct (ghost_map_lookup with "Hctx Hx") as %Hv.
  eauto.
Qed.

Lemma wal_heap_memappend_pre_to_q gh γh bs olds :
  ( ghost_map_auth γh 1 gh ∗
    memappend_pre γh bs olds )
  ==∗
  ( ghost_map_auth γh 1 (memappend_gh gh bs olds) ∗
    memappend_q γh bs olds ).
Proof.
  iIntros "(Hctx & Hpre)".
  iDestruct (big_sepL2_length with "Hpre") as %Hlen.

  iInduction (bs) as [|b] "Ibs" forall (gh olds Hlen).
  {
    iModIntro.
    rewrite /memappend_pre /memappend_q.
    destruct olds; simpl in *; try congruence.
    iFrame.
  }

  destruct olds; simpl in *; try congruence.
  iDestruct "Hpre" as "[Ha Hpre]".
  iDestruct (ghost_map_lookup with "Hctx Ha") as "%".

  iMod (ghost_map_update (HB p.1 (p.2 ++ [b.(update.b)])) with "Hctx Ha") as "[Hctx Ha]".

  iDestruct ("Ibs" $! _ olds with "[] Hctx Hpre") as "Hx".
  { iPureIntro. lia. }

  iMod "Hx" as "[Hctx Hq]".
  iModIntro.
  iFrame.
Qed.

Theorem memappend_pre_nodup γh (bs : list update.t) olds :
  memappend_pre γh bs olds -∗ ⌜NoDup (map update.addr bs)⌝.
Proof.
  iIntros "Hpre".
  iInduction bs as [|] "Hi" forall (olds).
  - simpl. iPureIntro. constructor.
  - iDestruct (big_sepL2_length with "Hpre") as %Hlen.
    destruct olds; simpl in *; try congruence.
    iDestruct "Hpre" as "[Ha Hpre]".
    iDestruct ("Hi" with "Hpre") as "%".

    iAssert (⌜update.addr a ∉ fmap update.addr bs⌝)%I as "%".
    {
      iClear "Hi".
      clear H Hlen.
      iInduction bs as [|] "Hi" forall (olds).
      + simpl. iPureIntro. apply not_elem_of_nil.
      + iDestruct (big_sepL2_length with "Hpre") as %Hlen.
        destruct olds; simpl in *; try congruence.
        iDestruct "Hpre" as "[Ha0 Hpre]".
        iDestruct ("Hi" with "Ha Hpre") as "%".
        destruct (decide (a.(update.addr) = a0.(update.addr))).
        {
          rewrite e.
          iDestruct (ghost_map_elem_valid_2 with "Ha Ha0") as %Hd.
          exfalso. apply Hd. simpl. auto.
        }
        iPureIntro.
        simpl.
        apply not_elem_of_cons.
        auto.
    }
    iPureIntro.
    eapply NoDup_cons_2; eauto.
Qed.

Lemma memappend_gh_not_in_bs : ∀ bs olds gh a,
  a ∉ fmap update.addr bs ->
  memappend_gh gh bs olds !! a = gh !! a.
Proof.
  induction bs; simpl; intros; eauto.
  destruct olds; eauto.
  apply not_elem_of_cons in H; intuition idtac.
  rewrite IHbs; eauto.
  rewrite lookup_insert_ne; eauto.
Qed.

Lemma memappend_gh_olds : ∀ bs olds gh i u old,
  bs !! i = Some u ->
  olds !! i = Some old ->
  NoDup (map update.addr bs) ->
  memappend_gh gh bs olds !! u.(update.addr) = Some (HB (fst old) (snd old ++ [u.(update.b)])).
Proof.
  induction bs; intros.
  { rewrite lookup_nil in H. congruence. }
  destruct olds.
  { rewrite lookup_nil in H0. congruence. }
  destruct i.
  { simpl. intros.
    inversion H; clear H; subst.
    inversion H0; clear H0; subst.
    rewrite memappend_gh_not_in_bs.
    { rewrite lookup_insert; eauto. }
    inversion H1; eauto.
  }

  simpl in *. intros.
  inversion H1.
  erewrite IHbs; eauto.
Qed.


Fixpoint apply_upds_u64 (d : gmap u64 Block) (upds : list update.t) : gmap u64 Block :=
  match upds with
  | nil => d
  | u :: upds' =>
    apply_upds_u64 (<[u.(update.addr) := u.(update.b)]> d) upds'
  end.

Lemma apply_upds_u64_insert bs : ∀ heapdisk u,
  u.(update.addr) ∉ map update.addr bs ->
  apply_upds_u64 (<[u.(update.addr) := u.(update.b)]> heapdisk) bs =
  <[u.(update.addr) := u.(update.b)]> (apply_upds_u64 heapdisk bs).
Proof.
  induction bs; intros; eauto.
  destruct a; simpl.
  destruct (decide (addr = u.(update.addr))); subst.
  - simpl in H. exfalso. apply H. apply elem_of_list_here.
  - rewrite -> insert_commute by eauto.
    rewrite IHbs; eauto.
    intro Hne. apply H. apply elem_of_list_further. eauto.
Qed.

Lemma apply_upds_u64_delete bs : ∀ heapdisk a,
  a ∉ map update.addr bs ->
  apply_upds_u64 (delete a heapdisk) bs =
  delete a (apply_upds_u64 heapdisk bs).
Proof.
  induction bs; intros; eauto.
  destruct a; simpl.
  destruct (decide (addr = a0)); subst.
  - simpl in H. exfalso. apply H. apply elem_of_list_here.
  - rewrite <- delete_insert_ne by eauto.
    rewrite IHbs; eauto.
    intro Hne. apply H. apply elem_of_list_further. eauto.
Qed.

(*
RJ:Lemma was unused; ghost map used here has a different type than
the one in the main ghost state...
Lemma apply_upds_u64_split heapdisk bs (γ: gname) (unmodified : gmap u64 heap_block) :
  NoDup (map update.addr bs) ->
  ( ∀ u, u ∈ bs -> unmodified !! u.(update.addr) = None ) ->
  ( ∀ l v, unmodified !! l = Some v → heapdisk !! l = Some v ) ->
  ⊢ ([∗ map] l↦v ∈ apply_upds_u64 heapdisk bs, l ↪[γ] v) -∗
    ([∗ map] l↦v ∈ unmodified, l ↪[γ] v) ∗
    ([∗ list] u ∈ bs, u.(update.addr) ↪[γ] u.(update.b)) : iProp Σ.
Proof.
  iIntros (Hnodup Hdisjoint Hinheapdisk) "Happly".
  iInduction bs as [|] "Hbs" forall (heapdisk Hinheapdisk); simpl.
  { iSplitL; last by done.
    iApply (big_sepM_subseteq with "Happly").
    apply map_subseteq_spec; eauto. }
  inversion Hnodup; subst.
  rewrite apply_upds_u64_insert; eauto.
  iDestruct (big_sepM_insert_delete with "Happly") as "[Ha Happly]". iFrame "Ha".
  rewrite -apply_upds_u64_delete; eauto.
  iDestruct ("Hbs" with "[] [] [] Happly") as "Happly"; last by iFrame.
  - eauto.
  - iPureIntro. intros. eapply Hdisjoint. eapply elem_of_list_further. eauto.
  - iPureIntro. intros. destruct (decide (l = a.(update.addr))); subst.
    + exfalso.
      rewrite Hdisjoint in H; try congruence.
      apply elem_of_list_here.
    + rewrite lookup_delete_ne; eauto.
Qed.
*)

Lemma apply_upds_u64_apply_upds bs :
  ∀ heapdisk d,
  ( ∀ (a : u64), heapdisk !! a = d !! uint.Z a ) ->
  ∀ (a : u64), apply_upds_u64 heapdisk bs !! a =
    apply_upds bs d !! uint.Z a.
Proof.
  induction bs; simpl; eauto; intros.
  destruct a; simpl.
  erewrite IHbs. { reflexivity. }
  intros a.
  destruct (decide (a = addr)); subst.
  - repeat rewrite lookup_insert. eauto.
  - rewrite -> lookup_insert_ne by eauto.
    rewrite H.
    rewrite lookup_insert_ne; eauto.
    intro Hne. apply n. word.
Qed.

Definition memappend_crash_pre γh (bs: list update.t) (crash_heaps: async (gmap u64 Block)) : iProp Σ :=
  "Hcrashheapsfrag" ∷ ghost_var γh.(wal_heap_crash_heaps) (3/4) crash_heaps.

Definition memappend_crash γh (bs: list update.t) (crash_heaps : async (gmap u64 Block)) lwh' : iProp Σ :=
  let new_crash_heap := apply_upds_u64 (latest crash_heaps) bs in
  is_locked_walheap γh lwh' ∗
  ghost_var γh.(wal_heap_crash_heaps) (3/4) (async_put (new_crash_heap) crash_heaps).

Lemma memappend_pre_addrs_wf (γ: gname) bs olds gh σ :
  memappend_pre γ bs olds -∗
  ghost_map_auth γ 1 gh -∗
  ([∗ map] a↦b ∈ gh, wal_heap_inv_addr σ a b) -∗
  ⌜addrs_wf bs σ.(log_state.d)⌝.
Proof.
  iIntros "Hpre Hctx Hinv".
  rewrite /addrs_wf.
  setoid_rewrite Forall_forall.
  iIntros (x Hx).
  eapply elem_of_list_lookup_1 in Hx.
  destruct Hx as [i Hx].
  rewrite /memappend_pre.
  iDestruct (big_sepL2_lookup_1_some with "Hpre") as (o) "%Holds"; eauto.
  iDestruct (big_sepL2_lookup with "Hpre") as "Hp"; eauto.
  iDestruct (ghost_map_lookup with "Hctx Hp") as "%Hv".
  iDestruct (big_sepM_lookup with "Hinv") as "%Hinv"; eauto.
  intuition eauto.
Qed.

Lemma ghost_var_update_parts {A} `{!ghost_varG Σ A} (b:A) (γ: gname) q1 q2 (a1 a2: A) :
  (q1 + q2 = 1)%Qp →
  ghost_var γ q1 a1 -∗
  ghost_var γ q2 a2 ==∗
  ghost_var γ q1 b ∗ ghost_var γ q2 b.
Proof.
  intros Hsum.
  iApply ghost_var_update_2.
  done.
Qed.

Lemma dom_memappend_gh_unchanged gh bs olds :
  (∀ u, u ∈ bs → u.(update.addr) ∈ dom gh)  →
  dom (memappend_gh gh bs olds) =
  dom gh.
Proof.
  generalize dependent olds.
  generalize dependent gh.
  induction bs; simpl; intros; auto.
  destruct olds; auto.
  rewrite IHbs.
  - set_solver.
  - set_solver.
Qed.

Theorem wal_heap_memappend E γh bs (Q : u64 -> iProp Σ) (PreQ : iProp Σ) (PreQ' : iProp Σ) lwh :
  PreQ' ∧ ( ∀ σ, PreQ ∗ is_locked_walheap γh lwh ∗ wal_heap_inv γh σ -∗ |NC={⊤ ∖ ↑walN, E}=>
      ∃ olds crash_heaps,
        |NC={E}=>
        memappend_pre γh.(wal_heap_h) bs olds ∗
        memappend_crash_pre γh bs crash_heaps ∗
        is_locked_walheap γh lwh ∗
        wal_heap_inv γh σ ∗
        ( ∀ pos,
            memappend_crash γh bs crash_heaps (Build_locked_walheap (locked_wh_σd lwh) (locked_wh_σtxns lwh ++ [(pos, bs)])) ∗
            memappend_q γh.(wal_heap_h) bs olds
          -∗ |NC={E, ⊤ ∖ ↑walN}=> txn_pos γh.(wal_heap_walnames) (length (possible crash_heaps)) pos -∗ Q pos ) ) -∗
  is_locked_walheap γh lwh -∗
  PreQ -∗
  ( ( ∀ σ σ' txn_id,
      ⌜wal_wf σ⌝ -∗
      ⌜relation.denote (log_mem_append bs) σ σ' txn_id⌝ -∗
        let txn_num := length σ.(log_state.txns) in
      ( (wal_heap_inv γh) σ
          -∗ |NC={⊤ ∖↑ walN}=> ⌜addrs_wf bs σ.(log_state.d)⌝ ∗ (wal_heap_inv γh) σ' ∗ (txn_pos γh.(wal_heap_walnames) txn_num txn_id -∗ Q txn_id)) ) ∧
    ( "Hlockedheap" ∷ is_locked_walheap γh lwh ∗ PreQ ∗ PreQ' )).
Proof using walheapG0.
  iIntros "Hpre Hlockedheap HpreQ".
  iSplit; last first.
  { iFrame. iLeft in "Hpre". iFrame. }

  iIntros (σ σ' pos) "% % Hinv".

  simpl in *; monad_inv.
  simpl in *.

  iDestruct "Hpre" as "[_ Hpre]".
  iDestruct ("Hpre" with "[$Hinv $HpreQ $Hlockedheap]") as "Hpre".

  iMod "Hpre" as (olds crash_heaps0) "Hpre".
  iMod "Hpre" as "(Hpre & Hprecrash & Hlockedheap & Hinv & Hfupd)".
  iNamed "Hprecrash".
  iNamed "Hinv".

  iDestruct (memappend_pre_addrs_wf with "Hpre Hctx Hgh") as %Haddrswf.

  iDestruct (memappend_pre_nodup with "Hpre") as %Hnodup.

  iDestruct (big_sepL2_length with "Hpre") as %Hlen.
  iDestruct (memappend_pre_in_gh with "Hctx Hpre") as %Hbs_in_gh.

  iMod (wal_heap_memappend_pre_to_q with "[$Hctx $Hpre]") as "[Hctx Hq]".

  iDestruct (ghost_var_agree with "Htxns Hlockedheap") as "%Hagree".
  inversion Hagree; clear Hagree. subst.

  iMod (ghost_var_update_halves (σ.(log_state.d), σ.(log_state.txns) ++ [(pos', bs)]) with "Htxns Hlockedheap") as "[Htxns Hlockedheap]".

  iNamed "Hcrash_heaps".
  rewrite /memappend_crash_pre. iNamed "Hprecrash".
  iDestruct (ghost_var_agree with "Hcrash_heaps_own Hcrashheapsfrag") as %<-.
  iDestruct "Hpossible_heaps" as "#Hpossible_heaps".
  iDestruct (big_sepL_app with "Hpossible_heaps") as "[_ Hlatest]".
  simpl.
  iDestruct "Hlatest" as "[Hlatest _]".
  rewrite /wal_heap_inv_crash.
  iNamed "Hlatest".

  iMod (ghost_var_update_parts (async_put (apply_upds_u64 (latest crash_heaps) bs) crash_heaps) with "Hcrash_heaps_own Hcrashheapsfrag") as "[Hcrash_heaps_own Hcrashheapsfrag]".
  { rewrite Qp.quarter_three_quarter //. }

  iSpecialize ("Hfupd" $! (pos')).

  iDestruct ("Hfupd" with "[$Hlockedheap $Hq $Hcrashheapsfrag]") as "Hfupd".
  iMod "Hfupd".

  iModIntro.
  iSplitR; first by done.
  clear Haddrswf.
  iSplitR "Hfupd".
  2: {
    iIntros "Hpos".
    iApply "Hfupd".
    iExactEq "Hpos". f_equal.
    eauto.
  }

  iExists _, _.
  iFrame.
  iSplit.
  { simpl; eauto.
    rewrite dom_memappend_gh_unchanged //.
    intros u Hin.
    move: Hbs_in_gh Hin.
    clear.
    rewrite elem_of_list_lookup elem_of_dom.
    naive_solver. }
  iDestruct (big_sepM_forall with "Hgh") as %Hgh.
  iSplitL.
  2: iSplit.
  2: {
    iPureIntro. eapply wal_wf_append_txns; simpl; eauto.
    { unfold addrs_wf.
      intros.
      apply Forall_lookup; intros i u.
      specialize (Hbs_in_gh u i).
      intuition eauto.
      destruct H4 as [old ?]; eauto.
      specialize (Hgh (u.(update.addr)) (HB old.1 old.2)).
      intuition; auto. }
    intros. apply H1 in H0. lia.
  }
  2: {
    rewrite /possible app_length /= in Hcrashes_complete.
    rewrite -> firstn_all2 in Hcrashheap_contents by lia.

    iSplitR.
    { iPureIntro. rewrite /= /async_put /possible app_length /= ?app_length /=. lia. }
    rewrite /async_put /possible /=.
    iApply big_sepL_app.
    iSplit.
    2: { iSplitL; last by done.
      rewrite firstn_all2.
      2: { rewrite app_length -Hcrashes_complete /possible app_length /=. lia. }
      iPureIntro. intros a0. simpl.
      rewrite txn_upds_app apply_upds_app /=.
      unfold txn_upds at 1; simpl. rewrite app_nil_r.
      eapply apply_upds_u64_apply_upds; eauto.
    }
    iApply big_sepL_app.
    iDestruct (big_sepL_app with "Hpossible_heaps") as "[H0 H1]".
    iSplit.
    { iApply (big_sepL_mono with "H0").
      iIntros (k h Hkh) "H".
      rewrite take_app_le; first by iFrame.
      apply lookup_lt_Some in Hkh. lia. }
    iSplitL; last by done.
    rewrite -> take_app_length' by lia.
    eauto.
  }

  intuition.
  iApply big_sepM_forall.
  iIntros (k b Hkb).
  destruct b.
  iPureIntro.
  simpl.
  specialize (Hgh k).

  destruct (decide (k ∈ fmap update.addr bs)).
  - eapply elem_of_list_fmap in e as ex.
    destruct ex as [y [-> ?]].
    apply elem_of_list_lookup in H0; destruct H0.
    edestruct Hbs_in_gh; eauto.
    destruct H4.
    specialize (Hgh _ H5). simpl in *.
    destruct Hgh as [addr_wf Hgh].
    destruct Hgh as [txn_id' Hgh].
    intuition; auto.
    exists txn_id'.

    pose proof Hkb as Hkb'.
    erewrite memappend_gh_olds in Hkb'; eauto.
    inversion Hkb'; clear Hkb'; subst.
    intuition.

    {
      rewrite -disk_at_txn_id_append; eauto.
      unfold wal_wf in Hwf; intuition.
      lia.
    }

    {
      etransitivity; first apply updates_since_updates; auto.
      erewrite updates_for_addr_in; eauto.
      f_equal; auto.
    }

  - rewrite memappend_gh_not_in_bs in Hkb; eauto.
    specialize (Hgh _ Hkb).
    simpl in *.

    destruct Hgh as [wf_addr Hgh].
    destruct Hgh as [pos Hgh].
    intuition; auto.
    exists pos.
    intuition.

    {
      rewrite -disk_at_txn_id_append; eauto.
      unfold wal_wf in Hwf; intuition.
      lia.
    }

    {
      rewrite -H6.
      etransitivity; first apply updates_since_updates; auto.
      erewrite updates_for_addr_notin; eauto.
      rewrite app_nil_r; auto.
    }
Qed.

Theorem no_updates_since_le σ a t0 t1 :
  (t0 ≤ t1)%nat ->
  no_updates_since σ a t0 ->
  no_updates_since σ a t1.
Proof.
  rewrite /no_updates_since /txn_upds; intros.
  eapply incl_Forall; eauto.
  unfold log_state.txns.
  destruct σ.
  simpl in *.
  repeat rewrite fmap_drop.
  apply incl_concat.
  unfold incl.
  intros.
  eapply in_drop_ge; [ | eauto ]; lia.
Qed.

Lemma wal_heap_inv_pointsto_in_bounds γ dq walptr wn dinit a v E :
  ↑walN.@"wal" ⊆ E ->
  is_wal (wal_heap_inv γ) walptr wn dinit -∗
  a ↪[γ.(wal_heap_h)] {dq} v -∗ |NC={E}=>
  a ↪[γ.(wal_heap_h)] {dq} v ∗
  in_bounds wn a.
Proof.
  iIntros (HE) "#Hwal Hmapsto".
  iDestruct "Hwal" as "[Hwal _]".
  iInv "Hwal" as "Hwal_open".
  iAssert (◇ in_bounds wn a)%I as "#>Ha".
  { iDestruct "Hwal_open" as (σ) "[Hwalinner >Hheapinv]".
    iDestruct (is_wal_inner_base_disk with "Hwalinner") as "#>Hbasedisk".
    iNamed "Hheapinv".
    iDestruct (ghost_map_lookup with "Hctx Hmapsto") as "%Hvalid".
    iDestruct (big_sepM_lookup with "Hgh") as "%Ha"; eauto.
    iExists _. iFrame "Hbasedisk". iPureIntro.
    destruct Ha as [Ha _]. destruct Ha as [_ Ha]. destruct Ha as [b Ha].
    eauto. }
  by iFrame "∗#".
Qed.

Lemma apply_upds_wf_some σ (a : u64) :
  wal_wf σ ->
  is_Some (apply_upds (txn_upds σ.(log_state.txns)) σ.(log_state.d) !! uint.Z a) ->
  is_Some (σ.(log_state.d) !! uint.Z a).
Proof.
  rewrite /wal_wf /addrs_wf. intuition.
  destruct H0.
  eapply lookup_apply_upds in H0; intuition eauto.
  rewrite /log_state.updates in H1.
  destruct H3. intuition subst.
  eapply Forall_forall in H1; eauto.
  destruct H1. destruct H1. eauto.
Qed.

Lemma wal_heap_inv_apply_upds_in_bounds γ walptr dinit wn σd σtxns a b :
  apply_upds (txn_upds σtxns) σd !! uint.Z a = Some b ->
  is_wal (wal_heap_inv γ) walptr wn dinit -∗
  ghost_var γ.(wal_heap_txns) (1 / 2) (σd, σtxns) -∗ |NC={⊤}=>
  ghost_var γ.(wal_heap_txns) (1 / 2) (σd, σtxns) ∗
  in_bounds wn a.
Proof.
  iIntros (Happly) "#Hwal H".
  iDestruct "Hwal" as "[Hwal _]".
  iInv "Hwal" as "Hwal_open".
  iDestruct "Hwal_open" as (σ) "[Hwalinner >Hheapinv]".
  iDestruct (is_wal_inner_base_disk with "Hwalinner") as "#>Hbasedisk".
  iAssert (▷ in_bounds wn a)%I with "[-]" as "#Ha".
  2: {
    iModIntro. iSplitL "Hwalinner Hheapinv".
    { iNext. iExists _. iFrame. }
    iDestruct "Ha" as ">Ha".
    iModIntro. iFrame "Ha". done. }
  iModIntro.
  iExists _. iFrame "Hbasedisk".
  iNamed "Hheapinv".
  iDestruct (ghost_var_agree with "H Htxns") as "%Heq".
  inversion Heq; clear Heq; subst.
  iPureIntro.
  eapply apply_upds_wf_some; eauto.
Qed.

Theorem wp_Walog__Read l (blkno : u64) γ lwh b wn dinit :
  {{{ is_wal (wal_heap_inv γ) l wn dinit ∗
      is_locked_walheap γ lwh ∗
      ⌜ locked_wh_disk lwh !! uint.Z blkno = Some b ⌝
  }}}
    wal.Walog__Read #l #blkno
  {{{ bl, RET (slice_val bl);
      is_locked_walheap γ lwh ∗
      is_block bl (DfracOwn 1) b
  }}}.
Proof using walheapG0.
  iIntros (Φ) "(#Hwal & Htxnsfrag & %Hb) HΦ".
  wp_call.
  unfold locked_wh_disk in *.
  destruct lwh as [σd σtxns].
  unfold is_locked_walheap in *. simpl in *.

  iMod (wal_heap_inv_apply_upds_in_bounds with "Hwal Htxnsfrag") as "[Htxnsfrag #Hinbounds]"; eauto.

  wp_apply (wp_Walog__ReadMem _
    (λ mb,
      match mb with
      | Some b' => ghost_var γ.(wal_heap_txns) (1/2) (σd, σtxns) ∗ ⌜ b' = b ⌝
      | None =>
        ∀ (σ σ' : log_state.t) (b0 : Block),
          ⌜wal_wf σ⌝
          -∗ ⌜relation.denote (log_read_installed blkno) σ σ' b0⌝
             -∗ wal_heap_inv γ σ
                -∗ |NC={⊤ ∖ ↑walN}=> wal_heap_inv γ σ'
                            ∗ ghost_var γ.(wal_heap_txns) (1/2) (σd, σtxns) ∗ ⌜b0 = b⌝
      end
    )%I with "[$Hwal Htxnsfrag]").
  { iIntros (σ σ' mb) "%Hwal_wf %Hrelation Hwalinv".
    iNamed "Hwalinv".
    iDestruct (ghost_var_agree with "Htxns Htxnsfrag") as "%Hagree".
    inversion Hagree; clear Hagree; subst.

    simpl in *; monad_inv.
    destruct x.
    {
      simpl in *; monad_inv.
      simpl in *; monad_inv.

      unfold last_disk in Hrelation.
      unfold disk_at_txn_id in Hrelation.
      rewrite -> take_ge in Hrelation by lia.
      rewrite Hb in Hrelation.

      simpl in *; monad_inv.

      iModIntro. iFrame. iSplitL; done.
    }
    {
      simpl in *; monad_inv.
      simpl in *; monad_inv.

      iMod (mono_nat_own_update new_installed with "Hinstalled") as "[Hinstalled #Hinstalledfrag]".
      { intuition idtac. }
      iMod (mono_nat_own_update new_durable with "Hcrash_heaps_lb") as "[Hcrash_heaps_lb _]".
      { lia. }

      iModIntro.
      iSplitL "Hctx Hgh Htxns Hinstalled Hcrash_heaps_own Hcrash_heaps Hcrash_heaps_lb".
      { iExists _, _. iFrame.
        iSplit.
        { simpl; auto. }
        iSplitL "Hgh".
        {
          iApply wal_update_installed; first by intuition lia.
          iApply wal_update_durable; first by intuition lia.
          iFrame. }
        iPureIntro.
        eapply wal_wf_advance_installed_lb; last by (intuition; simpl; lia).
        eapply wal_wf_advance_durable_lb; eauto.
      }

      iIntros (σ0 σ1 b0) "%Hwf' %Hrelation Hwalinv".
      simpl in *; monad_inv.
      simpl in *; monad_inv.
      match goal with
      | H : context[unwrap ?x] |- _ => destruct x eqn:?
      end.
      2: simpl in *; monad_inv.
      simpl in *; monad_inv.

      iNamed "Hwalinv".
      iDestruct (ghost_var_agree with "Htxns Htxnsfrag") as "%Hagree".
      inversion Hagree; clear Hagree; subst.
      rewrite <- H5 in Hb.
      rewrite <- H6 in Hb.

      iDestruct (mono_nat_lb_own_valid with "Hinstalled Hinstalledfrag") as %[_ Hle].

      rewrite no_updates_since_last_disk in Heqo; eauto.
      2: {
        rewrite /no_updates_since. rewrite H6.
        eapply no_updates_since_le; last by eauto.
        lia.
      }

      unfold last_disk in Heqo.
      unfold disk_at_txn_id in Heqo.
      rewrite -> take_ge in Heqo by lia.
      rewrite Hb in Heqo.
      inversion Heqo; subst.

      iModIntro. iFrame. iSplitL; done.
    }
  }

  iIntros (ok bl) "Hbl".
  destruct ok.
  {
    iDestruct "Hbl" as (b') "(Hbl & Hlatestfrag & ->)".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
  {
    wp_pures.
    wp_apply (wp_Walog__ReadInstalled _
      (λ b', ghost_var γ.(wal_heap_txns) (1/2) (σd, σtxns) ∗ ⌜ b' = b ⌝)%I
      with "[$Hwal $Hbl]").
    { iFrame "#". }
    iIntros (bli) "Hbli".
    iDestruct "Hbli" as (b0) "(Hb0 & Hlatestfrag & ->)".
    iApply "HΦ". by iFrame.
  }
Qed.

Theorem wal_heap_pointsto_latest_helper γ dq lwh (a : u64) (v : heap_block) σ :
  wal_heap_inv γ σ ∗
  is_locked_walheap γ lwh ∗
  a ↪[γ.(wal_heap_h)] {dq} v -∗
  ⌜ locked_wh_disk lwh !! uint.Z a = Some (hb_latest_update v) ⌝.
Proof.
  iIntros "(Hheap & Htxnsfrag & Hmapsto)".
  iNamed "Hheap".
  iDestruct (ghost_var_agree with "Htxns Htxnsfrag") as "%Hagree".
  inversion Hagree; clear Hagree; subst.
  iDestruct (ghost_map_lookup with "Hctx Hmapsto") as "%Hvalid".
  iDestruct (big_sepM_lookup with "Hgh") as "%Hvalid_gh"; eauto.
  destruct v.
  destruct Hvalid_gh as [wf_addr Hvalid_gh].
  destruct Hvalid_gh; intuition idtac.
  iPureIntro.
  eapply updates_since_to_last_disk in H; eauto.
  rewrite /last_disk /disk_at_txn_id take_ge in H; last by lia.
  rewrite /locked_wh_disk. rewrite -H0 -H1 /=. congruence.
Qed.

Theorem wal_heap_pointsto_latest γ l lwh (a : u64) (v : heap_block) E wn dinit :
  ↑walN ⊆ E ->
  is_wal (wal_heap_inv γ) l wn dinit ∗
  is_locked_walheap γ lwh ∗
  a ↪[γ.(wal_heap_h)] v -∗ |NC={E}=>
    is_locked_walheap γ lwh ∗
    a ↪[γ.(wal_heap_h)] v ∗
    ⌜ locked_wh_disk lwh !! uint.Z a = Some (hb_latest_update v) ⌝.
Proof.
  iIntros (HNE) "(#Hwal & Htxnsfrag & Hmapsto)".
  iMod (is_wal_open with "Hwal") as (σ) "[>Hheap Hclose]"; first by solve_ndisj.
  iDestruct (wal_heap_pointsto_latest_helper with "[$Hheap $Htxnsfrag $Hmapsto]") as %Hx.
  iMod ("Hclose" with "Hheap").
  iModIntro.
  by iFrame.
Qed.

Theorem wp_Walog__Flush_heap l γ dinit (txn_id : nat) (pos : u64) :
  {{{ is_wal (wal_heap_inv γ) l (wal_heap_walnames γ) dinit ∗
      txn_pos (wal_heap_walnames γ) txn_id pos
  }}}
    wal.Walog__Flush #l #pos
  {{{ RET #();
      mono_nat_lb_own γ.(wal_heap_durable_lb) txn_id
  }}}.
Proof using walheapG0.
  iIntros (Φ) "(#Hwal & Hpos) HΦ".
  wp_apply (wp_Walog__Flush with "[$Hwal $Hpos]").
  2: { iIntros "H". iApply "HΦ". iExact "H". }
  iIntros (σ σ' r Hwf Htransition) "Hinv".

  simpl in *; monad_inv.
  intuition idtac.

  iNamed "Hinv".
  iMod (mono_nat_own_update new_durable with "Hcrash_heaps_lb") as "[Hcrash_heaps_lb #Hlb]".
  { lia. }
  iDestruct (mono_nat_lb_own_le txn_id with "Hlb") as "#Hpost".
  { lia. }
  iFrame "Hpost".

  iModIntro.
  iExists _, _. iFrame.
  iSplit.
  { simpl; auto. }
  iPureIntro.
  eapply wal_wf_advance_durable_lb; eauto. lia.
Qed.

Theorem lwh_crash_heaps γ σ crash_heaps lwh :
  ghost_var γ.(wal_heap_crash_heaps) (3 / 4) crash_heaps -∗
  is_locked_walheap γ lwh -∗
  wal_heap_inv γ σ -∗
  ∃ installed_lb durable_lb,
    wal_heap_inv_crashes crash_heaps
      {|
        log_state.d := lwh.(locked_wh_σd);
        log_state.txns := lwh.(locked_wh_σtxns);
        log_state.installed_lb := installed_lb;
        log_state.durable_lb := durable_lb |}.
Proof.
  iIntros "Hch Hlwh Hinv".
  iNamed "Hinv".
  iDestruct (ghost_var_agree with "Hch Hcrash_heaps_own") as %<-.
  destruct σ; simpl.
  iDestruct (ghost_var_agree with "Hlwh Htxns") as "%Hlwh".
  inversion Hlwh; clear Hlwh; subst.
  iExists _, _. by iFrame.
Qed.

End heap.
