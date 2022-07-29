From Perennial.program_proof Require Export grove_prelude.
From Perennial.program_proof.mvcc Require Import mvcc_ghost proph_proof.

(* Invariant namespaces. *)
Definition mvccN := nroot.
Definition mvccNTuple := nroot .@ "tuple".
Definition mvccNGC := nroot .@ "gc".
Definition mvccNSST := nroot .@ "sst".

Section def.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(* GC invariants. *)
Definition mvcc_inv_gc_def γ : iProp Σ :=
  [∗ list] sid ∈ sids_all,
    ∃ (tids : gmap u64 unit) (tidmin : u64),
      site_active_tids_half_auth γ sid tids ∗
      site_min_tid_half_auth γ sid (int.nat tidmin) ∗
      ∀ tid, ⌜tid ∈ (dom tids) -> (int.nat tidmin) ≤ (int.nat tid)⌝.

Definition mvcc_inv_gc γ : iProp Σ :=
  inv mvccNGC (mvcc_inv_gc_def γ).

(* SST invariants. *)
(* TODO *)
Definition ptuple_past_rel (key : u64) (phys : list dbval) (past : list action) : Prop.
Admitted.

Definition per_key_inv_def
           (γ : mvcc_names) (key : u64) (tmods : gset (nat * dbmap))
           (ts : nat) (m : dbmap) (past : list action)
  : iProp Σ :=
  ∃ (phys logi : list dbval),
    "Hptuple" ∷ ptuple_auth γ (1 / 2) key phys ∗
    "Hltuple" ∷ ltuple_auth γ key logi ∗
    "%Htmrel" ∷ ⌜tuple_mods_rel phys logi (per_tuple_mods tmods key)⌝ ∗
    "%Hpprel" ∷ ⌜ptuple_past_rel key phys past⌝ ∗
    "%Hlmrel" ∷ ⌜last logi = m !! key⌝ ∗
    "%Htsge"  ∷ ⌜length logi ≤ S ts⌝.

Definition cmt_inv_def
           (γ : mvcc_names) (tmods : gset (nat * dbmap)) (future : list action)
  : iProp Σ :=
  "HcmtAuth" ∷ cmt_tmods_auth γ tmods ∗
  "%Hcmt"    ∷ ⌜set_Forall (uncurry (first_commit_compatible future)) tmods⌝.

Definition nca_inv_def
           (γ : mvcc_names) (tids : gset nat) (future : list action)
  : iProp Σ :=
  "HncaAuth" ∷ nca_tids_auth γ tids ∗
  "%Hnca"    ∷ ⌜set_Forall (no_commit_abort future) tids⌝.

Definition fa_inv_def
           (γ : mvcc_names) (tids : gset nat) (future : list action)
  : iProp Σ :=
  "HfaAuth" ∷ fa_tids_auth γ tids ∗
  "%Hfa"    ∷ ⌜set_Forall (first_abort future) tids⌝.

Definition fci_inv_def
           (γ : mvcc_names) (tmods : gset (nat * dbmap)) (past future : list action)
  : iProp Σ :=
  "HfciAuth" ∷ fci_tmods_auth γ tmods ∗
  "%Hfci"    ∷ ⌜set_Forall (uncurry (first_commit_incompatible (past ++ future))) tmods⌝.

Definition fcc_inv_def
           (γ : mvcc_names) (tmods : gset (nat * dbmap)) (future : list action)
  : iProp Σ :=
  "HfccAuth" ∷ fcc_tmods_auth γ tmods ∗
  "%Hfcc"    ∷ ⌜set_Forall (uncurry (first_commit_compatible future)) tmods⌝.

Definition mvcc_inv_sst_def γ p : iProp Σ :=
  ∃ (tids_nca tids_fa : gset nat)
    (tmods_fci tmods_fcc tmods : gset (nat * dbmap))
    (ts : nat) (m : dbmap) (past future : list action),
    (* Prophecy. *)
    "Hproph" ∷ mvcc_proph γ p future ∗
    (* Current timestamp. *)
    "Hts" ∷ ts_auth γ ts ∗
    (* Global database map, i.e., auth element of the global ptsto. *)
    "Hm" ∷ dbmap_auth γ m ∗
    (* Per-key invariants. *)
    "Hkeys" ∷ ([∗ set] key ∈ keys_all, per_key_inv_def γ key tmods ts m past) ∗
    (* Ok txns. *)
    "Hcmt"  ∷ cmt_inv_def γ tmods future ∗
    (* Doomed txns. *)
    "Hnca"  ∷ nca_inv_def γ tids_nca future ∗
    "Hfa"   ∷ fa_inv_def  γ tids_fa future ∗
    "Hfci"  ∷ fci_inv_def γ tmods_fci past future ∗
    "Hfcc"  ∷ fcc_inv_def γ tmods_fcc future.

Instance mvcc_inv_sst_timeless γ p :
  Timeless (mvcc_inv_sst_def γ p).
Proof. unfold mvcc_inv_sst_def. apply _. Defined.

Definition mvcc_inv_sst γ p : iProp Σ :=
  inv mvccNSST (mvcc_inv_sst_def γ p).

End def.

Hint Extern 1 (environments.envs_entails _ (mvcc_inv_sst_def _ _)) => unfold mvcc_inv_sst_def : core.

Section theorem.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem active_ge_min γ (tid tidlb : u64) (sid : u64) :
  mvcc_inv_gc_def γ -∗
  active_tid γ tid sid -∗
  min_tid_lb γ (int.nat tidlb) -∗
  ⌜int.Z tidlb ≤ int.Z tid⌝.
Proof using heapGS0 mvcc_ghostG0 Σ.
  (* Q: How to remove [using]? *)
  iIntros "Hinv Hactive Hlb".
  iDestruct "Hactive" as "[[Htid %Hlookup] _]".
  apply sids_all_lookup in Hlookup.
  apply elem_of_list_lookup_2 in Hlookup.
  iDestruct (big_sepL_elem_of with "Hlb") as "Htidlb"; first done.
  iDestruct (big_sepL_elem_of with "Hinv") as (tids tidmin) "(Htids & Htidmin & %Hle)"; first done.
  (* Obtaining [tidmin ≤ tid]. *)
  iDestruct (site_active_tids_elem_of with "Htids Htid") as "%Helem".
  apply Hle in Helem.
  (* Obtaining [tidlb ≤ tidmin]. *)
  iDestruct (site_min_tid_valid with "Htidmin Htidlb") as "%Hle'".
  iPureIntro.
  apply Z.le_trans with (int.Z tidmin); word.
Qed.

Definition tuple_auth_prefix (γ : mvcc_names) (key : u64) : iProp Σ :=
  ∃ (phys logi : list dbval),
    "Hptuple" ∷ ptuple_auth γ (1 / 2) key phys ∗
    "Hltuple" ∷ ltuple_auth γ key logi ∗
    "%prefix" ∷ ⌜prefix phys logi⌝.

Lemma per_key_inv_tuple_acc γ key tmods ts m past :
  per_key_inv_def γ key tmods ts m past -∗
  tuple_auth_prefix γ key ∗
  (tuple_auth_prefix γ key -∗ per_key_inv_def γ key tmods ts m past).
Admitted.

Lemma per_key_inv_weaken_ts {γ key tmods ts} ts' {m past} :
  (ts ≤ ts')%nat ->
  per_key_inv_def γ key tmods ts m past -∗
  per_key_inv_def γ key tmods ts' m past.
Admitted.

Lemma per_key_inv_ltuple_ptsto γ tmods ts m past :
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts m past) ==∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts m past ∗
                         (∀ v, ⌜m !! k = Some v⌝ -∗ ltuple_ptsto γ k v ts)).
Proof.
  iIntros "Hkeys".
  iApply big_sepS_bupd.
  iApply (big_sepS_mono with "Hkeys").
  iIntros (k) "%Helem Hkey".
  iNamed "Hkey".
  iMod (ltuple_update (extend (S ts) logi) with "Hltuple") as "Hltuple".
  { apply extend_prefix. }
  iModIntro.
  iDestruct (ltuple_witness with "Hltuple") as "#Hlb".
  iSplitL.
  { do 2 iExists _.
    apply tuple_mods_rel_last_logi in Htmrel as Hlogi.
    apply (tuplext_linearize_unchanged ts) in Htmrel.
    iFrame "% ∗".
    iPureIntro.
    split.
    { rewrite -Hlmrel. apply extend_last. }
    { rewrite extend_length; [lia | auto]. }
  }
  iIntros (v) "%Hlookup".
  iExists _.
  iFrame "Hlb".
  iPureIntro.
  rewrite Hlookup in Hlmrel.
  rewrite (extend_last_Some _ _ v); last auto.
  destruct (decide (length logi ≤ ts)%nat).
  - rewrite lookup_app_r; last auto.
    apply lookup_replicate_2. lia.
  - apply not_le in n.
    rewrite lookup_app_l; last lia.
    rewrite last_lookup in Hlmrel.
    rewrite -Hlmrel.
    f_equal. lia.
Qed.

Lemma big_sepS_big_sepM_ltuple_ptstos γ tid m :
  ([∗ set] k ∈ keys_all, (∀ v, ⌜m !! k = Some v⌝ -∗ ltuple_ptsto γ k v tid)) -∗
  ([∗ map] k ↦ v ∈ m, ltuple_ptsto γ k v tid).
Proof.
  iIntros "Hset".
  (* Q: We should be able to prove this without persistence. *)
  rewrite big_sepM_forall.
  rewrite big_sepS_forall.
  iIntros (k v) "%Hlookup".
  iApply "Hset"; last done.
  iPureIntro.
  apply elem_of_fin_to_set.
Qed.

Theorem per_key_inv_ltuple_ptstos γ tmods tid m past :
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods tid m past) ==∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods tid m past) ∗
  ([∗ map] k ↦ v ∈ m, ltuple_ptsto γ k v tid).
Proof.
  iIntros "Hkeys".
  iMod (per_key_inv_ltuple_ptsto with "Hkeys") as "Hkeys".
  rewrite big_sepS_sep.
  iDestruct "Hkeys" as "[Hkeys Hltuples]".
  iDestruct (big_sepS_big_sepM_ltuple_ptstos with "Hltuples") as "Hltuples".
  by iFrame.
Qed.
                         
Theorem ltuple_ptuple_ptsto_eq γ k v1 v2 ts:
  tuple_auth_prefix γ k -∗
  ltuple_ptsto γ k v1 ts -∗
  ptuple_ptsto γ k v2 ts -∗
  ⌜v1 = v2⌝.
Admitted.

Theorem nca_inv_head_read γ l l' tid key tids :
  l = EvRead tid key :: l' ->
  nca_inv_def γ tids l -∗
  nca_inv_def γ tids l'.
Admitted.

Theorem fa_inv_head_read γ l l' tid key tids :
  l = EvRead tid key :: l' ->
  fa_inv_def γ tids l -∗
  fa_inv_def γ tids l'.
Admitted.

Theorem fci_inv_head_read γ p l l' tid key tmods :
  l = EvRead tid key :: l' ->
  fci_inv_def γ tmods p l -∗
  fci_inv_def γ tmods (p ++ [EvRead tid key]) l'.
Admitted.

Theorem fcc_inv_head_read γ l l' tid key tmods :
  l = EvRead tid key :: l' ->
  fcc_inv_def γ tmods l -∗
  fcc_inv_def γ tmods l'.
Proof.
  iIntros "%Hl Hfcc".
  iNamed "Hfcc".
  iFrame.
  iPureIntro.
  apply (set_Forall_impl _ _ _ Hfcc).
  intros tmod H.
  destruct tmod as [t m].
  simpl in *.
  by apply (first_commit_compatible_preserved Hl); first auto.
Qed.

Theorem cmt_inv_head_read γ l l' tid key tmods :
  l = EvRead tid key :: l' ->
  cmt_inv_def γ tmods l -∗
  cmt_inv_def γ tmods l'.
Admitted.

End theorem.
