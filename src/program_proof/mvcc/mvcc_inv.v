From Perennial.program_proof.mvcc Require Import mvcc_prelude.
From Perennial.program_proof.mvcc Require Import mvcc_ghost mvcc_misc mvcc_action mvcc_tuplext proph_proof.

Section def.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(* GC invariants. *)
Definition mvcc_inv_gc_site_def γ (sid : u64) : iProp Σ :=
  ∃ (tids : gset nat) (tidmin tidmax : nat),
    "HactiveA" ∷ site_active_tids_half_auth γ sid tids ∗
    "HminA"    ∷ site_min_tid_auth γ sid tidmin ∗
    "#Htslb"   ∷ ts_lb γ tidmax ∗
    "%Hmin"    ∷ ⌜set_Forall (λ tid, tidmin ≤ tid)%nat tids⌝ ∗
    "%Hmax"    ∷ ⌜set_Forall (λ tid, tid ≤ tidmax)%nat ({[ tidmin ]} ∪ tids)⌝.

Definition mvcc_inv_gc_def γ : iProp Σ :=
  [∗ list] sid ∈ sids_all, mvcc_inv_gc_site_def γ sid.

Instance mvcc_inv_gc_timeless γ :
  Timeless (mvcc_inv_gc_def γ).
Proof. unfold mvcc_inv_gc_def. apply _. Defined.

Definition mvcc_inv_gc γ : iProp Σ :=
  inv mvccNGC (mvcc_inv_gc_def γ).

(* SST invariants. *)
Definition len_ptuple_pact_rel (key : u64) (len : nat) (act : action) :=
  match act with
  | ActCommit tid mods => (key ∈ dom mods) -> (S tid < len)%nat
  | ActRead tid key' => (key = key') -> (tid < len)%nat
  | _ => True
  end.

Definition ptuple_past_rel (key : u64) (phys : list dbval) (past : list action) :=
  Forall (len_ptuple_pact_rel key (length phys)) past.

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
    "%Htsge"  ∷ ⌜(length logi ≤ S (S ts))%nat⌝.

Definition fc_tids_unique (fci fcc cmt : gset (nat * dbmap)) :=
  NoDup ((elements fci).*1 ++ (elements fcc).*1 ++ (elements cmt).*1).

Definition cmt_inv_def
           (γ : mvcc_names) (tmods : gset (nat * dbmap)) (future : list action) (ts : nat)
  : iProp Σ :=
  "HcmtAuth" ∷ cmt_tmods_auth γ tmods ∗
  "%Hcmt"    ∷ ⌜set_Forall (uncurry (first_commit_compatible future)) tmods⌝ ∗
  "%HcmtLe"  ∷ ⌜set_Forall (λ x, x.1 ≤ ts)%nat tmods⌝.

Definition nca_inv_def
           (γ : mvcc_names) (tids : gset nat) (future : list action) (ts : nat)
  : iProp Σ :=
  "HncaAuth" ∷ nca_tids_auth γ tids ∗
  "%Hnca"    ∷ ⌜set_Forall (no_commit_abort future) tids⌝ ∗
  "%HncaLe"  ∷ ⌜set_Forall (λ x, x ≤ ts)%nat tids⌝.

Definition fa_inv_def
           (γ : mvcc_names) (tids : gset nat) (future : list action) (ts : nat)
  : iProp Σ :=
  "HfaAuth" ∷ fa_tids_auth γ tids ∗
  "%Hfa"    ∷ ⌜set_Forall (first_abort future) tids⌝ ∗
  "%HfaLe"  ∷ ⌜set_Forall (λ x, x ≤ ts)%nat tids⌝.

Definition fci_inv_def
           (γ : mvcc_names) (tmods : gset (nat * dbmap)) (past future : list action) (ts : nat)
  : iProp Σ :=
  "HfciAuth" ∷ fci_tmods_auth γ tmods ∗
  "%Hfci"    ∷ ⌜set_Forall (uncurry (first_commit_incompatible past future)) tmods⌝ ∗
  "%HfciLe"  ∷ ⌜set_Forall (λ x, x.1 ≤ ts)%nat tmods⌝.

Definition fcc_inv_def
           (γ : mvcc_names) (tmods : gset (nat * dbmap)) (future : list action) (ts : nat)
  : iProp Σ :=
  "HfccAuth" ∷ fcc_tmods_auth γ tmods ∗
  "%Hfcc"    ∷ ⌜set_Forall (uncurry (first_commit_compatible future)) tmods⌝ ∗
  "%HfccLe"  ∷ ⌜set_Forall (λ x, x.1 ≤ ts)%nat tmods⌝.

Definition mvcc_inv_sst_def γ p : iProp Σ :=
  ∃ (tids_nca tids_fa : gset nat)
    (tmods_fci tmods_fcc tmods : gset (nat * dbmap))
    (ts : nat) (m : dbmap) (past future : list action),
    (* Prophecy. *)
    "Hproph" ∷ mvcc_proph γ p future ∗
    (* Current timestamp. *)
    "Hts"    ∷ ts_auth γ ts ∗
    (* Global database map, i.e., auth element of the global ptsto. *)
    "Hm"     ∷ dbmap_auth γ m ∗
    (* Per-key invariants. *)
    "Hkeys"  ∷ ([∗ set] key ∈ keys_all, per_key_inv_def γ key tmods ts m past) ∗
    (* Ok txns. *)
    "Hcmt"   ∷ cmt_inv_def γ tmods future ts ∗
    (* Doomed txns. *)
    "Hnca"   ∷ nca_inv_def γ tids_nca future ts ∗
    "Hfa"    ∷ fa_inv_def  γ tids_fa future ts ∗
    "Hfci"   ∷ fci_inv_def γ tmods_fci past future ts ∗
    "Hfcc"   ∷ fcc_inv_def γ tmods_fcc future ts ∗
    (* TIDs are unique among FC sets. *)
    "%Hfcnd" ∷ ⌜fc_tids_unique tmods_fci tmods_fcc tmods⌝.

Instance mvcc_inv_sst_timeless γ p :
  Timeless (mvcc_inv_sst_def γ p).
Proof. unfold mvcc_inv_sst_def. apply _. Defined.

Definition mvcc_inv_sst γ p : iProp Σ :=
  inv mvccNSST (mvcc_inv_sst_def γ p).

End def.

#[global]
Hint Extern 1 (environments.envs_entails _ (mvcc_inv_sst_def _ _)) => unfold mvcc_inv_sst_def : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (per_key_inv_def _ _ _ _ _ _)) => unfold per_key_inv_def : core.

Section theorem.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem active_ge_min γ (tid : u64) (tidlb : nat) (sid : u64) :
  mvcc_inv_gc_def γ -∗
  active_tid γ tid sid -∗
  min_tid_lb γ tidlb -∗
  ⌜(tidlb ≤ uint.nat tid)%nat⌝.
Proof.
  iIntros "Hinv Hactive Hlb".
  iDestruct "Hactive" as "[[Htid %Hlookup] _]".
  apply sids_all_lookup in Hlookup.
  apply list_elem_of_lookup_2 in Hlookup.
  iDestruct (big_sepL_elem_of with "Hlb") as "Htidlb"; first done.
  iDestruct (big_sepL_elem_of with "Hinv") as "H"; first done.
  iNamed "H".
  (* Obtaining [tidmin ≤ tid]. *)
  iDestruct (site_active_tids_elem_of with "HactiveA Htid") as "%Helem".
  apply Hmin in Helem.
  (* Obtaining [tidlb ≤ tidmin]. *)
  iDestruct (site_min_tid_valid with "HminA Htidlb") as "%Hle".
  iPureIntro.
  lia.
Qed.

Lemma nca_inv_weaken_ts {γ tids l ts} ts' :
  (ts ≤ ts')%nat ->
  nca_inv_def γ tids l ts -∗
  nca_inv_def γ tids l ts'.
Proof.
  iIntros "%Hle Hnca".
  iNamed "Hnca".
  iFrame "HncaAuth %".
  iPureIntro.
  apply (set_Forall_impl _ _ _ HncaLe). lia.
Qed.

Lemma fa_inv_weaken_ts {γ tids l ts} ts' :
  (ts ≤ ts')%nat ->
  fa_inv_def γ tids l ts -∗
  fa_inv_def γ tids l ts'.
Proof.
  iIntros "%Hts Hfa".
  iNamed "Hfa".
  iFrame "HfaAuth %".
  iPureIntro.
  apply (set_Forall_impl _ _ _ HfaLe). lia.
Qed.

Lemma fci_inv_weaken_ts {γ tmods l1 l2 ts} ts' :
  (ts ≤ ts')%nat ->
  fci_inv_def γ tmods l1 l2 ts -∗
  fci_inv_def γ tmods l1 l2 ts'.
Proof.
  iIntros "%Hts Hfci".
  iNamed "Hfci".
  iFrame "HfciAuth %".
  iPureIntro.
  apply (set_Forall_impl _ _ _ HfciLe). lia.
Qed.

Lemma fcc_inv_weaken_ts {γ tmods l ts} ts' :
  (ts ≤ ts')%nat ->
  fcc_inv_def γ tmods l ts -∗
  fcc_inv_def γ tmods l ts'.
Proof.
  iIntros "%Hts Hfcc".
  iNamed "Hfcc".
  iFrame "HfccAuth %".
  iPureIntro.
  apply (set_Forall_impl _ _ _ HfccLe). lia.
Qed.

Lemma cmt_inv_weaken_ts {γ tmods l ts} ts' :
  (ts ≤ ts')%nat ->
  cmt_inv_def γ tmods l ts -∗
  cmt_inv_def γ tmods l ts'.
Proof.
  iIntros "%Hts Hcmt".
  iNamed "Hcmt".
  iFrame "HcmtAuth %".
  iPureIntro.
  apply (set_Forall_impl _ _ _ HcmtLe). lia.
Qed.

Lemma ptuple_past_rel_read_diff_key key keyr tid phys past :
  key ≠ keyr ->
  ptuple_past_rel key phys past ->
  ptuple_past_rel key phys (past ++ [ActRead tid keyr]).
Proof.
  intros Hneq Hrel.
  unfold ptuple_past_rel.
  rewrite Forall_app.
  split; first done.
  rewrite Forall_singleton.
  by simpl.
Qed.

Lemma ptuple_past_rel_read_lt_len key tid phys past :
  (tid < length phys)%nat ->
  ptuple_past_rel key phys past ->
  ptuple_past_rel key phys (past ++ [ActRead tid key]).
Proof.
  intros Hlt Hrel.
  unfold ptuple_past_rel.
  rewrite Forall_app.
  split; first done.
  rewrite Forall_singleton.
  by simpl.
Qed.

Lemma len_ptuple_pact_rel_weaken_len {key} len {len' act} :
  (len ≤ len')%nat ->
  len_ptuple_pact_rel key len act ->
  len_ptuple_pact_rel key len' act.
Proof.
  intros Hlen Hrel.
  unfold len_ptuple_pact_rel in *.
  destruct act as [tid mods | tid key' |]; last done.
  - (* Case [ActCommit]. *)
    intros Helem. apply Hrel in Helem. lia.
  - (* Case [ActRead]. *)
    intros Helem. apply Hrel in Helem. lia.
Qed.

Lemma ptuple_past_rel_extensible key phys phys' past :
  prefix phys phys' ->
  ptuple_past_rel key phys past ->
  ptuple_past_rel key phys' past.
Proof.
  intros Hprefix Hrel.
  unfold ptuple_past_rel in *.
  apply (Forall_impl _ _ _ Hrel).
  intros a Hlen.
  apply (len_ptuple_pact_rel_weaken_len (length phys)); last done.
  by apply prefix_length.
Qed.

Lemma ptuple_past_rel_commit_lt_len key tid mods phys past :
  (S tid < length phys)%nat ->
  ptuple_past_rel key phys past ->
  ptuple_past_rel key phys (past ++ [ActCommit tid mods]).
Proof.
  intros Hlt Hrel.
  unfold ptuple_past_rel.
  rewrite Forall_app.
  split; first done.
  rewrite Forall_singleton.
  by simpl.
Qed.

Lemma per_key_inv_weaken_ts {γ key tmods ts} ts' {m past} :
  (ts ≤ ts')%nat ->
  per_key_inv_def γ key tmods ts m past -∗
  per_key_inv_def γ key tmods ts' m past.
Proof.
  iIntros "%Hle Hkey".
  iNamed "Hkey".
  do 2 iExists _.
  iFrame "∗ %".
  iPureIntro. lia.
Qed.

Lemma per_key_inv_past_snoc_diff_key {γ key keyr tmods ts} tid {m past} :
  key ≠ keyr ->
  per_key_inv_def γ key tmods ts m past -∗
  per_key_inv_def γ key tmods ts m (past ++ [ActRead tid keyr]).
Proof.
  iIntros "%Hneq Hkey".
  iNamed "Hkey".
  do 2 iExists _.
  iFrame "∗ %".
  iPureIntro. apply ptuple_past_rel_read_diff_key; done.
Qed.

Lemma per_key_inv_ltuple_ptsto γ tmods ts ts' m past :
  (ts < ts')%nat ->
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts m past) ==∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts' m past ∗
                         (∀ v, ⌜m !! k = Some v⌝ -∗ ltuple_ptsto γ k v ts')).
Proof.
  iIntros "%Hts Hkeys".
  iApply big_sepS_bupd.
  iApply (big_sepS_mono with "Hkeys").
  iIntros (k) "%Helem Hkey".
  iNamed "Hkey".
  iMod (ltuple_update (extend (S ts') logi) with "Hltuple") as "Hltuple".
  { apply extend_prefix. }
  iModIntro.
  iDestruct (ltuple_witness with "Hltuple") as "#Hlb".
  iSplitL.
  { do 2 iExists _.
    apply tuple_mods_rel_last_logi in Htmrel as Hlogi.
    apply (tuplext_linearize_unchanged ts') in Htmrel.
    iFrame "∗%".
    iPureIntro.
    split.
    { rewrite -Hlmrel. apply extend_last. }
    { rewrite extend_length; [lia | done]. }
  }
  iIntros (v) "%Hlookup".
  iExists _.
  iFrame "Hlb".
  iPureIntro.
  rewrite Hlookup in Hlmrel.
  rewrite (extend_last_Some _ _ v); last auto.
  destruct (decide (length logi ≤ ts')%nat).
  - rewrite lookup_app_r; last lia.
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

Theorem per_key_inv_ltuple_ptstos γ tmods ts ts' m past :
  (ts < ts')%nat ->
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts m past) ==∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts' m past) ∗
  ([∗ map] k ↦ v ∈ m, ltuple_ptsto γ k v ts').
Proof.
  iIntros "%Hts Hkeys".
  iMod (per_key_inv_ltuple_ptsto with "Hkeys") as "Hkeys"; first apply Hts.
  rewrite big_sepS_sep.
  iDestruct "Hkeys" as "[Hkeys Hltuples]".
  iDestruct (big_sepS_big_sepM_ltuple_ptstos with "Hltuples") as "Hltuples".
  by iFrame.
Qed.

Lemma per_key_inv_dbmap_ptstos_update_1 {γ tmods ts} ts' {m : dbmap} {past} r mods :
  dom mods ⊆ dom r ->
  (ts < ts')%nat ->
  dbmap_auth γ m -∗
  dbmap_ptstos γ 1 r -∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts m past) ==∗
  dbmap_auth γ (mods ∪ m) ∗
  dbmap_ptstos γ 1 (mods ∪ r) ∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k ({[ (ts', mods) ]} ∪ tmods) ts' (mods ∪ m) past ∗
                         (∀ v, ⌜m !! k = Some v⌝ -∗ ltuple_ptsto γ k v ts')).
Proof.
  iIntros "%Hdom %Hts Hdb Hdbpts Hkeys".
  iDestruct (dbmap_lookup_big with "Hdb Hdbpts") as "%Hsubseteq".
  iMod (dbmap_update_big _ (mods ∪ r) with "Hdb Hdbpts") as "[Hdb Hdbpts]"; first set_solver.
  rewrite -map_union_assoc.
  rewrite (map_subseteq_union r m); last done.
  iFrame.
  iApply big_sepS_bupd.
  iApply (big_sepS_mono with "Hkeys").
  iIntros (key) "%Helem Hkey".
  iNamed "Hkey".
  iMod (ltuple_update (extend (S ts') logi) with "Hltuple") as "Hltuple".
  { apply extend_prefix. }
  iDestruct (ltuple_witness with "Hltuple") as "#Hlb".
  iSplitL; last first.
  { iModIntro.
    iIntros (v) "%Hlookup".
    iExists _.
    iFrame "Hlb".
    iPureIntro.
    rewrite Hlookup in Hlmrel.
    rewrite (extend_last_Some _ _ v); last auto.
    destruct (decide (length logi ≤ ts')%nat).
    - rewrite lookup_app_r; last lia.
      apply lookup_replicate_2. lia.
    - apply not_le in n.
      rewrite lookup_app_l; last lia.
      rewrite last_lookup in Hlmrel.
      rewrite -Hlmrel.
      f_equal. lia.
  }
  destruct (decide (key ∈ dom mods)); last first.
  { (* Case [key ∉ dom mods]. *)
    do 2 iExists _.
    apply tuple_mods_rel_last_logi in Htmrel as Hlogi.
    iFrame "∗ %".
    iPureIntro.
    rewrite not_elem_of_dom in n.
    split.
    { (* Prove [tuple_mods_rel]. *)
    rewrite per_tuple_mods_union_None; last done.
      by apply tuplext_linearize_unchanged.
    }
    split.
  { (* Prove last in logical tuple is latest value. *)
      rewrite lookup_union_r; last done.
      by rewrite extend_last.
    }
    { (* Prove an upper bound of the length of logical tuple. *)
      rewrite extend_length; [lia | done].
    }
  }
  (* Case [key ∈ dom mods]. *)
  rewrite elem_of_dom in e. destruct e as [v Hlookup].
  iMod (ltuple_update (extend (S ts') logi ++ [v]) with "Hltuple") as "Hltuple".
  { by apply prefix_app_r. }
  iModIntro.
  do 2 iExists _.
  iFrame "∗ %".
  iPureIntro.
  split.
  { (* Prove [tuple_mods_rel]. *)
    rewrite (per_tuple_mods_union_Some v); last done.
    apply tuplext_linearize_changed; [lia | done].
  }
  split.
  { (* Prove last in logical tuple is latest value. *)
    rewrite lookup_union_l'; last done.
    by rewrite last_snoc.
  }
  { (* Prove an upper bound of the length of logical tuple. *)
    rewrite length_app. simpl.
    rewrite extend_length; first lia.
    by eapply tuple_mods_rel_last_logi.
  }
Qed.

Theorem per_key_inv_dbmap_ptstos_update {γ tmods ts} ts' {m : dbmap} {past} r mods :
  dom mods ⊆ dom r ->
  (ts < ts')%nat ->
  dbmap_auth γ m -∗
  dbmap_ptstos γ 1 r -∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts m past) ==∗
  dbmap_auth γ (mods ∪ m) ∗
  dbmap_ptstos γ 1 (mods ∪ r) ∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k ({[ (ts', mods) ]} ∪ tmods) ts' (mods ∪ m) past) ∗
  ([∗ map] k ↦ v ∈ r, ltuple_ptsto γ k v ts').
Proof.
  iIntros "%Hdom %Hts Hdb Hdbpts Hkeys".
  iDestruct (dbmap_lookup_big with "Hdb Hdbpts") as "%Hrm".
  iMod (per_key_inv_dbmap_ptstos_update_1 with "Hdb Hdbpts Hkeys")
    as "(Hdb & Hdbpts & Hkeys)"; [done | done |].
  iModIntro.
  rewrite big_sepS_sep.
  iDestruct "Hkeys" as "[Hkeys Hltuples]".
  iFrame.
  iApply big_sepS_big_sepM_ltuple_ptstos.
  iApply (big_sepS_mono with "Hltuples").
  iIntros (k Helem) "Hltuple".
  iIntros (v Hlookup).
  iApply "Hltuple".
  iPureIntro.
  apply (lookup_weaken r); done.
Qed.

(* Theorems to re-establish invariants after prophecy resolution. *)
Definition diff_abort_action (a : action) (tids : gset nat) :=
  match a with
  | ActAbort tid => tid ∉ tids
  | _ => True
  end.

Definition diff_commit_action (a : action) (tmods : gset (nat * dbmap)) :=
  match a with
  | ActCommit tid _ => ∀ mods, (tid, mods) ∉ tmods
  | _ => True
  end.

Lemma nca_inv_any_action γ l l' a tids ts :
  l = a :: l' ->
  nca_inv_def γ tids l ts -∗
  nca_inv_def γ tids l' ts.
Proof.
  iIntros "%Hhead Hnca".
  iNamed "Hnca".
  iFrame "∗ %".
  iPureIntro.
  apply (set_Forall_impl _ _ _ Hnca).
  intros tid H.
  rewrite -hd_error_tl_repr in Hhead.
  destruct Hhead as [_ Htl].
  apply (no_commit_abort_preserved l); auto.
Qed.

Lemma fa_inv_diff_action γ l l' a tids ts :
  l = a :: l' ->
  diff_abort_action a tids ->
  fa_inv_def γ tids l ts -∗
  fa_inv_def γ tids l' ts.
Proof.
  iIntros "%Hl %Ha Hfa".
  iNamed "Hfa".
  iFrame "∗ %".
  iPureIntro.
  intros tid Helem.
  apply Hfa in Helem as H.
  apply (first_abort_preserved Hl); [intros contra; set_solver | auto].
Qed.

Lemma fa_inv_same_action γ l l' tid tids ts :
  l = ActAbort tid :: l' ->
  fa_tids_frag γ tid -∗
  fa_inv_def γ tids l ts ==∗
  fa_inv_def γ (tids ∖ {[ tid ]}) l' ts.
Proof using heapGS0 mvcc_ghostG0 Σ.
  (* FIXME *)
  iIntros "%Hl Hfrag Hfa".
  iNamed "Hfa".
  iDestruct (fa_tids_lookup with "HfaAuth Hfrag") as "%Helem".
  iMod (fa_tids_delete with "HfaAuth Hfrag") as "HfaAuth".
  iModIntro.
  iFrame.
  iPureIntro.
  split.
  - set tids' := tids ∖ _.
    apply (set_Forall_subseteq _ tids') in Hfa; last set_solver.
    intros t Helem'.
    apply Hfa in Helem' as H.
    apply (first_abort_preserved Hl); [set_solver | auto].
  - apply set_Forall_subseteq with tids; [set_solver | auto].
Qed.

Lemma fci_inv_diff_action γ p l l' a tmods ts :
  l = a :: l' ->
  diff_commit_action a tmods ->
  fci_inv_def γ tmods p l ts -∗
  fci_inv_def γ tmods (p ++ [a]) l' ts.
Proof.
  iIntros "%Hl %Ha Hfcc".
  iNamed "Hfcc".
  iFrame "∗ %".
  iPureIntro.
  intros tmod Helem.
  destruct tmod as [t m].
  apply Hfci in Helem as H.
  simpl in *.
  apply (first_commit_incompatible_preserved Hl); [set_solver | auto].
Qed.

Lemma fcc_inv_diff_action γ l l' a tmods ts :
  l = a :: l' ->
  diff_commit_action a tmods ->
  fcc_inv_def γ tmods l ts -∗
  fcc_inv_def γ tmods l' ts.
Proof.
  iIntros "%Hl %Ha Hfcc".
  iNamed "Hfcc".
  iFrame "∗ %".
  iPureIntro.
  intros tmod Helem.
  destruct tmod as [t m].
  apply Hfcc in Helem as H.
  simpl in *.
  apply (first_commit_compatible_preserved Hl); [set_solver | auto].
Qed.

Lemma cmt_inv_diff_action γ l l' a tmods ts :
  l = a :: l' ->
  diff_commit_action a tmods ->
  cmt_inv_def γ tmods l ts -∗
  cmt_inv_def γ tmods l' ts.
Proof.
  iIntros "%Hl %Ha Hcmt".
  iNamed "Hcmt".
  iFrame "∗ %".
  iPureIntro.
  intros tmod Helem.
  destruct tmod as [t m].
  apply Hcmt in Helem as H.
  simpl in *.
  apply (first_commit_compatible_preserved Hl); [set_solver | auto].
Qed.

Lemma cmt_inv_same_action γ l l' tid mods tmods ts :
  l = ActCommit tid mods :: l' ->
  NoDup (elements tmods).*1 ->
  cmt_tmods_frag γ (tid, mods) -∗
  cmt_inv_def γ tmods l ts ==∗
  cmt_inv_def γ (tmods ∖ {[ (tid, mods) ]}) l' ts.
Proof using heapGS0 mvcc_ghostG0 Σ.
  (* FIXME *)
  iIntros "%Hl %HND Hfrag Hcmt".
  iNamed "Hcmt".
  iDestruct (cmt_tmods_lookup with "HcmtAuth Hfrag") as "%Helem".
  iMod (cmt_tmods_delete with "HcmtAuth Hfrag") as "HcmtAuth".
  iModIntro.
  iFrame.
  iPureIntro.
  split.
  - set tmods' := tmods ∖ _.
    apply (set_Forall_subseteq _ tmods') in Hcmt; last set_solver.
    pose proof (tmods_NoDup_notin_difference HND Helem) as Hnotin.
    intros [t m] Helem'.
    apply Hcmt in Helem' as H.
    simpl in *.
    apply (first_commit_compatible_preserved Hl); [set_solver | auto].
  - apply set_Forall_subseteq with tmods; [set_solver | auto].
Qed.

Lemma cmt_inv_fcc_tmods γ l tmods ts :
  cmt_inv_def γ tmods l ts -∗
  ⌜set_Forall (uncurry (first_commit_compatible l)) tmods⌝.
Proof. iIntros "Hcmt". by iNamed "Hcmt". Qed.

Lemma ptuple_past_rel_abort key phys past tid :
  ptuple_past_rel key phys past ->
  ptuple_past_rel key phys (past ++ [ActAbort tid]).
Proof.
  unfold ptuple_past_rel.
  intros H.
  rewrite Forall_app.
  split; first done.
  by rewrite Forall_singleton.
Qed.

Lemma per_key_inv_past_abort {γ tmods ts m past} tid :
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts m past) -∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts m (past ++ [ActAbort tid])).
Proof.
  iIntros "Hkeys".
  iApply big_sepS_mono; last eauto.
  iIntros (key) "%Helem Hkey".
  iNamed "Hkey".
  apply (ptuple_past_rel_abort _ _ _ tid) in Hpprel.
  eauto with iFrame.
Qed.

Lemma per_key_inv_tmods_minus_disj γ k tmods ts m past tid mods :
  k ∉ dom mods ->
  per_key_inv_def γ k tmods ts m past -∗
  per_key_inv_def γ k (tmods ∖ {[ (tid, mods) ]}) ts m past.
Proof.
  iIntros "%Hnotin Hkey".
  iNamed "Hkey".
  do 2 iExists _.
  iFrame "∗ %".
  iPureIntro.
  rewrite not_elem_of_dom in Hnotin.
  by rewrite per_tuple_mods_minus_None.
Qed.

Lemma per_key_inv_past_commit_disj γ k tmods ts m past tid mods :
  k ∉ dom mods ->
  per_key_inv_def γ k tmods ts m past -∗
  per_key_inv_def γ k tmods ts m (past ++ [ActCommit tid mods]).
Proof.
  iIntros "%Hnotin Hkey".
  iNamed "Hkey".
  do 2 iExists _.
  iFrame "∗ %".
  iPureIntro.
  apply Forall_app.
  split; first done.
  rewrite Forall_singleton.
  by simpl.
Qed.

Lemma fc_tids_unique_cmt fci fcc cmt :
  fc_tids_unique fci fcc cmt ->
  NoDup (elements cmt).*1.
Proof.
  unfold fc_tids_unique.
  intros HNoDup.
  rewrite NoDup_app_assoc NoDup_app_comm in HNoDup.
  by apply NoDup_app in HNoDup as [H _].
Qed.

Lemma fc_tids_unique_notin_fci fci fcc cmt tid mods :
  (tid, mods) ∈ cmt ->
  fc_tids_unique fci fcc cmt ->
  ∀ m, (tid, m) ∉ fci.
Proof.
  unfold fc_tids_unique.
  intros Helem HNoDup.
  rewrite NoDup_app_assoc NoDup_app_comm in HNoDup.
  apply NoDup_app in HNoDup as (_ & HNoDup & _).
  rewrite -elem_of_elements in Helem.
  apply (list_elem_of_fmap_2 fst) in Helem. simpl in Helem.
  apply HNoDup in Helem.
  intros m Helem'.
  rewrite -elem_of_elements in Helem'.
  apply (list_elem_of_fmap_2 fst) in Helem'. simpl in Helem'.
  set_solver.
Qed.

Lemma fc_tids_unique_notin_fcc fci fcc cmt tid mods :
  (tid, mods) ∈ cmt ->
  fc_tids_unique fci fcc cmt ->
  ∀ m, (tid, m) ∉ fcc.
Proof.
  unfold fc_tids_unique.
  intros Helem HNoDup.
  rewrite NoDup_app_assoc NoDup_app_comm in HNoDup.
  apply NoDup_app in HNoDup as (_ & HNoDup & _).
  rewrite -elem_of_elements in Helem.
  apply (list_elem_of_fmap_2 fst) in Helem. simpl in Helem.
  apply HNoDup in Helem.
  intros m Helem'.
  rewrite -elem_of_elements in Helem'.
  apply (list_elem_of_fmap_2 fst) in Helem'. simpl in Helem'.
  set_solver.
Qed.

Lemma fc_tids_unique_minus_cmt {fci fcc cmt} tid mods :
  fc_tids_unique fci fcc cmt ->
  fc_tids_unique fci fcc (cmt ∖ {[ (tid, mods) ]}).
Proof.
  intros H.
  apply NoDup_app in H as (Hfci & Hict & Hct).
  apply NoDup_app in Hct as (Hfcc & Hct & Hcmt).
  apply NoDup_app.
  split; first done.
  split.
  { intros x Helem.
    rewrite not_elem_of_app.
    apply Hict in Helem.
    split; set_solver.
  }
  apply NoDup_app.
  split; first done.
  split.
  { intros x Helem.
    apply Hct in Helem.
    set_solver.
  }
  destruct (decide ((tid, mods) ∈ cmt)); last first.
  { rewrite difference_disjoint_L; [done | set_solver]. }
  rewrite (union_difference_L {[ (tid, mods) ]} cmt) in Hcmt; last set_solver.
  rewrite NoDup_Permutation_proper in Hcmt; last first.
  {  set cmt' := _ ∖ _.
     rewrite elements_union_singleton; last set_solver.
     rewrite fmap_cons. simpl. reflexivity.
  }
  by apply NoDup_cons in Hcmt as [_ H].
Qed.

(* Really ugly proof... Maybe should have defined TID uniqueness differently? *)
#[local]
Lemma fc_tids_unique_insert {A B C} ts ts' mods :
  (ts < ts')%nat ->
  set_Forall (λ x, x.1 ≤ ts)%nat (A ∪ B ∪ C) ->
  fc_tids_unique A B C ->
  fc_tids_unique ({[ (ts', mods) ]} ∪ A) B C.
Proof.
  intros Hts.
  unfold fc_tids_unique.
  intros Hltall H.
  apply (set_Forall_subseteq _ A) in Hltall as HltA; last set_solver.
  apply (set_Forall_subseteq _ B) in Hltall as HltB; last set_solver.
  apply (set_Forall_subseteq _ C) in Hltall as HltC; last set_solver.
  rewrite NoDup_Permutation_proper; last first.
  { apply Permutation_app; last reflexivity.
    rewrite elements_union_singleton; last first.
    { intros Helem.
      apply HltA in Helem. simpl in Helem. lia.
    }
    rewrite fmap_cons. simpl. reflexivity.
  }
  replace (λ x, _) with ((λ tidx, (tidx ≤ ts)%nat) ∘ (fst : nat * dbmap -> nat)) in *; last done.
  apply set_Forall_elements, Forall_fmap in HltA, HltB, HltC.
  rewrite Forall_forall in HltA.
  rewrite Forall_forall in HltB.
  rewrite Forall_forall in HltC.
  apply NoDup_app in H as (HA & HABC & HBC).
  apply NoDup_app in HBC as (HB & HBC & HC).
  apply NoDup_app.
  split.
  { rewrite NoDup_cons.
    split; last done.
    intros contra.
    apply HltA in contra. lia.
  }
  split.
  { intros x Helem.
    rewrite elem_of_cons in Helem.
    destruct Helem; last by auto.
    rewrite not_elem_of_app.
    split.
    { intros contra. apply HltB in contra. lia. }
    { intros contra. apply HltC in contra. lia. }
  }
  apply NoDup_app.
  split; first done.
  split; done.
Qed.

Lemma fc_tids_unique_insert_fci {fci fcc cmt} ts ts' mods :
  (ts < ts')%nat ->
  set_Forall (λ x, x.1 ≤ ts)%nat (fci ∪ fcc ∪ cmt) ->
  fc_tids_unique fci fcc cmt ->
  fc_tids_unique ({[ (ts', mods) ]} ∪ fci) fcc cmt.
Proof.
  intros Hltall.
  by apply fc_tids_unique_insert.
Qed.

Lemma fc_tids_unique_insert_fcc {fci fcc cmt} ts ts' mods :
  (ts < ts')%nat ->
  set_Forall (λ x, x.1 ≤ ts)%nat (fci ∪ fcc ∪ cmt) ->
  fc_tids_unique fci fcc cmt ->
  fc_tids_unique fci ({[ (ts', mods) ]} ∪ fcc) cmt.
Proof.
  intros Hts Hltall.
  unfold fc_tids_unique.
  do 2 rewrite (NoDup_app_comm (elements fci).*1).
  do 2 rewrite -NoDup_app_assoc.
  replace (_ ∪ _ ∪ _) with (fcc ∪ cmt ∪ fci) in Hltall; last by set_solver.
  by eapply fc_tids_unique_insert.
Qed.

Lemma fc_tids_unique_insert_cmt {fci fcc cmt} ts ts' mods :
  (ts < ts')%nat ->
  set_Forall (λ x, x.1 ≤ ts)%nat (fci ∪ fcc ∪ cmt) ->
  fc_tids_unique fci fcc cmt ->
  fc_tids_unique fci fcc ({[ (ts', mods) ]} ∪ cmt).
Proof.
  intros Hts Hltall.
  unfold fc_tids_unique.
  do 2 rewrite NoDup_app_assoc.
  do 2 rewrite (NoDup_app_comm ((elements fci).*1 ++ _)).
  replace (_ ∪ _ ∪ _) with (cmt ∪ fci ∪ fcc) in Hltall; last by set_solver.
  by eapply fc_tids_unique_insert.
Qed.

Lemma fc_inv_fc_tids_lt_ts
      (γ : mvcc_names) (fci fcc cmt : gset (nat * dbmap))
      (past future : list action) (ts : nat) :
  fci_inv_def γ fci past future ts -∗
  fcc_inv_def γ fcc future ts -∗
  cmt_inv_def γ cmt future ts -∗
  ⌜set_Forall (λ x, x.1 ≤ ts)%nat (fci ∪ fcc ∪ cmt)⌝.
Proof.
  iIntros "Hfci Hfcc Hcmt".
  iNamed "Hfci".
  iNamed "Hfcc".
  iNamed "Hcmt".
  iPureIntro.
  apply set_Forall_union; last done.
  apply set_Forall_union; done.
Qed.

(**
 * The following lemma says that from FCC we know txns must write the same key in
 * TID order.
 *)
Lemma fcc_head_commit_le_all tid mods tmods future :
  set_Forall (uncurry (first_commit_compatible future)) tmods ->
  head_commit future tid mods ->
  set_Forall (λ key, le_tids_mods tid (per_tuple_mods tmods key)) (dom mods).
Proof.
  intros Hfcc Hhead key Hinmods.
  unfold le_tids_mods.
  intros tm Helem.
  destruct tm as [t m]. simpl.
  apply mods_tuple_to_global in Helem.
  destruct Helem as (mods' & Hinmods' & Hlookup).
  apply Hfcc in Hinmods'. simpl in Hinmods'.
  apply elem_of_dom_2 in Hlookup.
  eapply safe_extension_wr; [by eauto | by eauto | set_solver].
Qed.

Lemma fcc_head_read_le_all tid key tmods future :
  set_Forall (uncurry (first_commit_compatible future)) tmods ->
  head_read future tid key ->
  le_tids_mods tid (per_tuple_mods tmods key).
Proof.
  intros Hfcc Hhead.
  unfold le_tids_mods.
  intros tm Helem.
  destruct tm as [t m]. simpl.
  apply mods_tuple_to_global in Helem.
  destruct Helem as (mods & Hinmods & Hlookup).
  apply Hfcc in Hinmods. simpl in Hinmods.
  apply elem_of_dom_2 in Hlookup.
  eapply safe_extension_rd; [by eauto | by eauto | set_solver].
Qed.

Lemma mvcc_inv_sst_ts_auth_acc γ p :
  mvcc_inv_sst_def γ p -∗
  ∃ ts, ts_auth γ ts ∗ (∀ ts', ⌜(ts ≤ ts')%nat⌝ -∗ ts_auth γ ts' -∗ mvcc_inv_sst_def γ p).
Proof.
  iIntros "Hinv".
  iNamed "Hinv".
  iExists _. iFrame "Hts".
  iIntros (ts' Hle) "Hts".
  iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
  { iIntros (k) "%Helem Hkeys".
    iApply (per_key_inv_weaken_ts ts' with "Hkeys"). lia.
  }
  iDestruct (nca_inv_weaken_ts ts' with "Hnca") as "Hnca"; first lia.
  iDestruct (fa_inv_weaken_ts ts' with "Hfa") as "Hfa"; first lia.
  iDestruct (fci_inv_weaken_ts ts' with "Hfci") as "Hfci"; first lia.
  iDestruct (fcc_inv_weaken_ts ts' with "Hfcc") as "Hfcc"; first lia.
  iDestruct (cmt_inv_weaken_ts ts' with "Hcmt") as "Hcmt"; first lia.
  eauto 15 with iFrame.
Qed.

End theorem.
