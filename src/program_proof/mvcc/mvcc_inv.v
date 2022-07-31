From Perennial.program_proof Require Export grove_prelude.
From Perennial.program_proof.mvcc Require Import mvcc_ghost mvcc_misc proph_proof.

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
           (γ : mvcc_names) (tmods : gset (nat * dbmap)) (future : list action) (ts : nat)
  : iProp Σ :=
  "HcmtAuth" ∷ cmt_tmods_auth γ tmods ∗
  "%Hcmt"    ∷ ⌜set_Forall (uncurry (first_commit_compatible future)) tmods⌝ ∗
  "%HcmtLt"  ∷ ⌜set_Forall (λ x, x.1 < ts)%nat tmods⌝.

Definition nca_inv_def
           (γ : mvcc_names) (tids : gset nat) (future : list action) (ts : nat)
  : iProp Σ :=
  "HncaAuth" ∷ nca_tids_auth γ tids ∗
  "%Hnca"    ∷ ⌜set_Forall (no_commit_abort future) tids⌝ ∗
  "%HncaLt"  ∷ ⌜set_Forall (λ x, x < ts)%nat tids⌝.

Definition fa_inv_def
           (γ : mvcc_names) (tids : gset nat) (future : list action) (ts : nat)
  : iProp Σ :=
  "HfaAuth" ∷ fa_tids_auth γ tids ∗
  "%Hfa"    ∷ ⌜set_Forall (first_abort future) tids⌝ ∗
  "%HfaLt"  ∷ ⌜set_Forall (λ x, x < ts)%nat tids⌝.

Definition fci_inv_def
           (γ : mvcc_names) (tmods : gset (nat * dbmap)) (past future : list action) (ts : nat)
  : iProp Σ :=
  "HfciAuth" ∷ fci_tmods_auth γ tmods ∗
  "%Hfci"    ∷ ⌜set_Forall (uncurry (first_commit_incompatible past future)) tmods⌝ ∗
  "%HfciLt"  ∷ ⌜set_Forall (λ x, x.1 < ts)%nat tmods⌝.

Definition fcc_inv_def
           (γ : mvcc_names) (tmods : gset (nat * dbmap)) (future : list action) (ts : nat)
  : iProp Σ :=
  "HfccAuth" ∷ fcc_tmods_auth γ tmods ∗
  "%Hfcc"    ∷ ⌜set_Forall (uncurry (first_commit_compatible future)) tmods⌝ ∗
  "%HfccLt"  ∷ ⌜set_Forall (λ x, x.1 < ts)%nat tmods⌝.

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
    "Hcmt"  ∷ cmt_inv_def γ tmods future ts ∗
    (* Doomed txns. *)
    "Hnca"  ∷ nca_inv_def γ tids_nca future ts ∗
    "Hfa"   ∷ fa_inv_def  γ tids_fa future ts ∗
    "Hfci"  ∷ fci_inv_def γ tmods_fci past future ts ∗
    "Hfcc"  ∷ fcc_inv_def γ tmods_fcc future ts.

Instance mvcc_inv_sst_timeless γ p :
  Timeless (mvcc_inv_sst_def γ p).
Proof. unfold mvcc_inv_sst_def. apply _. Defined.

Definition mvcc_inv_sst γ p : iProp Σ :=
  inv mvccNSST (mvcc_inv_sst_def γ p).

End def.

Hint Extern 1 (environments.envs_entails _ (mvcc_inv_sst_def _ _)) => unfold mvcc_inv_sst_def : core.
Hint Extern 1 (environments.envs_entails _ (per_key_inv_def _ _ _ _ _ _)) => unfold per_key_inv_def : core.

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

Lemma nca_inv_weaken_ts {γ tids l ts} ts' :
  (ts ≤ ts')%nat ->
  nca_inv_def γ tids l ts -∗
  nca_inv_def γ tids l ts'.
Proof.
  iIntros "%Hle Hnca".
  iNamed "Hnca".
  iFrame "HncaAuth %".
  iPureIntro.
  apply (set_Forall_impl _ _ _ HncaLt). lia.
Qed.

Lemma fa_inv_weaken_ts {γ tids l ts} ts' :
  (ts ≤ ts')%nat ->
  fa_inv_def γ tids l ts -∗
  fa_inv_def γ tids l ts'.
Admitted.

Lemma fci_inv_weaken_ts {γ tmods l1 l2 ts} ts' :
  (ts ≤ ts')%nat ->
  fci_inv_def γ tmods l1 l2 ts -∗
  fci_inv_def γ tmods l1 l2 ts'.
Admitted.

Lemma fcc_inv_weaken_ts {γ tmods l ts} ts' :
  (ts ≤ ts')%nat ->
  fcc_inv_def γ tmods l ts -∗
  fcc_inv_def γ tmods l ts'.
Admitted.

Lemma cmt_inv_weaken_ts {γ tmods l ts} ts' :
  (ts ≤ ts')%nat ->
  cmt_inv_def γ tmods l ts -∗
  cmt_inv_def γ tmods l ts'.
Admitted.

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

Theorem per_key_inv_dbmap_ptstos_update {γ tmods tid m past} r mods :
  dbmap_ptstos γ r -∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods tid m past) ==∗
  dbmap_ptstos γ (mods ∪ r) ∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k ({[ (tid, mods) ]} ∪ tmods) tid m past).
Admitted.

Theorem ltuple_ptuple_ptsto_eq γ k v1 v2 ts:
  tuple_auth_prefix γ k -∗
  ltuple_ptsto γ k v1 ts -∗
  ptuple_ptsto γ k v2 ts -∗
  ⌜v1 = v2⌝.
Admitted.

(* Theorems to re-establish invariants after prophecy resolution. *)
Definition diff_abort_action (a : action) (tids : gset nat) :=
  match a with
  | EvAbort tid => tid ∉ tids
  | _ => True
  end.

Definition diff_commit_action (a : action) (tmods : gset (nat * dbmap)) :=
  match a with
  | EvCommit tid _ => ∀ mods, (tid, mods) ∉ tmods
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
  l = EvAbort tid :: l' ->
  fa_tids_frag γ tid -∗
  fa_inv_def γ tids l ts ==∗
  fa_inv_def γ (tids ∖ {[ tid ]}) l' ts.
Proof using heapGS0 mvcc_ghostG0 Σ.
  (* FIXME *)
  iIntros "%Hl Hfrag Hfa".
  iNamed "Hfa".
  iDestruct (fa_tids_lookup with "Hfrag HfaAuth") as "%Helem".
  iMod (fa_tids_delete with "Hfrag HfaAuth") as "HfaAuth".
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

Local Lemma NoDup_notin_difference {tmods : gset (nat * dbmap)} {tid mods} :
  NoDup (elements tmods).*1 ->
  (tid, mods) ∈ tmods ->
  ∀ m, (tid, m) ∉ tmods ∖ {[ (tid, mods) ]}.
Proof.
  intros HND Helem m Helem'.
  apply union_difference_singleton_L in Helem.
  set tmods' := tmods ∖ {[ (tid, mods) ]} in Helem Helem'.
  rewrite Helem in HND.
  rewrite fmap_Permutation in HND; last first.
  { apply elements_union_singleton. set_solver. }
  simpl in HND.
  apply NoDup_cons_1_1 in HND.
  set_solver.
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
  NoDup (elements tmods).*1 ->
  l = EvCommit tid mods :: l' ->
  cmt_tmods_frag γ (tid, mods) -∗
  cmt_inv_def γ tmods l ts ==∗
  cmt_inv_def γ (tmods ∖ {[ (tid, mods) ]}) l' ts.
Proof using heapGS0 mvcc_ghostG0 Σ.
  (* FIXME *)
  iIntros "%HND %Hl Hfrag Hcmt".
  iNamed "Hcmt".
  iDestruct (cmt_tmods_lookup with "Hfrag HcmtAuth") as "%Helem".
  iMod (cmt_tmods_delete with "Hfrag HcmtAuth") as "HcmtAuth".
  iModIntro.
  iFrame.
  iPureIntro.
  split.
  - set tmods' := tmods ∖ _.
    apply (set_Forall_subseteq _ tmods') in Hcmt; last set_solver.
    pose proof (NoDup_notin_difference HND Helem) as Hnotin.
    intros [t m] Helem'.
    apply Hcmt in Helem' as H.
    simpl in *.
    apply (first_commit_compatible_preserved Hl); [set_solver | auto].
  - apply set_Forall_subseteq with tmods; [set_solver | auto].
Qed.

Lemma ptuple_past_rel_abort key phys past tid :
  ptuple_past_rel key phys past ->
  ptuple_past_rel key phys (past ++ [EvAbort tid]).
Admitted.

Lemma per_key_inv_past_abort {γ tmods ts m past} tid :
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts m past) -∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods ts m (past ++ [EvAbort tid])).
Proof.
  iIntros "Hkeys".
  iApply big_sepS_mono; last eauto.
  iIntros (key) "%Helem Hkey".
  iNamed "Hkey".
  apply (ptuple_past_rel_abort _ _ _ tid) in Hpprel.
  eauto with iFrame.
Qed.

End theorem.
