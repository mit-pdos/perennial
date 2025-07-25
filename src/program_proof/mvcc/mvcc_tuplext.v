From Perennial.program_proof.mvcc Require Import mvcc_prelude mvcc_misc.

(**
 * Convert global modifications to per-tuple modification.
 *)
Fixpoint per_tuple_mods_list (l : list (nat * dbmap)) (key : u64) : gset (nat * dbval) :=
  match l with
  | [] => ∅
  | hd :: tl => match hd.2 !! key with
              | None => per_tuple_mods_list tl key
              | Some v => {[ (hd.1, v) ]} ∪ (per_tuple_mods_list tl key)
              end
  end.

Definition per_tuple_mods (s : gset (nat * dbmap)) (key : u64) : gset (nat * dbval) :=
  per_tuple_mods_list (elements s) key.

(* TODO: Rename lemma names from [mods] to [tmods], [tuple] to [key]. *)

Lemma mods_tuple_to_global_list l key tid v :
  (tid, v) ∈ per_tuple_mods_list l key ->
  ∃ mods, (tid, mods) ∈ l ∧ mods !! key = Some v.
Proof.
  intros H.
  induction l as [| x l IHl]; first set_solver.
  simpl in H.
  destruct (x.2 !! key) eqn:E.
  - rewrite elem_of_union in H.
    destruct H; last set_solver.
    rewrite elem_of_singleton in H.
    inversion H.
    subst tid d.
    exists x.2.
    rewrite -(surjective_pairing x).
    set_solver.
  - destruct (IHl H) as [mods [Hin Hlookup]].
    set_solver.
Qed.

Lemma mods_tuple_to_global s key tid v :
  (tid, v) ∈ per_tuple_mods s key ->
  ∃ mods, (tid, mods) ∈ s ∧ mods !! key = Some v.
Proof.
  intros H.
  apply mods_tuple_to_global_list in H.
  set_solver.
Qed.

Lemma mods_global_to_tuple_list l key tid mods v :
  (tid, mods) ∈ l ∧ mods !! key = Some v ->
  (tid, v) ∈ per_tuple_mods_list l key.
Proof.
  intros [Helem Hlookup].
  induction l as [| x l IHl]; first set_solver.
  rewrite elem_of_cons in Helem.
  destruct Helem.
  - subst x. simpl.
    rewrite Hlookup.
    set_solver.
  - specialize (IHl H). simpl.
    destruct (x.2 !! key); set_solver.
Qed.

Lemma mods_global_to_tuple {s key tid} mods {v} :
  (tid, mods) ∈ s ∧ mods !! key = Some v ->
  (tid, v) ∈ per_tuple_mods s key. 
Proof.
  intros [Helem Hlookup].
  rewrite -elem_of_elements in Helem.
  by apply mods_global_to_tuple_list with mods.
Qed.

Lemma tmods_NoDup_notin_difference {tmods : gset (nat * dbmap)} {tid mods} :
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

Lemma per_tuple_mods_union_None
      {tmods : gset (nat * dbmap)} {tid : nat} {mods : dbmap} {k : u64} :
  mods !! k = None ->
  per_tuple_mods ({[ (tid, mods) ]} ∪ tmods) k = per_tuple_mods tmods k.
Proof.
  intros Hlookup.
  rewrite set_eq.
  intros [t v].
  split.
  - intros Helem.
    apply mods_tuple_to_global in Helem.
    destruct Helem as (mods' & Helem & Hlookup').
    rewrite elem_of_union in Helem.
    destruct Helem; first set_solver.
    by apply mods_global_to_tuple with mods'.
  - intros Helem.
    apply mods_tuple_to_global in Helem.
    destruct Helem as (mods' & Helem & Hlookup').
    apply mods_global_to_tuple with mods'.
    split; [set_solver | done].
Qed.

Lemma per_tuple_mods_union_Some
      {tmods : gset (nat * dbmap)} {tid : nat} {mods : dbmap} {k : u64} (v : dbval) :
  mods !! k = Some v ->
  per_tuple_mods ({[ (tid, mods) ]} ∪ tmods) k = {[ (tid, v) ]} ∪ (per_tuple_mods tmods k).
Proof.
  intros Hlookup.
  rewrite set_eq.
  intros [t u].
  split.
  - intros Helem.
    apply mods_tuple_to_global in Helem.
    destruct Helem as (mods' & Helem & Hlookup').
    rewrite elem_of_union in Helem.
    destruct Helem; first set_solver.
    rewrite elem_of_union. right.
    by apply mods_global_to_tuple with mods'.
  - intros Helem.
    rewrite elem_of_union in Helem.
    destruct Helem.
    + rewrite elem_of_singleton in H. rewrite H.
      apply mods_global_to_tuple with mods.
      split; [set_solver | done].
    + apply mods_tuple_to_global in H.
      destruct H as (mods' & Helem & Hlookup').
      apply mods_global_to_tuple with mods'.
      split; [set_solver | done].
Qed.

Lemma per_tuple_mods_minus_None
      {tmods : gset (nat * dbmap)} {tid : nat} {mods : dbmap} {k : u64} :
  mods !! k = None ->
  per_tuple_mods (tmods ∖ {[ (tid, mods) ]}) k = per_tuple_mods tmods k.
Proof.
  intros Hlookup.
  destruct (decide ((tid, mods) ∈ tmods)); last first.
  { by replace (_ ∖ _) with tmods by set_solver. }
  rewrite {2} (union_difference_L {[ (tid, mods) ]} tmods); last set_solver.
  set tmods' := _ ∖ _.
  symmetry.
  by apply per_tuple_mods_union_None.
Qed.

Lemma tmods_global_to_key_notin {tmods : gset (nat * dbmap)} {tid : nat} k v :
  (∀ mods, (tid, mods) ∉ tmods) ->
  (tid, v) ∉ per_tuple_mods tmods k.
Proof.
  intros Hnotin Helem.
  apply mods_tuple_to_global in Helem.
  destruct Helem as (mods & Helem & _).
  set_solver.
Qed.

Lemma per_tuple_mods_minus_Some
      {tmods : gset (nat * dbmap)} {tid : nat} {mods : dbmap} {k : u64} (v : dbval) :
  NoDup (elements tmods).*1 ->
  (tid, mods) ∈ tmods ->
  mods !! k = Some v ->
  per_tuple_mods (tmods ∖ {[ (tid, mods) ]}) k = (per_tuple_mods tmods k) ∖ {[ (tid, v) ]}.
Proof.
  intros HND Helem Hlookup.
  rewrite {2} (union_difference_L {[ (tid, mods) ]} tmods); last set_solver.
  set tmods' := _ ∖ _.
  pose proof (tmods_NoDup_notin_difference HND Helem) as Hnotin.
  apply (tmods_global_to_key_notin k v) in Hnotin.
  rewrite (per_tuple_mods_union_Some v); [set_solver | done].
Qed.

Definition find_tid_val_step (tid : nat) (x : nat * dbval) (res : (option nat) * dbval)
  : (option nat) * dbval :=
  match res.1 with
  | None => if decide (x.1 < tid) then (Some x.1, x.2) else res
  | Some tid' => if decide (tid' < x.1 < tid) then (Some x.1, x.2) else res
  end.

Lemma find_tid_val_step_noop tid x res :
  (tid ≤ x.1)%nat ->
  find_tid_val_step tid x res = res.
Proof.
  intros Hle.
  unfold find_tid_val_step.
  destruct res.1 eqn:E.
  - case_decide; [lia | done].
  - case_decide; [lia | done].
Qed.
  
Definition find_tid_val (tid : nat) (v : dbval) (l : list (nat * dbval)) : (option nat) * dbval :=
  foldr (find_tid_val_step tid) (None, v) l.

Lemma find_tid_val_unfold tid v l :
  find_tid_val tid v l = foldr (find_tid_val_step tid) (None, v) l.
Proof. reflexivity. Qed.

Definition find_val tid v l := (find_tid_val tid v l).2.

Definition imme_pred (l : list nat) (p n : nat) :=
  p ∈ l ∧ (p < n)%nat ∧ Forall (λ x, x ≤ p ∨ n ≤ x)%nat l.

Lemma find_tid_val_spec tid v l :
  let res := find_tid_val tid v l in
  match res.1 with
  | None => Forall (λ x, tid ≤ x)%nat l.*1 ∧ res.2 = v
  | Some tid' => imme_pred l.*1 tid' tid ∧ (tid', res.2) ∈ l
  end.
Proof.
  induction l as [| x l IHl].
  - by simpl.
  - simpl in IHl.
    destruct (find_tid_val _ _ l).1 eqn:E.
    + unfold find_tid_val. simpl.
      unfold find_tid_val_step. rewrite E.
      case_decide.
      * simpl.
        destruct IHl as [(Helem & Hlt & Hl) _].
        split; last first.
        { rewrite -(surjective_pairing x). set_solver. }
        split; first set_solver.
        split; first lia.
        apply Forall_cons.
        split; first lia.
        apply (Forall_impl _ _ _ Hl).
        lia.
      * rewrite E.
        destruct IHl as [(Helem & Hlt & Hl) Helem'].
        split; last set_solver.
        split; first set_solver.
        split; first lia.
        apply Forall_cons.
        split; first lia.
        apply (Forall_impl _ _ _ Hl).
        lia.
    + unfold find_tid_val. simpl.
      unfold find_tid_val_step. rewrite E.
      case_decide.
      * simpl.
        split; last first.
        { rewrite -(surjective_pairing x). set_solver. }
        split; first set_solver.
        split; first lia.
        apply Forall_cons.
        split; first lia.
        destruct IHl as [IHl _].
        apply (Forall_impl _ _ _ IHl).
        lia.
      * rewrite E.
        destruct IHl as [IHl Heq].
        split; last auto.
        apply Forall_cons.
        split; first lia.
        apply (Forall_impl _ _ _ IHl).
        lia.
Qed.

Lemma find_tid_val_Some tid d l :
  Exists (λ x, x.1 < tid)%nat l ->
  ∃ tid' v', find_tid_val tid d l = (Some tid', v') ∧ imme_pred l.*1 tid' tid ∧ (tid', v') ∈ l.
Proof.
  intros HExists.
  rewrite Exists_exists in HExists.
  destruct HExists as (x & Helem & Hlt).
  pose proof (find_tid_val_spec tid d l) as Hspec. simpl in Hspec.
  destruct (find_tid_val tid d l).1 eqn:E.
  - destruct Hspec as [_ Helem'].
    pose proof (find_tid_val_spec tid d l) as Hspec. simpl in Hspec.
    rewrite E in Hspec.
    set res := (find_tid_val tid d l).
    exists n, res.2.
    split; last auto.
    rewrite (surjective_pairing res).
    by apply pair_equal_spec.
  - destruct Hspec as [Hallge _].
    apply (list_elem_of_fmap_2 fst) in Helem. simpl in Helem.
    rewrite Forall_forall in Hallge.
    apply Hallge in Helem. lia.
Qed.

Lemma find_tid_val_None tid d l :
  Forall (λ x, tid ≤ x.1)%nat l ->
  find_tid_val tid d l = (None, d).
Proof.
  intros HForall.
  induction l as [| x l IHl]; first set_solver.
  rewrite Forall_cons in HForall.
  destruct HForall as [Hx HForall].
  simpl. rewrite IHl; last auto.
  unfold find_tid_val_step. simpl.
  by case_decide; first lia.
Qed.

Lemma find_tid_val_Exists tid d1 d2 l :
  Exists (λ x, x.1 < tid)%nat l ->
  find_tid_val tid d1 l = find_tid_val tid d2 l.
Proof.
  intros HExists.
  induction l as [| x l IHl]; first by apply Exists_nil in HExists.
  simpl.
  apply Exists_cons in HExists.
  destruct HExists.
  - destruct (decide (Forall (λ x, tid ≤ x.1)%nat l)).
    + pose proof (find_tid_val_None _ d1 l f).
      pose proof (find_tid_val_None _ d2 l f).
      rewrite H0 H1.
      unfold find_tid_val_step. simpl.
      by case_decide; last lia.
    + apply not_Forall_Exists in n; last apply _.
      f_equal.
      apply IHl.
      apply (Exists_impl _ _ _ n).
      simpl. lia.
  - f_equal. by apply IHl.
Qed.

Lemma find_tid_val_extensible tid tid' v l :
  Forall (λ x, x.1 < tid')%nat l ->
  (tid' ≤ tid)%nat ->
  find_tid_val tid' v l = find_tid_val tid v l.
Proof.
  intros Hallgt Hle.
  induction l as [| x l IHl]; first done.
  simpl.
  rewrite Forall_cons in Hallgt.
  destruct Hallgt as [Hx Hallgt].
  rewrite IHl; last auto.
  set res := (find_tid_val _ _ _).
  unfold find_tid_val_step.
  destruct res.1.
  - case_decide.
    + case_decide; [done | lia].
    + case_decide; [lia | done].
  - case_decide; last lia.
    case_decide; last lia. done.
Qed.

Lemma imme_pred_perm_eq (p1 p2 n : nat) (l1 l2 : list nat) :
  l1 ≡ₚ l2 ->
  imme_pred l1 p1 n ->
  imme_pred l2 p2 n ->
  p1 = p2.
Proof.
  intros Hperm Hl1 Hl2.
  destruct Hl1 as (Helem1 & Hlt1 & Hl1).
  destruct Hl2 as (Helem2 & Hlt2 & Hl2).
  rewrite elem_of_Permutation_proper in Helem1; last apply Hperm.
  apply Permutation_sym in Hperm.
  rewrite elem_of_Permutation_proper in Helem2; last apply Hperm.
  rewrite Forall_forall in Hl1.
  rewrite Forall_forall in Hl2.
  apply Hl1 in Helem2.
  apply Hl2 in Helem1.
  lia.
Qed.

Lemma NoDup_perm_fmap_fst (l1 l2 : list (nat * dbval)) (a : nat) (b1 b2 : dbval) :
  NoDup l1.*1 ->
  l1 ≡ₚ l2 ->
  (a, b1) ∈ l1 ->
  (a, b2) ∈ l2 ->
  b1 = b2.
Proof.
  intros HNoDup Hperm Helem1 Helem2.
  apply Permutation_sym in Hperm.
  rewrite elem_of_Permutation_proper in Helem2; last apply Hperm.
  (* Funny way to prove this... *)
  pose proof (elem_of_list_to_map_1 _ _ _ HNoDup Helem1) as H1.
  pose proof (elem_of_list_to_map_1 _ _ _ HNoDup Helem2) as H2.
  naive_solver.
Qed.

Lemma NoDup_elements_fmap_fst_union (tid : nat) (v : dbval) (s : gset (nat * dbval)) :
  tid ∉ (elements s).*1 ->
  NoDup (elements s).*1 ->
  NoDup (elements ({[ (tid, v) ]} ∪ s)).*1.
Proof.
  intros Hnotin HNoDup.
  rewrite fmap_Permutation; last first.
  { apply elements_union_singleton.
    intros contra.
    rewrite -elem_of_elements in contra.
    by apply (list_elem_of_fmap_2 fst) in contra.
  }
  rewrite fmap_cons. simpl.
  by apply NoDup_cons_2; last auto.
Qed.

Lemma NoDup_elements_fmap_fst_difference (tid : nat) (v : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  NoDup (elements (s ∖ {[ (tid, v) ]})).*1.
Proof.
  intros HNoDup.
  destruct (decide ((tid, v) ∈ s)); last first.
  { by replace (s ∖ _) with s by set_solver. }
  rewrite (union_difference_singleton_L _ _ e) in HNoDup.
  remember (s ∖ _) as s'.
  rewrite fmap_Permutation in HNoDup; last first.
  { apply elements_union_singleton. set_solver. }
  rewrite fmap_cons NoDup_cons in HNoDup.
  by destruct HNoDup as [_ HNoDup].
Qed.

Lemma find_tid_val_perm tid v l1 l2 :
  NoDup l1.*1 ->
  l1 ≡ₚ l2 ->
  find_tid_val tid v l1 = find_tid_val tid v l2.
Proof.
  intros HNoDup Hperm.
  assert (Hpermfst : l1.*1 ≡ₚ l2.*1) by by apply fmap_Permutation.
  pose proof (find_tid_val_spec tid v l1) as Hl1.
  pose proof (find_tid_val_spec tid v l2) as Hl2.
  simpl in Hl1, Hl2.
  destruct (find_tid_val _ _ l1).1 eqn:E1.
  - destruct (find_tid_val _ _ l2).1 eqn:E2.
    + destruct Hl1 as [Hl1 Helem1].
      destruct Hl2 as [Hl2 Helem2].
      pose proof (imme_pred_perm_eq _ _ _ _ _ Hpermfst Hl1 Hl2) as Heq.
      subst n0.
      rewrite (surjective_pairing (find_tid_val _ _ l1)).
      rewrite (surjective_pairing (find_tid_val _ _ l2)).
      rewrite E1 E2.
      apply pair_equal_spec.
      split; first done.
      apply (NoDup_perm_fmap_fst l1 l2 n); auto.
    + destruct Hl1 as [(Hn & Hlt & _) _].
      destruct Hl2 as [Hl2 _].
      rewrite elem_of_Permutation_proper in Hn; last apply Hpermfst.
      rewrite Forall_forall in Hl2.
      apply Hl2 in Hn. lia.
  - destruct (find_tid_val _ _ l2).1 eqn:E2.
    + destruct Hl2 as [(Hn & Hlt & _) _].
      destruct Hl1 as [Hl1 _].
      apply Permutation_sym in Hpermfst.
      rewrite elem_of_Permutation_proper in Hn; last apply Hpermfst.
      rewrite Forall_forall in Hl1.
      apply Hl1 in Hn. lia.
    + unfold find_val.
      destruct Hl1 as [_ Helem1].
      destruct Hl2 as [_ Helem2].
      rewrite (surjective_pairing (find_tid_val _ _ l1)).
      rewrite (surjective_pairing (find_tid_val _ _ l2)).
      rewrite E1 E2.
      apply pair_equal_spec.
      split; first done.
      by rewrite Helem1 Helem2.
Qed.

Definition diff_tid_val_at (tid : nat) (v : dbval) (s : gset (nat * dbval)) :=
  find_tid_val tid v (elements s).

Lemma diff_tid_val_at_unfold tid v s :
  diff_tid_val_at tid v s = find_tid_val tid v (elements s).
Proof. reflexivity. Qed.

Definition diff_val_at (tid : nat) (v : dbval) (s : gset (nat * dbval)) :=
  (diff_tid_val_at tid v s).2.

Definition le_tids_mods (tid : nat) (mods : gset (nat * dbval)) :=
  set_Forall (λ x, (tid <= x.1)%nat) mods.

Definition gt_tids_mods (tid : nat) (mods : gset (nat * dbval)) :=
  set_Forall (λ x, (x.1 < tid)%nat) mods.

Lemma le_tids_mods_weaken tid tid' mods :
  (tid ≤ tid')%nat ->
  le_tids_mods tid' mods ->
  le_tids_mods tid mods.
Proof. intros Hle H. apply (set_Forall_impl _ _ _ H). lia. Qed.

Lemma gt_tids_mods_Forall_fmap_fst tid mods :
  gt_tids_mods tid mods ->
  Forall (λ n, (n < tid)%nat) (elements mods).*1.
Proof.
  intros H.
  unfold gt_tids_mods in H.
  rewrite set_Forall_elements in H.
  by apply Forall_fmap.
Qed.
                                        
Lemma diff_tid_val_at_le_all tid v s :
  le_tids_mods tid s ->
  diff_tid_val_at tid v s = (None, v).
Proof.
  intros Hle.
  unfold le_tids_mods in Hle. rewrite set_Forall_elements in Hle.
  unfold diff_tid_val_at.
  remember (elements s) as l.
  clear Heql.
  induction l as [| x l IHl]; first auto.
  rewrite Forall_cons in Hle.
  destruct Hle as [Hx Hle].
  apply IHl in Hle.
  unfold find_tid_val.
  simpl.
  unfold find_tid_val in Hle.
  rewrite Hle.
  unfold find_tid_val_step. simpl.
  case_decide; [lia | done].
Qed.

Lemma diff_val_at_le_all tid v s :
  le_tids_mods tid s ->
  diff_val_at tid v s = v.
Proof.
  intros Hle. unfold diff_val_at.
  rewrite diff_tid_val_at_le_all; done.
Qed.

Lemma diff_tid_val_at_S (tid : nat) (v d : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  (tid, v) ∈ s ->
  diff_tid_val_at (S tid) d s = (Some tid, v).
Proof.
  intros HNoDup Hin.
  rewrite -elem_of_elements in Hin.
  unfold diff_tid_val_at.
  remember (elements s) as l.
  clear Heql s.
  induction l as [| x l IHl]; first set_solver.
  simpl.
  rewrite fmap_cons NoDup_cons in HNoDup.
  destruct HNoDup as [Hnotin HNoDup].
  rewrite elem_of_cons in Hin.
  destruct Hin.
  - unfold find_tid_val_step.
    rewrite (surjective_pairing x) in H. inversion H.
    destruct (find_tid_val _ _ _).1 eqn:E.
    + pose proof (find_tid_val_spec (S x.1) d l) as Hspec.
      simpl in Hspec. rewrite E in Hspec.
      destruct Hspec as [(Helem & Hlt & _) _].
      assert (Hneq : tid ≠ n).
      { intros Heq. rewrite Heq in H1. set_solver. }
      assert (Hlt' : n < tid) by lia.
      case_decide; [done | lia].
    + case_decide; [done | lia].
  - rewrite IHl; [| auto | auto].
    unfold find_tid_val_step. simpl.
    case_decide; [lia | done].
Qed.

Lemma diff_val_at_S (tid : nat) (v d : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  (tid, v) ∈ s ->
  diff_val_at (S tid) d s = v.
Proof.
  intros HNoDup Hin. unfold diff_val_at.
  rewrite (diff_tid_val_at_S _ v); done.
Qed.

Lemma diff_val_at_gt_min_sub_min (tid tid' : nat) (v d : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  le_tids_mods tid' s ->
  (tid', v) ∈ s ->
  (tid' < tid)%nat ->
  diff_val_at tid d s = diff_val_at tid v (s ∖ {[(tid', v)]}).
Proof.
  intros HNoDup Hmin Helem Hlt.
  unfold diff_val_at.
  apply union_difference_singleton_L in Helem.
  rewrite {1} Helem.
  set s' := (s ∖ _).
  unfold diff_tid_val_at.
  rewrite (find_tid_val_perm _ _ _ ((tid', v) :: elements s')); last first.
  { apply elements_union_singleton. set_solver. }
  { subst s'. rewrite -union_difference_singleton_L; set_solver. }
  destruct (decide (set_Forall (λ x, tid ≤ x.1)%nat s')).
  - (* No proper TID in the new set [s']. *)
    rewrite -diff_tid_val_at_unfold.
    rewrite (diff_tid_val_at_le_all _ v); last auto.
    simpl.
    rewrite -diff_tid_val_at_unfold diff_tid_val_at_le_all; last done.
    unfold find_tid_val_step. simpl.
    case_decide; [done | lia].
  - apply not_set_Forall_Exists in n; last apply _.
    destruct n as (x & Helem' & Hgt).
    simpl in Hgt. apply not_le in Hgt.
    simpl.
    assert (HExists : Exists (λ x, x.1 < tid)%nat (elements s')).
    { rewrite Exists_exists. exists x. set_solver. }
    rewrite (find_tid_val_Exists _ d v); last auto.
    destruct (find_tid_val_Some tid v (elements s')) as (tidu & u & Heq & _ & Helemu); first auto.
    rewrite Heq.
    unfold find_tid_val_step.
    simpl.
    case_decide; last done.
    assert (contra : (tid' ≤ (tidu, u).1)%nat).
    { unfold set_Forall in Hmin. apply Hmin. set_solver. }
    simpl in contra. lia.
Qed.


Lemma diff_val_at_empty (tid : nat) (v : dbval) :
  diff_val_at tid v ∅ = v.
Proof. done. Qed.

Lemma diff_val_at_extensible (tid tid' : nat) (v : dbval) (s : gset (nat * dbval)) :
  gt_tids_mods tid' s ->
  (tid' ≤ tid)%nat ->
  diff_val_at tid' v s = diff_val_at tid v s.
Proof.
  intros Hallgt Hle.
  unfold diff_val_at, diff_tid_val_at.
  unfold gt_tids_mods in Hallgt.
  rewrite set_Forall_elements in Hallgt.
  rewrite (find_tid_val_extensible tid tid'); auto.
Qed.

Lemma diff_tid_val_at_add_max_le_max (tid tid' : nat) (v d : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  gt_tids_mods tid' s ->
  (tid ≤ tid')%nat ->
  diff_tid_val_at tid d ({[(tid', v)]} ∪ s) = diff_tid_val_at tid d s.
Proof.
  intros HNoDup Hgt_all Hle.
  unfold diff_tid_val_at.
  erewrite find_tid_val_perm; last first.
  { apply elements_union_singleton.
    intros contra.
    unfold gt_tids_mods in Hgt_all.
    apply Hgt_all in contra.
    simpl in contra. lia.
  }
  { apply NoDup_elements_fmap_fst_union; last done.
    intros contra.
    apply gt_tids_mods_Forall_fmap_fst in Hgt_all.
    rewrite Forall_forall in Hgt_all.
    apply Hgt_all in contra. lia.
  }
  simpl.
  rewrite find_tid_val_step_noop; [done | by simpl].
Qed.

Lemma diff_val_at_add_max_le_max (tid tid' : nat) (v d : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  gt_tids_mods tid' s ->
  (tid ≤ tid')%nat ->
  diff_val_at tid d ({[(tid', v)]} ∪ s) = diff_val_at tid d s.
Proof.
  intros HNoDup Hgt_all Hle.
  unfold diff_val_at.
  rewrite diff_tid_val_at_add_max_le_max; auto.
Qed.

Definition tuple_mods_rel (phys logi : list dbval) (mods : gset (nat * dbval)) :=
  ∃ (diff : list dbval) (v : dbval),
    logi = phys ++ diff ∧
    last phys = Some v ∧
    NoDup (elements mods).*1 ∧
    set_Forall (λ x, (length phys ≤ S x.1 < length logi)%nat) mods ∧
    ∀ (i : nat) (u : dbval), diff !! i = Some u ->
                           u = diff_val_at (i + length phys) v mods.

Lemma tuple_mods_rel_eq_empty (phys logi : list dbval) (mods : gset (nat * dbval)) :
  phys = logi ->
  tuple_mods_rel phys logi mods ->
  mods = ∅.
Proof.
  intros Heq (diff & v & _ & _ & _ & Hlen & _).
  destruct (decide (mods = ∅)); first done.
  apply set_choose_L in n.
  destruct n as [x Helem].
  rewrite Heq in Hlen.
  apply Hlen in Helem. lia.
Qed.

Lemma tuple_mods_rel_last_phys (phys logi : list dbval) (mods : gset (nat * dbval)) :
  tuple_mods_rel phys logi mods ->
  ∃ v, last phys = Some v.
Proof.
  intros Hrel.
  destruct Hrel as (diff & v & _ & H & _).
  by eauto.
Qed.

Lemma tuple_mods_rel_last_logi (phys logi : list dbval) (mods : gset (nat * dbval)) :
  tuple_mods_rel phys logi mods ->
  ∃ v, last logi = Some v.
Proof.
  intros Hrel.
  destruct Hrel as (diff & v & Hprefix & Hphys & _).
  rewrite Hprefix.
  rewrite last_app.
  destruct (last diff); eauto.
Qed.

Lemma tuple_mods_rel_prefix (phys logi : list dbval) (mods : gset (nat * dbval)) :
  tuple_mods_rel phys logi mods ->
  prefix phys logi.
Proof.
  intros Hrel.
  unfold tuple_mods_rel in Hrel.
  destruct Hrel as (diff & v & H & _). unfold prefix.
  by eauto.
Qed.

Theorem tuplext_read (tid : nat) (phys logi : list dbval) (mods : gset (nat * dbval)) :
  (tid < length logi)%nat ->
  le_tids_mods tid mods ->
  tuple_mods_rel phys logi mods ->
  tuple_mods_rel (extend (S tid) phys) logi mods.
Proof.
  intros Hub Hle_all (diff & v & Hprefix & Hlast & HNoDup & Hlen & Hdiff).
  unfold tuple_mods_rel.
  set lenext := (S tid - length phys)%nat.
  exists (drop lenext diff), v.
  split.
  { (* prefix *)
    apply (extend_last_Some (S tid)) in Hlast as Heq.
    rewrite Heq Hprefix -app_assoc.
    rewrite app_inv_head_iff.
    rewrite -{1} (take_drop lenext diff).
    rewrite app_inv_tail_iff.
    symmetry. apply replicate_as_Forall.
    split.
    { rewrite length_take_le; first done.
      rewrite Hprefix length_app in Hub. lia.
    }
    rewrite Forall_forall.
    intros u Helem.
    apply list_elem_of_lookup in Helem.
    destruct Helem as [i Hlookup].
    rewrite lookup_take_Some in Hlookup.
    destruct Hlookup as [Hlookup Hle].
    apply Hdiff in Hlookup.
    rewrite Hlookup.
    symmetry. apply diff_val_at_le_all.
    subst lenext.
    assert (H : (i + length phys ≤ tid)%nat) by lia.
    apply le_tids_mods_weaken with tid; auto.
  }
  split.
  { (* last *) rewrite -Hlast. apply extend_last. }
  split; first done.
  split.
  { (* len *)
    unfold le_tids_mods in Hle_all.
    rewrite extend_length; last eauto.
    intros x Helem.
    apply Hlen in Helem as H1.
    apply Hle_all in Helem as H2.
    split; lia.
  }
  { (* diff *)
    intros i u Hlookup.
    rewrite lookup_drop in Hlookup.
    apply Hdiff in Hlookup.
    rewrite Hlookup.
    f_equal.
    rewrite extend_length; [lia | eauto].
  }
Qed.

Theorem tuplext_write (tid : nat) (v : dbval) (phys logi : list dbval) (mods : gset (nat * dbval)) :
  le_tids_mods tid mods ->
  (tid, v) ∈ mods ->
  tuple_mods_rel phys logi mods ->
  tuple_mods_rel ((extend (S tid) phys) ++ [v]) logi (mods ∖ {[(tid, v)]}).
Proof.
  intros Hle_all Hinmods (diff & w & Hprefix & Hlast & HNoDup & Hlen & Hdiff).
  assert (Hub : (S tid < length logi)%nat).
  { apply Hlen in Hinmods. simpl in Hinmods. lia. }
  assert (Hlb : (length phys ≤ S tid)%nat).
  { apply Hlen in Hinmods. simpl in Hinmods. lia. }
  unfold tuple_mods_rel.
  set lenext := S (S tid - length phys)%nat.
  exists (drop lenext diff), v.
  split.
  { (* prefix *)
    apply (extend_last_Some (S tid)) in Hlast as Heq.
    rewrite Heq Hprefix -app_assoc -app_assoc.
    rewrite app_inv_head_iff.
    rewrite -{1} (take_drop lenext diff).
    rewrite app_assoc.
    rewrite app_inv_tail_iff.
    rewrite (take_S_r _ _ v); last first.
    { (* value at [tid + 1] *)
      assert (Hgoal : ∃ v', diff !! (S tid - length phys)%nat = Some v').
      { apply list_lookup_lt.
        rewrite Hprefix length_app in Hub. lia.
      }
      destruct Hgoal as [v' Hgoal].
      apply Hdiff in Hgoal as Hv'.
      replace (S tid - _ + _)%nat with (S tid)%nat in Hv' by lia.
      rewrite (diff_val_at_S tid v w mods) in Hv'; [| auto | auto].
      by rewrite Hv' in Hgoal.
    }
    rewrite app_inv_tail_iff.
    symmetry. apply replicate_as_Forall.
    split.
    { rewrite length_take_le; first done.
      rewrite Hprefix length_app in Hub. lia.
    }
    rewrite Forall_forall.
    intros u Helem.
    apply list_elem_of_lookup in Helem.
    destruct Helem as [i Hlookup].
    rewrite lookup_take_Some in Hlookup.
    destruct Hlookup as [Hlookup Hle].
    apply Hdiff in Hlookup.
    rewrite Hlookup.
    symmetry. apply diff_val_at_le_all.
    subst lenext.
    assert (H : (i + length phys ≤ tid)%nat) by lia.
    apply le_tids_mods_weaken with tid; auto.
  }
  split.
  { (* last *) by rewrite last_snoc. }
  split.
  { (* unique *) by apply NoDup_elements_fmap_fst_difference. }
  split.
  { (* len *)
    unfold le_tids_mods in Hle_all.
    rewrite length_app.
    rewrite extend_length; last eauto.
    intros x Helem.
    assert (Helem' : x ∈ mods) by set_solver.
    apply Hlen in Helem' as H1.
    apply Hle_all in Helem' as H2.
    assert (Hneq : x.1 ≠ tid).
    { intros Heq.
      rewrite elem_of_difference in Helem.
      destruct Helem as [_ Hnotin].
      rewrite not_elem_of_singleton in Hnotin.
      replace x with (x.1, x.2) in Helem', Hnotin; last first.
      { symmetry. apply surjective_pairing. }
      subst tid.
      rewrite -elem_of_elements in Hinmods.
      rewrite -elem_of_elements in Helem'.
      assert (Heq : v = x.2).
      { eapply NoDup_perm_fmap_fst; eauto. }
      by subst v.
    }
    simpl.
    split; lia.
  }
  { (* diff *)
    intros i u Hlookup.
    rewrite lookup_drop in Hlookup.
    apply Hdiff in Hlookup.
    rewrite Hlookup.
    rewrite length_app.
    rewrite extend_length; last eauto.
    rewrite (Nat.add_comm _ i).
    rewrite -(Nat.add_assoc i).
    simpl.
    replace (S tid - _ + _)%nat with (S tid)%nat; last lia.
    replace (tid + 1)% nat with (S tid)%nat; last lia.
    replace (S tid + 1)%nat with (S (S tid))%nat; last lia.
    apply diff_val_at_gt_min_sub_min; [auto | auto | auto | lia].
  }
Qed.

Theorem tuplext_linearize_unchanged (tid : nat) (phys logi : list dbval) (mods : gset (nat * dbval)) :
  tuple_mods_rel phys logi mods ->
  tuple_mods_rel phys (extend (S tid) logi) mods.
Proof.
  intros Hrel.
  pose proof Hrel as (diff & v & Hprefix & Hlast & HNoDup & Hlen & Hdiff).
  unfold tuple_mods_rel.
  assert (Hlast' : ∃ v', last logi = Some v').
  { rewrite Hprefix last_app. destruct (last diff); eauto. }
  destruct Hlast' as [v' Hlast'].
  exists (diff ++ replicate (S tid - length logi) v'), v.
  split.
  { (* prefix *)
    apply (extend_last_Some (S tid)) in Hlast' as Heq.
    by rewrite Heq Hprefix -app_assoc.
  }
  split.
  { (* last *) done. }
  split; first done.
  split.
  { (* len *)
    apply (set_Forall_impl _ _ _ Hlen).
    intros x Hlt.
    split; first lia.
    apply Nat.lt_le_trans with (length logi); [lia | apply extend_length_ge].
  }
  { (* diff *)
    intros i u Hlookup.
    destruct (decide (i < length diff)%nat).
    - apply Hdiff. by rewrite lookup_app_l in Hlookup; last auto.
    - apply not_lt in n.
      rewrite lookup_app_r in Hlookup; last lia.
      rewrite lookup_replicate in Hlookup.
      destruct Hlookup as [Heq Hlt]. subst v'.
      (* Case [diff = nil] is treated as a special case. *)
      destruct (decide (diff = [])).
      { rewrite e app_nil_r in Hprefix.
        rewrite (tuple_mods_rel_eq_empty phys logi mods); [| auto | done].
        rewrite diff_val_at_empty. subst logi.
        rewrite Hlast' in Hlast.
        by inversion Hlast.
      }
      (* Use the last value of [logi] as the reference to apply [diff_val_at_extensible]. *)
      rewrite last_lookup in Hlast'.
      rewrite -(diff_val_at_extensible _ (pred (length diff) + length phys)); last first.
      { lia. }
      { unfold gt_tids_mods.
        apply (set_Forall_impl _ _ _ Hlen).
        intros x [_ H].
        rewrite Hprefix length_app in H. lia.
      }
      apply Hdiff.
      rewrite -Hlast'.
      do 2 rewrite -last_lookup.
      rewrite Hprefix.
      rewrite last_app.
      destruct (last diff) eqn:E; [done | by rewrite last_None in E].
  }
Qed.

Theorem tuplext_linearize_changed (tid : nat) (v : dbval) (phys logi : list dbval) (mods : gset (nat * dbval)) :
  (length logi ≤ S tid)%nat ->
  tuple_mods_rel phys logi mods ->
  tuple_mods_rel phys ((extend (S tid) logi) ++ [v]) ({[(tid, v)]} ∪ mods).
Proof.
  intros Hlb Hrel.
  pose proof Hrel as (diff & w & Hprefix & Hlast & HNoDup & Hlen & Hdiff).
  unfold tuple_mods_rel.
  assert (Hlast' : ∃ v', last logi = Some v').
  { rewrite Hprefix last_app. destruct (last diff); eauto. }
  destruct Hlast' as [v' Hlast'].
  exists (diff ++ replicate (S tid - length logi) v' ++ [v]), w.
  split.
  { (* prefix *)
    apply (extend_last_Some (S tid)) in Hlast' as Heq.
    rewrite Heq Hprefix.
    by do 2 rewrite -app_assoc.
  }
  split.
  { (* last *) done. }
  split.
  { apply NoDup_elements_fmap_fst_union; last done.
    intros contra.
    (* Q: ugly... better way? *)
    replace (λ x, (_ ≤ S x.1 < _)%nat) with ((λ n, (length phys ≤ S n < length logi)%nat) ∘ (fst : nat * dbval -> nat)) in Hlen by done.
    rewrite set_Forall_elements -Forall_fmap Forall_forall in Hlen.
    apply Hlen in contra. lia.
  }
  split.
  { (* len *)
    apply set_Forall_union.
    { rewrite set_Forall_singleton. simpl.
      split.
      - trans (length logi); last lia.
        rewrite Hprefix length_app. lia.
      - rewrite length_app. simpl.
        apply Nat.le_lt_trans with (length (extend (S tid) logi)); last lia.
        apply extend_length_ge_n. eauto.
    }
    apply (set_Forall_impl _ _ _ Hlen).
    intros x [H1 H2].
    split; first lia.
    rewrite length_app. simpl.
    apply Nat.lt_le_trans with (length logi); first lia.
    apply Nat.le_trans with (length (extend (S tid) logi)); [apply extend_length_ge | lia].
  }
  { (* diff *)
    intros i u Hlookup.
    assert (Hgt_all : gt_tids_mods tid mods).
    { intros x Helem.
      assert (Hgoal : (S x.1 < S tid)%nat).
      { apply Hlen in Helem. apply Nat.lt_le_trans with (length logi); lia. }
      lia.
    }
    pose proof Hlb as Hlb'.
    rewrite Hprefix length_app in Hlb'.
    destruct (decide (i < S tid - length phys)%nat); last first.
    { apply Nat.nle_gt in n.
      rewrite lookup_app_r in Hlookup; last lia.
      rewrite lookup_app_r in Hlookup; last first.
      { rewrite length_replicate Hprefix length_app. lia. }
      rewrite list_lookup_singleton_Some in Hlookup.
      destruct Hlookup as [Hi Heq].
      rewrite length_replicate in Hi.
      rewrite Hprefix length_app in Hi.
      assert (Hi' : (i + length phys = S tid)%nat) by lia.
      rewrite Hi'.
      rewrite (diff_val_at_S _ v); [done | | set_solver].
      apply NoDup_elements_fmap_fst_union; last done.
      intros contra.
      apply gt_tids_mods_Forall_fmap_fst in Hgt_all.
      rewrite Forall_forall in Hgt_all.
      apply Hgt_all in contra. lia.
    }
    rewrite diff_val_at_add_max_le_max; [| done | done | lia].
    rewrite app_assoc in Hlookup.
    rewrite lookup_app_l in Hlookup; last first.
    { rewrite length_app length_replicate Hprefix length_app. lia. }
    destruct (decide (i < length diff)%nat).
    - apply Hdiff. by rewrite lookup_app_l in Hlookup; last auto.
    - apply not_lt in n.
      rewrite lookup_app_r in Hlookup; last lia.
      rewrite lookup_replicate in Hlookup.
      destruct Hlookup as [Heq Hlt]. subst v'.
      (* Case [diff = nil] is treated as a special case. *)
      destruct (decide (diff = [])).
      { rewrite e app_nil_r in Hprefix.
        rewrite (tuple_mods_rel_eq_empty phys logi mods); [| auto | done].
        rewrite diff_val_at_empty. subst logi.
        rewrite Hlast' in Hlast.
        by inversion Hlast.
      }
      (* Use the last value of [logi] as the reference to apply [diff_val_at_extensible]. *)
      rewrite last_lookup in Hlast'.
      rewrite -(diff_val_at_extensible _ (pred (length diff) + length phys)); last first.
      { lia. }
      { unfold gt_tids_mods.
        apply (set_Forall_impl _ _ _ Hlen).
        intros x [_ H].
        rewrite Hprefix length_app in H. lia.
      }
      apply Hdiff.
      rewrite -Hlast'.
      do 2 rewrite -last_lookup.
      rewrite Hprefix.
      rewrite last_app.
      destruct (last diff) eqn:E; [done | by rewrite last_None in E].
  }
Qed.
