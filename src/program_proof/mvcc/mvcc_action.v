From Perennial.program_proof.mvcc Require Import mvcc_prelude.

Inductive action :=
| ActCommit (tid : nat) (mods : dbmap)
| ActRead   (tid : nat) (key : u64)
| ActAbort  (tid : nat).

Definition head_commit (l : list action) (tid : nat) (mods : dbmap) :=
  head l = Some (ActCommit tid mods).

Definition head_read (l : list action) (tid : nat) (key : u64) :=
  head l = Some (ActRead tid key).

Definition head_abort (l : list action) (tid : nat) :=
  head l = Some (ActAbort tid).

Definition no_commit_abort (l : list action) (tid : nat) :=
  (∀ mods, ActCommit tid mods ∉ l) ∧
  (ActAbort tid ∉ l).

Definition first_abort (l : list action) (tid : nat) :=
  ∃ lp ls,
    l = lp ++ (ActAbort tid) :: ls ∧
    no_commit_abort lp tid.

Definition compatible (tid : nat) (mods : dbmap) (e : action) :=
  match e with
  | ActCommit tid' mods' => (tid' < tid)%nat ∨ (dom mods) ∩ (dom mods') = ∅
  | ActRead tid' key => (tid' ≤ tid)%nat ∨ key ∉ (dom mods)
  | ActAbort tid' => True
  end.

#[local]
Instance compatible_dec tid mods e : Decision (compatible tid mods e).
Proof. destruct e; simpl; apply _. Defined.

Definition incompatible (tid : nat) (mods : dbmap) (e : action) := not (compatible tid mods e).

#[local]
Instance incompatible_dec tid mods e : Decision (incompatible tid mods e).
Proof. destruct e; simpl; apply _. Defined.

Definition compatible_all (l : list action) (tid : nat) (mods : dbmap) :=
  Forall (compatible tid mods) l.

Definition incompatible_exists (l : list action) (tid : nat) (mods : dbmap) :=
  Exists (incompatible tid mods) l.

Definition first_commit (l lp ls : list action) (tid : nat) (mods : dbmap) :=
  l = lp ++ (ActCommit tid mods) :: ls ∧
  no_commit_abort lp tid.

Definition first_commit_incompatible (l1 l2 : list action) (tid : nat) (mods : dbmap) :=
  ∃ lp ls,
    first_commit l2 lp ls tid mods ∧
    incompatible_exists (l1 ++ lp) tid mods.

Definition first_commit_compatible (l : list action) (tid : nat) (mods : dbmap) :=
  ∃ lp ls,
    first_commit l lp ls tid mods ∧
    compatible_all lp tid mods.

Definition is_commit_abort_tid (tid : nat) (e : action) : Prop :=
  match e with
  | ActCommit tid' _ => tid = tid'
  | ActAbort tid' => tid = tid'
  | _ => False
  end.

#[local]
Instance is_commit_abort_dec tid e : Decision (is_commit_abort_tid tid e).
Proof. destruct e; simpl; apply _. Defined.

Lemma is_commit_abort_tid_lor tid e :
  is_commit_abort_tid tid e ->
  (∃ mods, e = ActCommit tid mods) ∨ e = ActAbort tid.
Proof. intros. destruct e; set_solver. Qed.

Fixpoint find_max_prefix (tid : nat) (lp ls : list action) : (list action * list action) :=
  match ls with
  | [] => (lp, ls)
  | hd :: tl => if decide (is_commit_abort_tid tid hd)
              then (lp, ls)
              else find_max_prefix tid (lp ++ [hd]) tl
  end.

Lemma spec_find_max_prefix tid lp ls :
  ∃ ls1 ls2,
    (lp ++ ls1, ls2) = find_max_prefix tid lp ls ∧
    ls = ls1 ++ ls2 ∧
    no_commit_abort ls1 tid ∧
    (match head ls2 with
     | Some e => is_commit_abort_tid tid e
     | _ => True
     end).
Proof.
  generalize dependent lp.
  unfold no_commit_abort.
  induction ls as [| e ls IHls]; intros lp; simpl.
  - exists [], [].
    split; first by rewrite app_nil_r.
    set_solver.
  - case_decide.
    + exists [], (e :: ls).
      split; first by rewrite app_nil_r.
      set_solver.
    + destruct (IHls (lp ++ [e])) as (ls1 & ls2 & Heq & Hls2 & Hnca & Hhead).
      exists ([e] ++ ls1), ls2.
      rewrite -Heq.
      split; first by rewrite app_assoc.
      split; set_solver.
Qed.

Inductive tcform :=
| NCA
| FA
| FCI (mods : dbmap)
| FCC (mods : dbmap).

Definition peek (l : list action) (tid : nat) : tcform :=
  let (lp, ls) := find_max_prefix tid [] l
  in match head ls with
     | None => NCA
     | Some e => match e with
                | ActCommit _ mods => if decide (compatible_all lp tid mods) then FCC mods else FCI mods
                | _ => FA
                end
     end.

Theorem spec_peek l tid :
  match peek l tid with
  | NCA => no_commit_abort l tid
  | FA => first_abort l tid
  | FCI mods => first_commit_incompatible [] l tid mods
  | FCC mods => first_commit_compatible l tid mods
  end.
Proof.
  unfold peek.
  destruct (spec_find_max_prefix tid [] l) as (lp & ls & Hspec & Hl & Hnca & Hls).
  rewrite -Hspec.
  destruct (head ls) eqn:Els.
  - destruct a eqn:Ee.
    + simpl.
      apply is_commit_abort_tid_lor in Hls.
      destruct Hls as [[mods' Hls] | Hls]; last set_solver.
      inversion Hls. subst tid0 mods'.
      assert (Hfc : first_commit l lp (tail ls) tid mods).
      { unfold first_commit.
        split; last done.
        rewrite Hl.
        f_equal.
        by apply hd_error_tl_repr.
      }
      case_decide.
      * unfold first_commit_compatible.
        by exists lp, (tail ls).
      * unfold first_commit_incompatible.
        exists lp, (tail ls).
        unfold compatible_all in H.
        by apply not_Forall_Exists in H; last apply _.
    + unfold is_commit_abort_tid in Hls. set_solver.
    + apply is_commit_abort_tid_lor in Hls.
      destruct Hls; first set_solver.
      inversion H. subst tid0.
      unfold first_abort.
      exists lp, (tail ls).
      split; last done.
      rewrite Hl.
      f_equal.
      by apply hd_error_tl_repr.
  - apply head_None in Els.
    rewrite Els in Hl. rewrite app_nil_r in Hl. by rewrite Hl.
Qed.

Lemma no_commit_abort_false {l : list action} {tid : nat} :
  no_commit_abort l tid ->
  (∃ mods, head_commit l tid mods) ∨ (head_abort l tid) ->
  False.
Proof.
  intros [HnotinC HnotinA] [[mods Hhead] | Hhead]; apply head_Some_elem_of in Hhead; set_solver.
Qed.

Lemma head_middle {X} (l lp ls : list X) (x : X) :
  l = lp ++ x :: ls ->
  head l = head (lp ++ [x]).
Proof.
  intros Hl. rewrite Hl. destruct lp; auto.
Qed.

Theorem first_abort_false {l : list action} {tid : nat} (mods : dbmap) :
  first_abort l tid ->
  head_commit l tid mods ->
  False.
Proof.
  intros (lp & ls & Hl & HnotinC & _) Hhead.
  unfold head_commit in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  apply head_Some_elem_of in Hhead.
  set_solver.
Qed.

Theorem first_commit_false {l lp ls : list action} {tid : nat} {mods : dbmap} :
  first_commit l lp ls tid mods ->
  head_abort l tid ->
  False.
Proof.
  intros (Hl & _ & HnotinA) Hhead.
  unfold head_abort in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  apply head_Some_elem_of in Hhead.
  set_solver.
Qed.

Theorem first_commit_eq {l lp ls : list action} {tid : nat} {mods mods' : dbmap} :
  first_commit l lp ls tid mods ->
  head_commit l tid mods' ->
  mods = mods'.
Proof.
  intros (Hl & HnotinC & _) Hhead.
  unfold head_commit in Hhead.
  destruct lp; set_solver.
Qed.

Theorem safe_extension_rd (l : list action) (tid tid' : nat) (mods : dbmap) (key : u64) :
  first_commit_compatible l tid mods ->
  head_read l tid' key ->
  key ∈ (dom mods) ->
  (tid' ≤ tid)%nat.
Proof.
  intros (lp & ls & [Hl _] & Hcomp) Hhead Hin.
  unfold head_read in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  destruct lp; first set_solver.
  simpl in Hhead.
  inversion Hhead.
  unfold compatible_all in Hcomp.
  rewrite Forall_forall in Hcomp.
  destruct (Hcomp (ActRead tid' key)); [| done | done].
  rewrite H0.
  apply list_elem_of_here.
Qed.

Theorem safe_extension_wr (l : list action) (tid tid' : nat) (mods mods' : dbmap) :
  first_commit_compatible l tid mods ->
  head_commit l tid' mods' ->
  (dom mods) ∩ (dom mods') ≠ ∅ ->
  (tid' ≤ tid)%nat.
Proof.
  intros (lp & ls & [Hl _] & Hcomp) Hhead Hdom.
  unfold head_commit in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  destruct lp; first set_solver.
  simpl in Hhead.
  inversion Hhead.
  unfold compatible_all in Hcomp.
  rewrite Forall_forall in Hcomp.
  destruct (Hcomp (ActCommit tid' mods')); [| word | done].
  rewrite H0.
  apply list_elem_of_here.
Qed.

Lemma first_commit_incompatible_Exists (l1 l2 : list action) (tid : nat) (mods : dbmap) :
  first_commit_incompatible l1 l2 tid mods ->
  head_commit l2 tid mods ->
  Exists (incompatible tid mods) l1.
Proof.
  intros (lp & ls & [Hl [HnotinC _]] & Hincomp) Hhead.
  destruct lp; first by rewrite app_nil_r in Hincomp.
  unfold head_commit in Hhead.
  set_solver.
Qed.

Lemma Exists_incompatible_exists (l : list action) (tid : nat) (mods : dbmap) :
  Exists (incompatible tid mods) l ->
  ∃ key tid', key ∈ dom mods ∧
    ((ActRead tid' key ∈ l ∧ (tid < tid')%nat) ∨
     (∃ mods', key ∈ dom mods' ∧ ActCommit tid' mods' ∈ l ∧ (tid ≤ tid')%nat)).
Proof.
  intros H.
  rewrite Exists_exists in H.
  destruct H as (a & Helem & Hincomp).
  unfold incompatible, compatible in Hincomp.
  destruct a as [tid' mods' | tid' key |] eqn:E; last done.
  - (* Case Evcommit. *)
    apply Decidable.not_or in Hincomp.
    destruct Hincomp as [Hle Hoverlap].
    assert (Hindom : ∃ key, key ∈ dom mods ∧ key ∈ dom mods').
    { apply set_choose_L in Hoverlap. set_solver. }
    destruct Hindom as (key & Hindom & Hindom').
    eauto 10 with lia.
  - (* Case ActRead. *)
    apply Decidable.not_or in Hincomp.
    destruct Hincomp as [Hlt Hindom].
    apply dec_stable in Hindom.
    eauto 10 with lia.
Qed.

Lemma notin_tail {X} (x : X) (l : list X) :
  x ∉ l ->
  x ∉ tail l.
Proof.
  intros Hnotin.
  destruct l; first done.
  intros contra. simpl in contra. set_solver.
Qed.

Lemma no_commit_abort_preserved (l l' : list action) {tid : nat} :
  l' = tail l ->
  no_commit_abort l tid ->
  no_commit_abort l' tid.
Proof.
  intros Htl [Hnc Hna].
  rewrite Htl.
  unfold no_commit_abort in *.
  split.
  - intros mods. by apply notin_tail.
  - by apply notin_tail.
Qed.
  
Lemma first_abort_preserved {l l' : list action} {a : action} {tid : nat} :
  l = a :: l' ->
  a ≠ ActAbort tid ->
  first_abort l tid ->
  first_abort l' tid.
Proof.
  intros Hhead Hneq Hfa.
  destruct Hfa as (lp & ls & [Hl [HnotinC HnotinA]]).
  exists (tail lp), ls.
  split; last first.
  { unfold no_commit_abort.
    split; last by apply notin_tail.
    intros mods'. by apply notin_tail.
  }
  destruct lp eqn:Elp; first set_solver.
  simpl.
  rewrite -hd_error_tl_repr in Hhead.
  destruct Hhead as [_ Hl'].
  by rewrite -Hl' Hl.
Qed.

Lemma first_commit_incompatible_preserved {p l l' : list action} {a : action} {tid : nat} {mods : dbmap} :
  l = a :: l' ->
  (∀ mods', a ≠ ActCommit tid mods') ->
  first_commit_incompatible p l tid mods ->
  first_commit_incompatible (p ++ [a]) l' tid mods.
Proof.
  intros Hhead Hneq Hfci.
  destruct Hfci as (lp & ls & [Hl [HnotinC HnotinA]] & Hincomp).
  exists (tail lp), ls.
  split; last first.
  { rewrite -app_assoc.
    simpl.
    replace (a :: tail lp) with lp; first done.
    destruct lp eqn:Elp; first set_solver.
    simpl.
    rewrite -hd_error_tl_repr in Hhead.
    destruct Hhead as [Hhead _].
    set_solver.
  }
  split; last first.
  { unfold no_commit_abort.
    split; last by apply notin_tail.
    intros mods'. by apply notin_tail.
  }
  unfold first_commit.
  destruct lp eqn:Elp; first set_solver.
  simpl.
  rewrite -hd_error_tl_repr in Hhead.
  destruct Hhead as [_ Hl'].
  by rewrite -Hl' Hl.
Qed.

Lemma first_commit_compatible_preserved {l l' : list action} {a : action} {tid : nat} {mods : dbmap} :
  l = a :: l' ->
  (∀ mods', a ≠ ActCommit tid mods') ->
  first_commit_compatible l tid mods ->
  first_commit_compatible l' tid mods.
Proof.
  intros Hhead Hneq Hfcc.
  destruct Hfcc as (lp & ls & [Hl [HnotinC HnotinA]] & Hcomp).
  exists (tail lp), ls.
  split; last by apply Forall_tail.
  split; last first.
  { unfold no_commit_abort.
    split; last by apply notin_tail.
    intros mods'. by apply notin_tail.
  }
  unfold first_commit.
  destruct lp eqn:Elp; first set_solver.
  simpl.
  rewrite -hd_error_tl_repr in Hhead.
  destruct Hhead as [_ Hl'].
  by rewrite -Hl' Hl.
Qed.

Theorem first_commit_incompatible_suffix (l1 l2 : list action) (tid : nat) (mods : dbmap) :
  first_commit_incompatible [] l2 tid mods ->
  first_commit_incompatible l1 l2 tid mods.
Proof.
  intros Hfci.
  unfold first_commit_incompatible in *.
  destruct Hfci as (lp & ls & Hfc & Hincomp).
  exists lp, ls.
  split; first auto.
  simpl in Hincomp.
  apply Exists_app. by right.
Qed.
