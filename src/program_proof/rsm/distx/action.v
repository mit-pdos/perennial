From Perennial.program_proof Require Import grove_prelude.
(* TODO: remove this once invariance proof moved to their places. *)
From Perennial.program_proof.rsm.pure Require Import list.
From Perennial.program_proof.rsm.distx Require Import base.

Definition head_commit (l : list action) (ts : nat) (wrs : dbmap) :=
  head l = Some (ActCommit ts wrs).

Definition head_abort (l : list action) (ts : nat) :=
  head l = Some (ActAbort ts).

Definition head_read (l : list action) (ts : nat) (key : dbkey) :=
  head l = Some (ActRead ts key).

Definition no_commit_abort (l : list action) (tid : nat) :=
  ActAbort tid ∉ l ∧ ∀ wrs, ActCommit tid wrs ∉ l.

Definition first_abort (l : list action) (ts : nat) :=
  ∃ lp ls,
    l = lp ++ ls ∧
    no_commit_abort lp ts ∧
    head ls = Some (ActAbort ts).

Definition first_commit (l lp ls : list action) (ts : nat) (wrs : dbmap) :=
  l = lp ++ ls ∧
  no_commit_abort lp ts ∧
  head ls = Some (ActCommit ts wrs).

Definition compatible (ts : nat) (wrs : dbmap) (a : action) :=
  match a with
  | ActCommit tsa wrsa => (tsa < ts)%nat ∨ (dom wrs) ∩ (dom wrsa) = ∅
  | ActRead tsa key => (tsa ≤ ts)%nat ∨ key ∉ (dom wrs)
  | _ => True
  end.

#[local]
Instance compatible_dec ts wrs a : Decision (compatible ts wrs a).
Proof. destruct a; simpl; apply _. Defined.

Definition incompatible (ts : nat) (wrs : dbmap) (a : action) := not (compatible ts wrs a).

Definition compatible_all (l : list action) (ts : nat) (wrs : dbmap) :=
  Forall (compatible ts wrs) l.

Definition incompatible_exists (l : list action) (ts : nat) (wrs : dbmap) :=
  Exists (incompatible ts wrs) l.

Lemma not_compatible_all_incompatible_exists l ts wrs :
  not (compatible_all l ts wrs) ↔ incompatible_exists l ts wrs.
Proof.
  split; intros H.
  - by apply not_Forall_Exists in H; last apply _.
  - by apply Exists_not_Forall in H.
Qed.

(** A more natural definition of [first_commit] would be hiding [lp] and [ls]
with exists, but and intuitively it says "the first commit action in [l] with
timestamp [ts] is [ActCommit ts wrs]". However, [first_commit_incompatible]
needs access to the first part of [l] (i.e., the one without any commit action
of timestamp [ts], so we expose [lp] and [ls] as well. *)

Definition first_commit_incompatible (l1 l2 : list action) (ts : nat) (wrs : dbmap) :=
  ∃ lp ls,
    first_commit l2 lp ls ts wrs ∧
    incompatible_exists (l1 ++ lp) ts wrs.

Definition first_commit_compatible (l : list action) (ts : nat) (wrs : dbmap) :=
  ∃ lp ls,
    first_commit l lp ls ts wrs ∧
    compatible_all lp ts wrs.

Definition is_commit_abort_of_ts (ts : nat) act :=
  match act with
  | ActCommit tid _ => tid = ts
  | ActAbort tid => tid = ts
  | _ => False
  end.

Lemma is_commit_abort_of_ts_spec ts act :
  is_commit_abort_of_ts ts act ->
  act = ActAbort ts ∨ ∃ wrs, act = ActCommit ts wrs.
Proof.
  intros Hca.
  destruct act; last done; rewrite Hca.
  - right. by eauto.
  - by left.
Qed.

#[local]
Instance is_commit_abort_of_ts_dec ts a : Decision (is_commit_abort_of_ts ts a).
Proof. destruct a; simpl; apply _. Defined.

Fixpoint find_max_prefix_before_commit_abort
  (ts : nat) (lp ls : list action) : (list action * list action) :=
  match ls with
  | [] => (lp, ls)
  | hd :: tl => if decide (is_commit_abort_of_ts ts hd)
              then (lp, ls)
              else find_max_prefix_before_commit_abort ts (lp ++ [hd]) tl
  end.

Lemma find_max_prefix_before_commit_abort_spec ts lp ls :
  ∃ ls1 ls2,
    find_max_prefix_before_commit_abort ts lp ls = (lp ++ ls1, ls2) ∧
    ls = ls1 ++ ls2 ∧
    no_commit_abort ls1 ts ∧
    match head ls2 with
    | Some a => is_commit_abort_of_ts ts a
    | _ => True
    end.
    (* (ls2 = [] ∨ is_commit_abort_of_ts ts (head ls2)). *)
Proof.
  generalize dependent lp.
  rewrite /no_commit_abort.
  induction ls as [| a ls IH]; intros lp; simpl.
  { exists [], [].
    split; first by rewrite app_nil_r.
    split; first done.
    split; last done.
    rewrite /no_commit_abort. set_solver.
  }
  case_decide as Ha.
  - destruct (IH (lp ++ [a])) as (ls1 & ls2 & Heq & Hls2 & Hnca & Hhead).
    exists [], (a :: ls).
    split; first by rewrite app_nil_r.
    split; set_solver.
  - destruct (IH (lp ++ [a])) as (ls1 & ls2 & Heq & Hls2 & Hnca & Hhead).
    exists ([a] ++ ls1), ls2.
    split; first by rewrite app_assoc Heq.
    split; set_solver.
Qed.

Inductive tcform :=
(* no commit or abort in the entire list of actions *)
| NCA
(* first action is abort *)
| FA
(* first action is commit and it's incompatible with some previous actions *)
| FCI (wrs : dbmap)
(* first action is commit and it's compatible with some previous actions *)
| FCC (wrs : dbmap).

Definition peek (l : list action) (ts : nat) : tcform :=
  let (lp, ls) := find_max_prefix_before_commit_abort ts [] l in
  match head ls with
  | None => NCA
  | Some a => match a with
             | ActCommit _ wrs => if decide (compatible_all lp ts wrs)
                                 then FCC wrs
                                 else FCI wrs
             | _ => FA
             end
  end.

Definition conflict_cases
  (past future : list action) (ts : nat) (form : tcform) :=
  match form with
  | NCA => no_commit_abort future ts
  | FA => first_abort future ts
  | FCI wrs => first_commit_incompatible past future ts wrs
  | FCC wrs => first_commit_compatible future ts wrs
  end.

Theorem peek_spec l ts :
  conflict_cases [] l ts (peek l ts).
Proof.
  unfold peek.
  destruct (find_max_prefix_before_commit_abort_spec ts [] l) as (lp & ls & -> & Hl & Hnca & Hls).
  destruct (head ls) as [a |] eqn:Hhead; last first.
  { rewrite head_None in Hhead. subst ls. by rewrite /= Hl app_nil_r. }
  apply is_commit_abort_of_ts_spec in Hls.
  destruct Hls as [-> | [wrs ->]].
  { by exists lp, ls. }
  case_decide as Hcomp.
  { by exists lp, ls. }
  { exists lp, ls. by rewrite -not_compatible_all_incompatible_exists. }
Qed.

Lemma first_commit_head_abort future lp ls ts wrs :
  first_commit future lp ls ts wrs ->
  head_abort future ts ->
  False.
Proof.
  intros (Happ & [Hna _] & Hhead) Hha.
  destruct lp as [| x l]; last first.
  { rewrite Happ /head_abort /= in Hha.
    inv Hha.
    set_solver.
  }
  rewrite Happ /= /head_abort Hhead in Hha.
  by inv Hha.
Qed.

Lemma no_commit_abort_inv_tail_future future ts :
  no_commit_abort future ts ->
  no_commit_abort (tail future) ts.
Proof.
  intros [Hna Hnca].
  split.
  - by apply not_elem_of_tail.
  - intros wrs. by apply not_elem_of_tail.
Qed.

Lemma first_abort_inv_tail_future future ts a :
  a ≠ ActAbort ts ->
  head future = Some a ->
  first_abort future ts ->
  first_abort (tail future) ts.
Proof.
  intros Hne Hhead (lp & ls & (Happ & Hnca & Hheadls)).
  assert (Hnnil : lp ≠ nil).
  { intros Hlp. subst lp.
    simpl in Happ. subst ls.
    rewrite Hhead in Hheadls.
    inv Hheadls.
  }
  exists (tail lp), ls.
  split.
  { rewrite Happ. apply tail_app_l, Hnnil. }
  by split; first apply no_commit_abort_inv_tail_future.
Qed.

Lemma first_commit_incompatible_inv_snoc_past_tail_future past future ts wrs a :
  a ≠ ActCommit ts wrs ->
  head future = Some a ->
  first_commit_incompatible past future ts wrs ->
  first_commit_incompatible (past ++ [a]) (tail future) ts wrs.
Proof.
  intros Hne Hhead (lp & ls & (Happ & Hnca & Hheadls) & Hincomp).
  assert (Hnnil : lp ≠ nil).
  { intros Hlp. subst lp.
    simpl in Happ. subst ls.
    rewrite Hhead in Hheadls.
    inv Hheadls.
  }
  exists (tail lp), ls.
  split.
  { split.
    { rewrite Happ. apply tail_app_l, Hnnil. }
    by split; first apply no_commit_abort_inv_tail_future.
  }
  rewrite -app_assoc /=.
  replace (_ :: _) with lp; first apply Hincomp.
  rewrite -hd_error_tl_repr.
  split; last done.
  rewrite -Hhead.
  apply head_prefix; first apply Hnnil.
  rewrite Happ.
  by apply prefix_app_r.
Qed.

Lemma first_commit_incompatible_inv_tail_future past future ts tshd wrs :
  head_abort future tshd ->
  first_commit_incompatible past future ts wrs ->
  first_commit_incompatible past (tail future) ts wrs.
Proof.
  intros Hhead (lp & ls & (Happ & Hnca & Hheadls) & Hincomp).
  assert (Hnnil : lp ≠ nil).
  { intros Hlp. subst lp.
    simpl in Happ. subst ls.
    rewrite Hhead in Hheadls.
    inv Hheadls.
  }
  exists (tail lp), ls.
  split.
  { split.
    { rewrite Happ. apply tail_app_l, Hnnil. }
    by split; first apply no_commit_abort_inv_tail_future.
  }
  revert Hincomp.
  rewrite /incompatible_exists 2!Exists_app.
  intros Hincomp.
  destruct Hincomp as [Hincomp | Hincomp]; first by left.
  right.
  destruct lp as [| x t]; first done. simpl.
  rewrite Exists_cons in Hincomp.
  destruct Hincomp as [Hincomp | Hincomp]; last done.
  exfalso.
  rewrite /head_abort Happ /= in Hhead.
  inv Hhead.
  by rewrite /incompatible in Hincomp.
Qed.

Lemma first_commit_compatible_inv_tail_future future ts wrs a :
  a ≠ ActCommit ts wrs ->
  head future = Some a ->
  first_commit_compatible future ts wrs ->
  first_commit_compatible (tail future) ts wrs.
Proof.
  intros Hne Hhead (lp & ls & (Happ & Hnca & Hheadls) & Hincomp).
  assert (Hnnil : lp ≠ nil).
  { intros Hlp. subst lp.
    simpl in Happ. subst ls.
    rewrite Hhead in Hheadls.
    inv Hheadls.
  }
  exists (tail lp), ls.
  split.
  { split.
    { rewrite Happ. apply tail_app_l, Hnnil. }
    by split; first apply no_commit_abort_inv_tail_future.
  }
  by apply Forall_tail.
Qed.
