From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.proof Require Import proof_prelude.
From Perennial.Helpers Require Import bytes NamedProps.

From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi.

From New.proof.github_com.sanjit_bhat.pav.merkle_proof Require Import base serde.

Notation get_bit l n := (bytes_to_bits l !!! n : bool).

Section prefix_total.
Context `{!Inhabited A}.
Implicit Types x : A.
Implicit Types l : list A.

(* prefix of a list extended with inhabitant. *)
Definition prefix_total : relation (list A) :=
  λ l1 l2, ∃ n k, l2 ++ replicate n inhabitant = l1 ++ k.

#[global] Instance prefix_total_dec `{!EqDecision A} : RelDecision prefix_total.
Proof. Admitted.
(*
  fix go (l1 l2 : list A) :=
  match l1, l2 with
  | [], _ => left (prefix_nil _)
  | x :: l1, [] =>
    if x inhabitant, good. recurse.
    else, reject.
  | x :: l1, y :: l2 =>
    match decide_rel (=) x y with
    | left Hxy =>
      match go l1 l2 with
      | left Hl1l2 => left (prefix_cons_alt _ _ _ _ Hxy Hl1l2)
      | right Hl1l2 => right (Hl1l2 ∘ prefix_cons_inv_2 _ _ _ _)
      end
    | right Hxy => right (Hxy ∘ prefix_cons_inv_1 _ _ _ _)
    end
  end.
*)

Lemma prefix_total_nil l :
  prefix_total [] l.
Proof. exists 0%nat. by eexists. Qed.

Lemma prefix_total_snoc l0 l1 x :
  prefix_total l0 l1 →
  l1 !!! length l0 = x →
  prefix_total (l0 ++ [x]) l1.
Proof. Admitted.

Lemma prefix_total_snoc_inv l0 l1 x :
  prefix_total (l0 ++ [x]) l1 →
  prefix_total l0 l1 ∧ l1 !!! length l0 = x.
Proof. Admitted.

Lemma prefix_total_neq l0 l1 l2 :
  prefix_total l0 l1 →
  ¬ prefix_total l0 l2 →
  l1 ≠ l2.
Proof. Admitted.

Lemma prefix_total_app_l l1 l2 l3 :
  prefix_total (l1 ++ l3) l2 →
  prefix_total l1 l2.
Proof. Admitted.

Lemma prefix_total_full p l :
  length p = length l →
  prefix_total p l →
  p = l.
Proof.
  rewrite /prefix_total.
  intros ? (?&?&Heq).
  apply (f_equal (take (length l))) in Heq.
  by rewrite !take_app_length' in Heq.
Qed.

End prefix_total.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

(** tree. *)

(* [Cut]s denote a cut off tree.
for full trees, they come from invalid hashes,
while for partial trees, it's just an unknown-origin hash.
unifying these two types of Cuts allows for unified tree predicates.

a different approach to invalid full trees bubbles invalidness all the way to the top,
i.e., inversion resulting in option map.
that has the undesirable effect of invalidness "stopping the proof". *)
Inductive tree :=
  | Empty
  | Leaf (label val : list w8)
  | Inner (child0 child1 : tree)
  | Cut (hash : list w8).

(** tree paths. *)

Fixpoint find' t depth label :=
  match t with
  | Empty => None
  | Leaf l v => Some (l, v)
  | Inner c0 c1 =>
    let c := if get_bit label depth then c1 else c0 in
    find' c (S depth) label
  | Cut _ => None (* [None] matches [to_map]. *)
  end.
Definition find t label := find' t 0 label.
Hint Unfold find : merkle.

Definition found_nonmemb label (found : option $ (list w8 * list w8)%type) :=
  match found with
  | None => True
  | Some (found_label, _) => label ≠ found_label
  end.

Definition is_entry t label oval :=
  ∃ f,
  find t label = f ∧
  match oval with
  | Some v => f = Some (label, v)
  | None => found_nonmemb label f
  end.
Hint Unfold is_entry : merkle.

(** relation between trees and maps. *)

Fixpoint to_map t : gmap (list w8) (list w8) :=
  match t with
  | Leaf label val => {[label := val ]}
  | Inner child0 child1 => to_map child0 ∪ to_map child1
  | _ => ∅
  end.

Fixpoint is_sorted' t pref :=
  match t with
  (* using [prefix_total] allows other preds (e.g., [is_entry])
  to operate under an easier (and weaker), length-extended leaf model.
  this reduces proof burden.
  e.g., [find] doesn't need to track depth bounds. *)
  | Leaf label val => prefix_total pref (bytes_to_bits label)
  | Inner c0 c1 =>
    is_sorted' c0 (pref ++ [false]) ∧
    is_sorted' c1 (pref ++ [true])
  | _ => True
  end.
Definition is_sorted t := is_sorted' t [].
Hint Unfold is_sorted : merkle.

Lemma to_map_None_strong t pref label :
  is_sorted' t pref →
  ¬ prefix_total pref (bytes_to_bits label) →
  to_map t !! label = None.
Proof.
  revert pref.
  induction t; simpl; intros; try done.
  - opose proof (prefix_total_neq _ _ _ _ _) as Heq; [done..|].
    rewrite inj_iff in Heq.
    by simpl_map.
  - intuition.
    apply lookup_union_None_2.
    + eapply IHt1; [done|].
      by intros ?%prefix_total_app_l.
    + eapply IHt2; [done|].
      by intros ?%prefix_total_app_l.
Qed.

Tactic Notation "solve_bool" :=
  match goal with
  | H : ?x = negb ?x |- _ => by destruct x
  | H : negb ?x = ?x |- _ => by destruct x
  | |- ?x ≠ negb ?x => by destruct x
  | |- negb ?x ≠ ?x => by destruct x
  end.

Lemma to_map_None t pref bit label :
  is_sorted' t (pref ++ [bit]) →
  get_bit label (length pref) = negb bit →
  to_map t !! label = None.
Proof.
  intros.
  eapply to_map_None_strong; [done|].
  intros ?%prefix_total_snoc_inv.
  intuition. subst. solve_bool.
Qed.

Notation pref_ext p l := (p ++ [get_bit l (length p)]) (only parsing).

Lemma entry_to_lookup t label oval :
  is_sorted t →
  is_entry t label oval →
  to_map t !! label = oval.
Proof.
  autounfold with merkle.
  remember ([]) as pref.
  replace (0%nat) with (length pref) by (by subst).
  intros ? (?&?&?).
  assert (prefix_total pref (bytes_to_bits label)).
  { subst. apply prefix_total_nil. }
  clear Heqpref.
  generalize dependent pref.

  induction t; simpl; intros.
  - simpl_map. case_match; by subst.
  - case_match; simplify_eq/=; by simpl_map.
  - replace (S _) with (length $ pref_ext pref label) in * by len.
    intuition. rewrite lookup_union.
    case_match.
    + erewrite (to_map_None t1); [|done..].
      erewrite IHt2; cycle 1; [done|done|..].
      { by apply prefix_total_snoc. }
      by simplify_option_eq.
    + erewrite (to_map_None t2); [|done..].
      erewrite IHt1; cycle 1; [done|done|..].
      { by apply prefix_total_snoc. }
      by simplify_option_eq.
  - simpl_map. case_match; by subst.
Qed.

Lemma lookup_to_entry t label :
  is_sorted t →
  is_entry t label (to_map t !! label).
Proof.
  autounfold with merkle.
  remember ([]) as pref.
  replace (0%nat) with (length pref) by (by subst).
  assert (prefix_total pref (bytes_to_bits label)).
  { subst. apply prefix_total_nil. }
  clear Heqpref.
  generalize dependent pref.

  induction t; simpl; intros.
  - simpl_map. naive_solver.
  - eexists. intuition.
    destruct (decide (label = label0)); subst; by simpl_map.
  - replace (S _) with (length $ pref_ext pref label) in * by len.
    intuition. rewrite lookup_union.
    destruct (get_bit _ _) eqn:?.
    + erewrite (to_map_None t1); [|done..].
      rewrite left_id.
      eapply IHt2; try done.
      by apply prefix_total_snoc.
    + erewrite (to_map_None t2); [|done..].
      rewrite right_id.
      eapply IHt1; try done.
      by apply prefix_total_snoc.
  - simpl_map. naive_solver.
Qed.

Lemma entry_eq_lookup t label oval :
  is_sorted t →
  is_entry t label oval ↔ to_map t !! label = oval.
Proof.
  split.
  - by apply entry_to_lookup.
  - intros. subst. by apply lookup_to_entry.
Qed.

(** full trees / maps. *)

(* the overall structure of [is_full_tree] is a bit unconventional.
from the hash [h], it recursively computes (via [decode_node]) the tree [t].
a few consequences:
- it "resolves" the tree to the maximum extent possible.
- it limits invalid nodes only to when they're generated by decoding.
this allows proving [is_full_tree_inj].

[limit] prevents infinite recursion.
NOTE: many of the below cases are invariant to whether limit=0 or S l'.
to prevent duplicate proof branches, we use strong induction: [lt_wf_ind]. *)
Fixpoint is_full_tree' t h limit : iProp Σ :=
  ∃ d,
  "#His_hash" ∷ cryptoffi.is_hash d h ∗
  "#Hdecode" ∷ match decode_node d with
  | DecEmpty =>
    "%" ∷ ⌜ t = Empty ⌝
  | DecLeaf l v =>
    "%" ∷ ⌜ t = Leaf l v ⌝
  | DecInner h0 h1 =>
    match limit with
    | 0%nat =>
      "%" ∷ ⌜ t = Cut h ⌝
    | S limit' =>
      ∃ t0 t1,
      "#Hchild0" ∷ is_full_tree' t0 h0 limit' ∗
      "#Hchild1" ∷ is_full_tree' t1 h1 limit' ∗
      "%" ∷ ⌜ t = Inner t0 t1 ⌝
    end
  | DecInvalid =>
    "%" ∷ ⌜ t = Cut h ⌝
  end.
#[global] Arguments is_full_tree' !_.
Definition is_full_tree t h := is_full_tree' t h max_depth.
Hint Unfold is_full_tree : merkle.

(* rocq kernel doesn't allow reducing a fixpoint on its args without
the decreasing arg being a constructor.
this forces us to prove a manual unfolding lemma.
NOTE: ideally, automation could prove this. *)
Lemma is_full_tree_unfold t h limit :
  is_full_tree' t h limit
  ⊣⊢
  ∃ d,
  "#His_hash" ∷ cryptoffi.is_hash d h ∗
  "#Hdecode" ∷ match decode_node d with
  | DecEmpty =>
    "%" ∷ ⌜ t = Empty ⌝
  | DecLeaf l v =>
    "%" ∷ ⌜ t = Leaf l v ⌝
  | DecInner h0 h1 =>
    match limit with
    | 0%nat =>
      "%" ∷ ⌜ t = Cut h ⌝
    | S limit' =>
      ∃ t0 t1,
      "#Hchild0" ∷ is_full_tree' t0 h0 limit' ∗
      "#Hchild1" ∷ is_full_tree' t1 h1 limit' ∗
      "%" ∷ ⌜ t = Inner t0 t1 ⌝
    end
  | DecInvalid =>
    "%" ∷ ⌜ t = Cut h ⌝
  end.
Proof. destruct limit; naive_solver. Qed.

#[global] Instance is_full_tree_pers t h l : Persistent (is_full_tree' t h l).
Proof.
  revert t h. induction l as [? IH] using lt_wf_ind. intros.
  setoid_rewrite is_full_tree_unfold.
  apply exist_persistent. intros.
  repeat case_match; try apply _.
  ospecialize (IH n _); [lia|].
  apply _.
Qed.

Lemma is_full_tree_invert h l :
  Z.of_nat (length h) = cryptoffi.hash_len → ⊢
  ∃ t, is_full_tree' t h l.
Proof.
  revert h. induction l as [? IH] using lt_wf_ind. intros.
  setoid_rewrite is_full_tree_unfold.
  iDestruct (cryptoffi.is_hash_invert h) as "[% $]"; [done|].
  repeat case_match; try naive_solver.
  opose proof (decode_inner_inj _ _ _ _) as (_&?&?); [done|].
  ospecialize (IH n _); [lia|].
  iDestruct (IH hash0) as "[% $]"; [done|].
  iDestruct (IH hash1) as "[% $]"; [done|].
  naive_solver.
Qed.

(* if [Cut], carries the hash, so hashes must be equal.
otherwise, [decode_node_inj] says that Some preimg's are equal,
which implies the hashes are equal. *)
Lemma is_full_tree_det t h0 h1 l0 l1 :
  is_full_tree' t h0 l0 -∗
  is_full_tree' t h1 l1 -∗
  ⌜ h0 = h1 ⌝.
Proof.
  iInduction (l0) as [? IH] using lt_wf_ind forall (t h0 h1 l1);
    iEval (setoid_rewrite is_full_tree_unfold);
    iNamedSuffix 1 "0"; iNamedSuffix 1 "1";
    repeat case_match;
    iNamedSuffix "Hdecode0" "0"; iNamedSuffix "Hdecode1" "1";
    simplify_eq/=; try done.
  1-2:
    opose proof (decode_node_inj _ d d0 _ _ _) as (-> & [? ->]); [done..|];
    by iApply cryptoffi.is_hash_det.
  iSpecialize ("IH" $! n with "[]"); [word|].
  iDestruct ("IH" with "Hchild00 Hchild01") as %->.
  iDestruct ("IH" with "Hchild10 Hchild11") as %->.
  opose proof (decode_node_inj _ d d0 _ _ _) as (-> & [? ->]); [done..|].
  by iApply cryptoffi.is_hash_det.
Qed.

(* [is_full_tree_inj] demands the same [limit], which allows it to perform
the same number of hash inversions before potentially reaching [Cut].
merkle clients should all use the same [limit] in their code and proofs.
in practice, this limit is the hash length,
which was anyways required for liveness, and now is required for safety.
another approach is defining a predicate for limit validity.
however, the inversion lemma can't always guarantee this. *)
Lemma is_full_tree_inj t0 t1 h limit :
  is_full_tree' t0 h limit -∗
  is_full_tree' t1 h limit -∗
  ⌜ t0 = t1 ⌝.
Proof.
  iInduction (limit) as [? IH] using lt_wf_ind forall (t0 t1 h);
    iEval (setoid_rewrite is_full_tree_unfold);
    iNamedSuffix 1 "0"; iNamedSuffix 1 "1";
    iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %->;
    repeat case_match;
    iNamedSuffix "Hdecode0" "0"; iNamedSuffix "Hdecode1" "1";
    simplify_eq/=; try done.
  iSpecialize ("IH" $! n with "[]"); [word|].
  iDestruct ("IH" with "Hchild00 Hchild01") as %->.
  by iDestruct ("IH" with "Hchild10 Hchild11") as %->.
Qed.

#[global] Opaque is_full_tree'.

Definition is_map m h : iProp Σ :=
  ∃ t,
  "%Heq_map" ∷ ⌜ m = to_map t ⌝ ∗
  "#His_tree" ∷ is_full_tree t h.
Hint Unfold is_map : merkle.

Lemma is_map_invert h :
  Z.of_nat (length h) = cryptoffi.hash_len → ⊢
  ∃ m, is_map m h.
Proof.
  intros.
  iDestruct is_full_tree_invert as "[% H]"; [done|].
  iFrame "#".
  iPureIntro. naive_solver.
  (* NOTE: without [Opaque is_full_tree'], Qed spins forever.
  this happens even with [Arguments] constraints. *)
Qed.

Lemma is_map_inj m0 m1 h :
  is_map m0 h -∗
  is_map m1 h -∗
  ⌜ m0 = m1 ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (is_full_tree_inj with "His_tree0 His_tree1") as %->.
  by subst.
Qed.

(** cut trees. *)

(* [is_cut_tree] has a more traditional structure,
computing the hash [h] from the tree [t]. some consequences:
- it allows for trees that arbitrary cut off paths.
therefore, there are many trees with the same hash.
- it's hash structure more closely follows the code,
which make it easier to establish (and probably to use in lemmas). *)
Fixpoint is_cut_tree (t : tree) (h : list w8) : iProp Σ :=
  match t with
  | Empty =>
    "#His_hash" ∷ cryptoffi.is_hash (Some [emptyNodeTag]) h
  | Leaf label val =>
    "%Hlen_label" ∷ ⌜ length label < 2^64 ⌝ ∗
    "%Hlen_val" ∷ ⌜ length val < 2^64 ⌝ ∗
    "#His_hash" ∷
      cryptoffi.is_hash (Some $ [leafNodeTag] ++
        (u64_le $ length label) ++ label ++
        (u64_le $ length val) ++ val) h
  | Inner child0 child1 =>
    ∃ h0 h1,
    "#Hchild0" ∷ is_cut_tree child0 h0 ∗
    "#Hchild1" ∷ is_cut_tree child1 h1 ∗
    "#His_hash" ∷ cryptoffi.is_hash (Some $ [innerNodeTag] ++ h0 ++ h1) h
  | Cut ch =>
    "%Heq_cut" ∷ ⌜ h = ch ⌝ ∗
    "%Hlen_hash" ∷ ⌜ Z.of_nat $ length h = cryptoffi.hash_len ⌝
  end.

#[global]
Instance is_cut_tree_pers t h : Persistent (is_cut_tree t h).
Proof. revert h. induction t; apply _. Qed.

Fixpoint is_cutless t :=
  match t with
  | Cut _ => False
  | Inner child0 child1 => is_cutless child0 ∧ is_cutless child1
  | _ => True
  end.

Fixpoint is_cutless_path' t depth label :=
  match t with
  | Cut _ => False
  | Inner c0 c1 =>
    let c := if get_bit label depth then c1 else c0 in
    is_cutless_path' c (S depth) label
  | _ => True
  end.
Definition is_cutless_path t label := is_cutless_path' t 0 label.
Hint Unfold is_cutless_path : merkle.

Lemma is_cut_tree_len t h:
  is_cut_tree t h -∗
  ⌜ Z.of_nat $ length h = cryptoffi.hash_len ⌝.
Proof. destruct t; iNamed 1; [..|done]; by iApply cryptoffi.is_hash_len. Qed.

Lemma is_cut_tree_det t h0 h1 :
  is_cut_tree t h0 -∗
  is_cut_tree t h1 -∗
  ⌜ h0 = h1 ⌝.
Proof.
  iInduction t as [| ? | ? IH0 ? IH1 | ?] forall (h0 h1);
    simpl; iNamedSuffix 1 "0"; iNamedSuffix 1 "1".
  - by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %?.
  - by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %?.
  - iDestruct ("IH0" with "Hchild00 Hchild01") as %->.
    iDestruct ("IH1" with "Hchild10 Hchild11") as %->.
    by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %?.
  - naive_solver.
Qed.

(** full <-> cut tree reln. *)

Fixpoint is_limit' t limit :=
  match t with
  | Inner c0 c1 =>
    match limit with
    | 0%nat => False
    | S limit' =>
      is_limit' c0 limit' ∧
      is_limit' c1 limit'
    end
  | _ => True
  end.
Definition is_limit t := is_limit' t max_depth.
Hint Unfold is_limit : merkle.

Lemma is_limit_inc t (l0 l1 : nat) :
  is_limit' t l0 →
  l0 ≤ l1 →
  is_limit' t l1.
Proof.
  revert l0 l1.
  induction t; try done.
  simpl. intros.
  repeat (case_match; [done|]).
  naive_solver lia.
Qed.

Lemma full_entry_txfer t0 t1 h label oval :
  is_entry t0 label oval →
  is_cutless_path t0 label →
  is_limit t0 →
  is_cut_tree t0 h -∗
  is_full_tree t1 h -∗
  ⌜ is_entry t1 label oval ⌝.
Proof.
  autounfold with merkle.
  remember max_depth as limit. clear Heqlimit.
  remember 0%nat as depth. clear Heqdepth.
  iInduction t0 as [] forall (t1 h limit depth); simpl; iIntros "*";
    iEval (setoid_rewrite is_full_tree_unfold);
    iNamedSuffix 1 "0";
    iNamedSuffix 1 "1"; try done;
    iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %<-.
  - rewrite decode_empty_det. iNamed "Hdecode1". naive_solver.
  - rewrite decode_leaf_det; [|done..]. iNamed "Hdecode1". naive_solver.
  - iDestruct (is_cut_tree_len with "Hchild00") as %?.
    iDestruct (is_cut_tree_len with "Hchild10") as %?.
    rewrite decode_inner_det; [|done..].
    case_match; [done|].
    intuition.
    iNamedSuffix "Hdecode1" "1".
    subst. simpl.
    case_match.
    + by iApply "IHt0_2".
    + by iApply "IHt0_1".
Qed.

Lemma cut_to_full t h :
  is_cutless t →
  is_limit t →
  is_cut_tree t h -∗
  is_full_tree t h.
Proof.
  autounfold with merkle.
  remember max_depth as limit. clear Heqlimit.
  iInduction t as [] forall (h limit); simpl; iIntros "*";
    iEval (setoid_rewrite is_full_tree_unfold);
    iIntros "@"; try done;
    iFrame "#".
  - by rewrite decode_empty_det.
  - by rewrite decode_leaf_det.
  - iDestruct (is_cut_tree_len with "Hchild0") as %?.
    iDestruct (is_cut_tree_len with "Hchild1") as %?.
    rewrite decode_inner_det; [|done..].
    case_match; [done|].
    intuition.
    iExists _, _.
    repeat iSplit; [..|done].
    + by iApply "IHt1".
    + by iApply "IHt2".
Qed.

(** gallina tree ops.

need gallina transl of Golang [merkle.put] for determ spec.
determ needed bc user might call [VerifyMemb] multiple times on same tree,
expecting dig to be equal across calls.
to guarantee that, [merkle.proofToTree] needs to determ make tree from
inputted proof, and [merkle.put] needs to determ update tree with label, val. *)

(* NOTE: the code has tricky termination reasoning due to put-into-leaf
expanding common label bits into inner nodes.
this reasoning is reflected into gallina using [limit].
NOTE: separating [depth] from [limit] allows us to separate
label-index reasoning from termination reasoning.
otherwise, we'd have to track that, e.g., limit <= max_depth. *)
Fixpoint pure_put' t depth label val (limit : nat) :=
  match t with
  | Empty => Some (Leaf label val)
  | Leaf label' val' =>
    if decide (label = label') then Some (Leaf label val) else
    (* Golang put won't run out of limit. *)
    match limit with 0%nat => None | S limit' =>
    (* "unfolding" the two leaf puts lets us use [limit'] in recur calls. *)
    (* put 1. *)
    let t0_0 := if get_bit label' depth then Empty else t in
    let t0_1 := if get_bit label' depth then t else Empty in
    let t0 := if get_bit label depth then t0_1 else t0_0 in
    (* put 2. *)
    match pure_put' t0 (S depth) label val limit' with None => None | Some t1 =>
    let t2_0 := if get_bit label depth then t0_0 else t1 in
    let t2_1 := if get_bit label depth then t1 else t0_1 in
    Some $ Inner t2_0 t2_1
    end end
  | Inner c0 c1 =>
    match limit with 0%nat => None | S limit' =>
    let t0 := if get_bit label depth then c1 else c0 in
    match pure_put' t0 (S depth) label val limit' with None => None | Some t1 =>
    let t2_0 := if get_bit label depth then c0 else t1 in
    let t2_1 := if get_bit label depth then t1 else c1 in
    Some $ Inner t2_0 t2_1
    end end
  | Cut _ => None (* Golang put won't hit Cut. *)
  end.
Definition pure_put t label val := pure_put' t 0 label val max_depth.
Hint Unfold pure_put : merkle.
#[global] Arguments pure_put' !_.

Lemma pure_put_unfold t depth label val limit :
  pure_put' t depth label val limit
  =
  match t with
  | Empty => Some (Leaf label val)
  | Leaf label' val' =>
    if decide (label = label') then Some (Leaf label val) else
    (* Golang put won't run out of limit. *)
    match limit with 0%nat => None | S limit' =>
    (* "unfolding" the two leaf puts lets us use [limit'] in recur calls. *)
    (* put 1. *)
    let t0_0 := if get_bit label' depth then Empty else t in
    let t0_1 := if get_bit label' depth then t else Empty in
    let t0 := if get_bit label depth then t0_1 else t0_0 in
    (* put 2. *)
    match pure_put' t0 (S depth) label val limit' with None => None | Some t1 =>
    let t2_0 := if get_bit label depth then t0_0 else t1 in
    let t2_1 := if get_bit label depth then t1 else t0_1 in
    Some $ Inner t2_0 t2_1
    end end
  | Inner c0 c1 =>
    match limit with 0%nat => None | S limit' =>
    let t0 := if get_bit label depth then c1 else c0 in
    match pure_put' t0 (S depth) label val limit' with None => None | Some t1 =>
    let t2_0 := if get_bit label depth then c0 else t1 in
    let t2_1 := if get_bit label depth then t1 else c1 in
    Some $ Inner t2_0 t2_1
    end end
  | Cut _ => None (* Golang put won't hit Cut. *)
  end.
Proof. by destruct limit. Qed.

(* [sibs] order reversed from code for easier fixpoint. *)
Fixpoint pure_newShell' depth label (sibs : list $ list w8) :=
  match sibs with
  | [] => Empty
  | h :: sibs' =>
    let cut := Cut h in
    let t := pure_newShell' (S depth) label sibs' in
    let c0 := if get_bit label depth then cut else t in
    let c1 := if get_bit label depth then t else cut in
    Inner c0 c1
  end.
Definition pure_newShell label sibs := pure_newShell' 0 label sibs.
Hint Unfold pure_newShell : merkle.

Definition pure_proofToTree label sibs oleaf :=
  let t := pure_newShell label sibs in
  match oleaf with
  | None => Some t
  | Some (l, v) => pure_put t l v
  end.

(** invariants on [pure_put]. *)

Lemma cutless_new_put t label val :
  is_Some (pure_put t label val) →
  is_cutless_path t label.
Proof.
  autounfold with merkle.
  remember max_depth as limit. clear Heqlimit.
  remember 0%nat as depth. clear Heqdepth.
  revert t depth.
  induction limit as [? IH] using lt_wf_ind.
  intros *. rewrite pure_put_unfold.
  destruct t; simpl; intros; try done.
  case_match; try done.
  case_match; try done.
  eapply (IH n); [lia|done].
Qed.

Lemma cutless_over_put t t' label0 label1 val :
  is_cutless_path t label0 →
  pure_put t label1 val = Some t' →
  is_cutless_path t' label0.
Proof.
  autounfold with merkle.
  remember max_depth as limit. clear Heqlimit.
  remember 0%nat as depth. clear Heqdepth.
  revert t t' depth.
  induction limit as [? IH] using lt_wf_ind.
  intros *. rewrite pure_put_unfold.
  destruct t; simpl; intros;
    try case_decide; try case_match; try case_match;
    simplify_eq/=; try done.
  - ospecialize (IH n _); [lia|].
    repeat case_match; try done;
      (by eapply IH; [|done]).
  - ospecialize (IH n _); [lia|].
    repeat case_match; try done; (by eapply IH; [|done]).
Qed.

(* [pure_put] definitionally guarantees [limit] down the put path.
for [Inner] nodes down the opposite path, it preserves [limit]. *)
Lemma is_limit_over_put t t' label val :
  is_limit t →
  pure_put t label val = Some t' →
  is_limit t'.
Proof.
  autounfold with merkle.
  remember max_depth as limit. clear Heqlimit.
  remember 0%nat as depth. clear Heqdepth.
  revert t t' depth.
  induction limit as [? IH] using lt_wf_ind.
  intros *. rewrite pure_put_unfold.
  destruct t; simpl; intros;
    try case_decide; try case_match;
    simplify_eq/=; try done.
  - ospecialize (IH n _); [lia|].
    repeat case_match; try done;
      simplify_eq/=; intuition;
      by (eapply IH; [|done]).
  - ospecialize (IH n _); [lia|].
    repeat case_match; try done; naive_solver.
Qed.

Lemma is_sorted_over_put t t' label val :
  is_sorted t →
  pure_put t label val = Some t' →
  is_sorted t'.
Proof.
  autounfold with merkle.
  remember ([]) as pref.
  replace (0%nat) with (length pref) by (by subst).
  assert (prefix_total pref (bytes_to_bits label)).
  { subst. apply prefix_total_nil. }
  clear Heqpref.
  remember max_depth as limit. clear Heqlimit.
  generalize dependent pref.
  revert t t'.

  induction limit as [? IH] using lt_wf_ind.
  intros *. rewrite pure_put_unfold.
  destruct t; simpl; intros;
    try case_decide; try case_match;
    simplify_eq/=; try done.
  - ospecialize (IH n _); [lia|].
    replace (S _) with (length $ pref_ext pref label) in * by len.
    assert (prefix_total (pref_ext pref label) (bytes_to_bits label)).
    { by eapply prefix_total_snoc. }
    assert (prefix_total (pref_ext pref label0) (bytes_to_bits label0)).
    { by eapply prefix_total_snoc. }
    repeat case_match; try done;
      simplify_eq/=; intuition;
      by (eapply IH; last done).
  - ospecialize (IH n _); [lia|].
    replace (S _) with (length $ pref_ext pref label) in * by len.
    assert (prefix_total (pref_ext pref label) (bytes_to_bits label)).
    { by eapply prefix_total_snoc. }
    repeat case_match; try done;
      simplify_eq/=; intuition;
      by eapply IH.
Qed.

Tactic Notation "rw_get_bit" := repeat
  match goal with
  | H : bytes_to_bits _ !!! _ = _ |- _ => rewrite {}H
  end.

Lemma put_new_entry t t' label val :
  pure_put t label val = Some t' →
  is_entry t' label (Some val).
Proof.
  autounfold with merkle.
  remember max_depth as limit. clear Heqlimit.
  remember 0%nat as depth. clear Heqdepth.
  intros.
  eexists. intuition.
  generalize dependent depth.
  revert t t'.

  induction limit as [? IH] using lt_wf_ind.
  intros *. rewrite pure_put_unfold.
  destruct t; simpl; intros;
    try case_decide; try case_match;
    simplify_eq/=; try done.
  - ospecialize (IH n _); [lia|].
    repeat case_match; try done;
      simplify_eq/=; rw_get_bit; naive_solver.
  - ospecialize (IH n _); [lia|].
    repeat case_match; try done;
      simplify_eq/=; rw_get_bit; naive_solver.
Qed.

Lemma old_entry_over_put t t' label label' oval' val :
  is_entry t label' oval' →
  pure_put t label val = Some t' →
  label ≠ label' →
  is_entry t' label' oval'.
Proof.
  autounfold with merkle.
  remember max_depth as limit. clear Heqlimit.
  remember 0%nat as depth. clear Heqdepth.
  intros.
  generalize dependent depth.
  revert t t'.

  induction limit as [? IH] using lt_wf_ind.
  intros *. rewrite pure_put_unfold.
  destruct t; simpl; intros (?&?&?); intros;
    try case_decide; try case_match;
    simplify_eq/=.
  1-2: naive_solver.
  - ospecialize (IH n _); [lia|].
    repeat case_match; try done;
      simplify_eq/=; rw_get_bit;
      (* bit branch of old entry. *)
      try case_match; naive_solver.
  - ospecialize (IH n _); [lia|].
    repeat case_match; try done;
      simplify_eq/=; rw_get_bit; naive_solver.
Qed.

Definition cut_full_reln' ct ft lim h : iProp Σ :=
  "#Hct" ∷ is_cut_tree ct h ∗
  "#Hft" ∷ is_full_tree' ft h lim.
Definition cut_full_reln ct ft h := cut_full_reln' ct ft max_depth h.
Hint Unfold cut_full_reln : merkle.

Lemma cut_full_reln_Empty ft lim h :
  cut_full_reln' Empty ft lim h -∗ ⌜ft = Empty⌝.
Proof.
  iNamed 1.
  simpl. iNamedSuffix "Hct" "_ct".
  iEval (setoid_rewrite is_full_tree_unfold) in "Hft".
  iNamedSuffix "Hft" "_ft".
  iDestruct (cryptoffi.is_hash_inj with "His_hash_ft His_hash_ct") as %->.
  rewrite decode_empty_det. by iNamed "Hdecode_ft".
Qed.

Lemma cut_full_reln_Leaf {label val} ft lim h :
  cut_full_reln' (Leaf label val) ft lim h -∗ ⌜ft = Leaf label val⌝.
Proof.
  iNamed 1.
  simpl. iNamedSuffix "Hct" "_ct".
  iEval (setoid_rewrite is_full_tree_unfold) in "Hft".
  iNamedSuffix "Hft" "_ft".
  iDestruct (cryptoffi.is_hash_inj with "His_hash_ft His_hash_ct") as %->.
  rewrite decode_leaf_det; [|done..]. by iNamed "Hdecode_ft".
Qed.

Lemma cut_full_reln_Inner ft t0 t1 lim h :
  cut_full_reln' (Inner t0 t1) ft (S lim) h -∗
  (∃ t2 t3 h0 h1,
  ⌜ft = Inner t2 t3⌝ ∗
  is_cut_tree t0 h0 ∗
  is_cut_tree t1 h1 ∗
  is_full_tree' t2 h0 lim ∗
  is_full_tree' t3 h1 lim).
Proof.
  iNamed 1. simpl. iNamedSuffix "Hct" "_ct".
  iEval (setoid_rewrite is_full_tree_unfold) in "Hft".
  iNamedSuffix "Hft" "_ft".
  iDestruct (cryptoffi.is_hash_inj with "His_hash_ft His_hash_ct") as %->.
  iDestruct (is_cut_tree_len with "Hchild0_ct") as %?.
  iDestruct (is_cut_tree_len with "Hchild1_ct") as %?.
  rewrite decode_inner_det; [|done..]. iNamed "Hdecode_ft".
  iFrame "%#".
Qed.

Lemma init_to_reln_Empty lim :
  is_initialized -∗
  ∃ h, cut_full_reln' Empty Empty lim h.
Proof.
  rewrite /is_initialized. iNamed 1.
  rewrite /cut_full_reln'.
  iEval (setoid_rewrite is_full_tree_unfold).
  iFrame "#".
  by rewrite decode_empty_det.
Qed.

Lemma cut_to_full_Empty lim h :
  is_cut_tree Empty h -∗
  is_full_tree' Empty h lim.
Proof.
  simpl. iNamed 1.
  iEval (setoid_rewrite is_full_tree_unfold).
  iFrame "#".
  by rewrite decode_empty_det.
Qed.

Lemma cut_to_full_Leaf lim l v h :
  is_cut_tree (Leaf l v) h -∗
  is_full_tree' (Leaf l v) h lim.
Proof.
  simpl. iNamed 1.
  iEval (setoid_rewrite is_full_tree_unfold).
  iFrame "#".
  by rewrite decode_leaf_det.
Qed.

(* note: since put is pure, this lemma can't *give* post-put hash resources.
instead it requires them. *)
Lemma cut_full_over_put t0 t0' t1 t1' h0 h1 label val :
  (* to demonstrate Empty hash. *)
  is_initialized -∗
  cut_full_reln t0 t0' h0 -∗
  ⌜pure_put t0 label val = Some t1⌝ -∗
  cut_full_reln t1 t1' h1 -∗
  ⌜pure_put t0' label val = Some t1'⌝.
Proof.
  autounfold with merkle.
  remember max_depth as limit. clear Heqlimit.
  remember 0%nat as depth. clear Heqdepth.
  iIntros "#Hinit".
  iInduction limit as [? IH] using lt_wf_ind forall (t0 t0' t1 t1' h0 h1 depth).
  iNamedSuffix 1 "0". iIntros "%Hput". iNamedSuffix 1 "1".

  rewrite pure_put_unfold in Hput.
  destruct t0; try done.
  - (* get t0'. *)
    iDestruct (cut_full_reln_Empty t0' with "[$]") as %->.
    rewrite pure_put_unfold.
    simplify_eq/=.
    (* get t1'. *)
    by iDestruct (cut_full_reln_Leaf t1' with "[$]") as %->.

  - (* get t0'. *)
    iDestruct (cut_full_reln_Leaf t0' with "[$]") as %->.
    rewrite pure_put_unfold.
    simplify_eq/=. rewrite Hput.
    (* t1 casework, to get t1'. *)
    case_decide; try case_match; simplify_eq/=.
    { by iDestruct (cut_full_reln_Leaf t1' with "[$]") as %->. }
    iSpecialize ("IH" $! n with "[]"); [word|].
    case_match; try done.
    simplify_eq/=.
    iDestruct (cut_full_reln_Inner with "[$]") as
      "{Hct1 Hft1} (%&%&%&%&%& #Hchild0_ct1 & #Hchild1_ct1 & #Hchild0_ft1 & #Hchild1_ft1)".
    simplify_eq/=.

    (* t1=Inner case. very tricky. *)
    (* TODO: upstream. this doesn't support [occurrence] clauses like [in *]. *)
    Tactic Notation "ereplace0" open_constr(x) "with" open_constr(y) "in" constr(z) :=
      replace x with y in z.
    ereplace0
      (if get_bit label depth
        then if get_bit label0 depth then ?[a] else ?[b]
        else if get_bit label0 depth then ?b else ?a)
      with
      (if decide (get_bit label depth = get_bit label0 depth) then ?a else ?b) in H0.
    2: { by repeat case_match. }

    (* massage full tree children to look like cut tree children. *)
    iAssert (∃ t0', is_full_tree' (if get_bit label depth then
      if get_bit label0 depth then Empty else Leaf label0 val0 else t0') h2 n)%I as "[% Ht0]".
    { destruct (get_bit label _).
      2: { iFrame "#". }
      destruct (get_bit label0 depth).
      { by iDestruct (cut_to_full_Empty with "[$]") as "$". }
      { by iDestruct (cut_to_full_Leaf with "[$]") as "$". } }

    iAssert (∃ t1', is_full_tree' (if get_bit label depth then t1'
      else if get_bit label0 depth then Leaf label0 val0 else Empty) h3 n)%I as "[% Ht1]".
    { destruct (get_bit label _).
      { iFrame "#". }
      destruct (get_bit label0 depth).
      { by iDestruct (cut_to_full_Leaf with "[$]") as "$". }
      { by iDestruct (cut_to_full_Empty with "[$]") as "$". } }

    iDestruct (is_full_tree_inj with "Hchild0_ft1 Ht0") as %->.
    iDestruct (is_full_tree_inj with "Hchild1_ft1 Ht1") as %->.
    iClear "Ht0 Ht1".

    (* learn that t0 recursive put call gives massaged form. *)
    iDestruct (init_to_reln_Empty with "[$]") as "[% #Hreln_Empty]".
    iDestruct ("IH" $! _
      (if decide (get_bit label depth = get_bit label0 depth) then _ else _)
      _
      (if get_bit label depth then _ else _)
      (if decide (get_bit label depth = get_bit label0 depth) then _ else _)
      (* dep label, recur out is some child. *)
      (if get_bit label depth then h3 else h2)
      with "[][//][]") as "%".
    { case_decide.
      - iFrame "Hct0".
        iDestruct (cut_to_full_Leaf with "[$]") as "$".
      - iFrame "#". }
    { destruct (get_bit label _); iFrame "#". }

    iPureIntro. simplify_eq/=. by repeat case_match.

  - (* get t0'. *)
    case_match; try done.
    iSpecialize ("IH" $! n with "[]"); [word|].

    iDestruct (cut_full_reln_Inner with "[]") as
      "{Hct0 Hft0} (%&%&%&%&%& #Hchild0_ct0 & #Hchild1_ct0 & #Hchild0_ft0 & #Hchild1_ft0)".
    { iFrame "Hct0 #". }
    simpl in *. case_match; try done. simplify_eq/=.

    (* get t1'. *)
    iDestruct (cut_full_reln_Inner with "[]") as
      "{Hct1 Hft1} (%&%&%&%&%& #Hchild0_ct1 & #Hchild1_ct1 & #Hchild0_ft1 & #Hchild1_ft1)".
    { iFrame "Hct1 #". }
    simplify_eq/=.

    (* t0 / t1 (the final full tree children) aren't just the recur put out.
    they correspond to additional branching, as shown in the final cut trees.
    we need to make the branching structure evident. *)
    iAssert (∃ t0', is_full_tree'
      (if get_bit label depth then t2 else t0') h4 n)%I as "[% Ht0]".
    { destruct (get_bit label _).
      2: { iFrame "#". }
      iDestruct (is_cut_tree_det with "Hchild0_ct0 Hchild0_ct1") as %->.
      by iFrame "#". }
    iAssert (∃ t1', is_full_tree'
      (if get_bit label depth then t1' else t3) h5 n)%I as "[% Ht1]".
    { destruct (get_bit label _).
      { iFrame "#". }
      iDestruct (is_cut_tree_det with "Hchild1_ct0 Hchild1_ct1") as %->.
      by iFrame "#". }
    iDestruct (is_full_tree_inj with "Hchild0_ft1 Ht0") as %->.
    iDestruct (is_full_tree_inj with "Hchild1_ft1 Ht1") as %->.
    iClear "Ht0 Ht1".

    iDestruct ("IH" $! _
      (if get_bit label depth then _ else _)
      _
      (if get_bit label depth then _ else _)
      (if get_bit label depth then h3 else h2)
      (if get_bit label depth then h5 else h4)
      with "[][//][]") as "->".
    { case_match; iFrame "#". }
    { case_match; iFrame "#". }

    simplify_eq/=. iPureIntro. by case_match.
Qed.

(* easier [map_eq] extensional proof vs. using fin_map reductions. *)
Lemma to_map_over_put t t' label val :
  is_sorted t →
  pure_put t label val = Some t' →
  to_map t' = <[label:=val]>(to_map t).
Proof.
  intros. apply map_eq. intros.
  opose proof (is_sorted_over_put _ _ _ _ _ _); [done..|].
  destruct (decide (label = i)); subst; simpl_map.
  - apply entry_eq_lookup; [done|].
    by eapply put_new_entry.
  - rewrite -entry_eq_lookup; [|done].
    eapply old_entry_over_put; [|done..].
    by apply entry_eq_lookup.
Qed.

Fixpoint is_const_label_len t :=
  match t with
  | Leaf label val => Z.of_nat (length label) = cryptoffi.hash_len
  | Inner c0 c1 => is_const_label_len c0 ∧ is_const_label_len c1
  | _ => True
  end.

Tactic Notation "rw_pure_put" := repeat
  match goal with
  | H : pure_put' _ _ _ _ _ = None |- _ => rewrite -{}H
  end.

Lemma put_Some t label val :
  (* for max depth. *)
  is_limit t →
  Z.of_nat (length label) = cryptoffi.hash_len →
  is_const_label_len t →
  is_sorted t →
  (* for no Cut. *)
  is_cutless_path t label →
  is_Some (pure_put t label val).
Proof.
  autounfold with merkle.
  assert (∃ x, x = max_depth) as [limit Heq]; [by eexists|].
  rewrite -[in is_limit' _ _]Heq.
  rewrite -[in pure_put' _ _ _ _ _]Heq.
  remember [] as pref.
  assert (prefix_total pref (bytes_to_bits label)).
  { subst. apply prefix_total_nil. }
  replace 0%nat with (length pref); [|by subst].
  assert (length pref + limit = max_depth)%nat.
  { subst. simpl. lia. }
  clear Heq Heqpref.
  intros.
  generalize dependent t.
  generalize dependent pref.

  induction limit as [? IH] using lt_wf_ind.
  intros. rewrite pure_put_unfold.
  destruct t; simpl in *; try done.

  - case_decide; [done|].
    destruct limit.
    (* limit=0. show labels actually equal. *)
    { opose proof (prefix_total_full _ (bytes_to_bits label) _ _);
        [|done|]; [by len|].
      opose proof (prefix_total_full _ (bytes_to_bits label0) _ _);
        [|done|]; [by len|].
      simplify_eq/=. }

    ospecialize (IH limit _); [lia|].
    destruct (pure_put' _ _ _ _ _) eqn:?; [done|]. rw_pure_put.
    replace (S _) with (length $ pref_ext pref label) in * by len.
    eapply IH; repeat case_match; try done; [|len|..];
      by eapply prefix_total_snoc.
  - destruct limit; [done|].
    ospecialize (IH limit _); [lia|].
    intuition.
    destruct (pure_put' _ _ _ _ _) eqn:?; [done|]. rw_pure_put.
    replace (S _) with (length $ pref_ext pref label) in * by len.
    eapply IH; repeat case_match; try done; [..|len|len];
      by eapply prefix_total_snoc.
Qed.

(** invariants on [pure_newShell]. *)

Lemma limit_on_newShell label sibs :
  length sibs ≤ max_depth →
  is_limit (pure_newShell label sibs).
Proof.
  autounfold with merkle.
  remember max_depth as limit.
  remember 0%nat as depth.
  assert (depth + limit ≤ max_depth) by lia.
  clear Heqlimit Heqdepth.
  generalize dependent depth.
  revert limit.
  induction sibs; try done.
  simpl. intros.
  destruct limit; try done.
  opose proof (IHsibs limit (S depth) _ _); [lia..|].
  by case_match.
Qed.

Lemma const_label_on_newShell label sibs :
  is_const_label_len (pure_newShell label sibs).
Proof.
  autounfold with merkle.
  remember 0%nat as depth. clear Heqdepth.
  revert depth.
  induction sibs; try done.
  simpl. intros.
  by case_match.
Qed.

Lemma sorted_on_newShell label sibs :
  is_sorted (pure_newShell label sibs).
Proof.
  autounfold with merkle.
  remember [] as pref.
  replace 0%nat with (length pref) by (by subst).
  clear Heqpref.
  revert pref.
  induction sibs; try done.
  simpl. intros.
  opose proof (IHsibs (pref ++ [if get_bit label (length pref) then true else false])).
  replace (length (_ ++ _)) with (S (length pref)) in * by len.
  by case_match.
Qed.

Lemma cutless_on_newShell label sibs :
  is_cutless_path (pure_newShell label sibs) label.
Proof.
  autounfold with merkle.
  remember 0%nat as depth. clear Heqdepth.
  revert depth.
  induction sibs; try done.
  simpl. intros.
  by case_match.
Qed.

Lemma newShell_None label sibs :
  is_entry (pure_newShell label sibs) label None.
Proof.
  exists None. split; [|done].
  autounfold with merkle.
  remember 0%nat as depth. clear Heqdepth.
  revert depth.
  induction sibs; try done.
  simpl. intros.
  by case_match.
Qed.

(** invariants on [pure_proofToTree]. *)

#[local] Opaque pure_put.

Lemma proofToTree_None label sibs oleaf t :
  match oleaf with None => True | Some (l, _) => label ≠ l end →
  pure_proofToTree label sibs oleaf = Some t →
  is_entry t label None.
Proof.
  intros.
  opose proof (newShell_None label sibs).
  destruct oleaf as [[]|]; simpl in *.
  - by eapply old_entry_over_put.
  - by simplify_eq/=.
  (* [Opaque pure_put], otherwise long Qed. *)
Qed.

(** tree proofs. *)

Fixpoint is_sibs' (t : tree) (depth : nat) (label : list w8)
    (sibs : list $ list w8) : iProp Σ :=
  match t with
  | Empty =>
    "%Heq_sibs" ∷ ⌜ sibs = [] ⌝
  | Leaf _ _ =>
    "%Heq_sibs" ∷ ⌜ sibs = [] ⌝
  | Inner child0 child1 =>
    let c_recur := if get_bit label depth then child1 else child0 in
    let c_sib := if get_bit label depth then child0 else child1 in
    ∃ sib sibs',
    "%Heq_sibs" ∷ ⌜ sibs = sib :: sibs' ⌝ ∗
    "#Hrecur" ∷ is_sibs' c_recur (S depth) label sibs' ∗
    "#Hcut_tree" ∷ is_cut_tree c_sib sib
  | Cut _ => False
  end.
Definition is_sibs t label sibs := is_sibs' t 0 label sibs.
Hint Unfold is_sibs : merkle.

#[global] Instance is_sibs_pers t d l s : Persistent (is_sibs' t d l s).
Proof.
  revert d s. induction t; try apply _.
  simpl. intros. case_match; apply _.
Qed.

(*
Definition is_proof (label: list w8)
    (found: option ((list w8) * (list w8)%type)) (proof: list w8)
    (h: list w8) : iProp Σ :=
  ∃ t,
  "#Hhash" ∷ is_cut_tree t h ∗
  "#Hproof" ∷ tree_sibs_proof t label (W64 0) proof ∗
  "%Hpath" ∷ ⌜ tree_path t label (W64 0) found ⌝.

Lemma is_proof_to_is_found label found proof h:
  is_proof label found proof h -∗
  is_found label found h.
Proof. iNamed 1. iFrame "#%". Qed.

Lemma tree_sibs_proof_len t label depth proof :
  tree_sibs_proof t label depth proof -∗
  ⌜ Z.of_nat (length proof) `mod` cryptoffi.hash_len = 0 ⌝.
Proof.
  iInduction t as [| ? | ? IH0 ? IH1 | ?] forall (depth proof);
    simpl; iNamed 1; subst; simpl; [word..|idtac|done].
  rewrite length_app. case_match; iNamed "Hrecur";
    iDestruct (is_cut_tree_len with "Hcut_tree") as %?.
  - iDestruct ("IH1" with "Hrecur_proof") as %?. word.
  - iDestruct ("IH0" with "Hrecur_proof") as %?. word.
Qed.

Lemma is_proof_eq_dig label found proof hash0 hash1 :
  is_proof label found proof hash0 -∗
  is_proof label found proof hash1 -∗
  ⌜ hash0 = hash1 ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iRevert "Hhash0 Hproof0 Hhash1 Hproof1".
  remember (W64 0) as depth. clear Heqdepth.
  iInduction t as [| ? | ? IH0 ? IH1 | ?]
    forall (depth t0 hash0 hash1 proof Hpath0 Hpath1);
    destruct t0; try done;
    simpl in *; iIntros "#H0 #H1 #H2 #H3";
    iNamedSuffix "H0" "0"; iNamedSuffix "H1" "0";
    iNamedSuffix "H2" "1"; iNamedSuffix "H3" "1".

  - by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %?.
  - naive_solver.
  - apply (f_equal length) in Heq_proof1.
    rewrite length_app in Heq_proof1.
    case_match; iNamed "Hrecur1";
      iDestruct (is_cut_tree_len with "Hcut_tree") as %?;
      list_simplifier; word.
  - naive_solver.
  - simplify_eq/=.
    by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %?.
  - apply (f_equal length) in Heq_proof1.
    rewrite length_app in Heq_proof1.
    case_match; iNamed "Hrecur1";
      iDestruct (is_cut_tree_len with "Hcut_tree") as %?;
      list_simplifier; word.
  - apply (f_equal length) in Heq_proof0.
    rewrite length_app in Heq_proof0.
    case_match; iNamed "Hrecur0";
      iDestruct (is_cut_tree_len with "Hcut_tree") as %?;
      list_simplifier; word.
  - apply (f_equal length) in Heq_proof0.
    rewrite length_app in Heq_proof0.
    case_match; iNamed "Hrecur0";
      iDestruct (is_cut_tree_len with "Hcut_tree") as %?;
      list_simplifier; word.
  - case_match;
      iNamedSuffix "Hrecur0" "0"; iNamedSuffix "Hrecur1" "1".
    + (* equal sib hashes. *)
      iDestruct (is_cut_tree_len with "Hcut_tree0") as %?.
      iDestruct (is_cut_tree_len with "Hcut_tree1") as %?.
      subst. apply app_inj_2 in Heq_proof1 as [-> ->]; [|lia].
      iDestruct (is_cut_tree_det with "Hleft_hash0 Hcut_tree0") as %->.
      iDestruct (is_cut_tree_det with "Hleft_hash1 Hcut_tree1") as %->.
      (* equal child hashes. *)
      iDestruct ("IH1" with "[] [] Hright_hash0 Hrecur_proof0
        Hright_hash1 Hrecur_proof1") as %->; [done..|].
      by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %->.
    + (* equal sib hashes. *)
      iDestruct (is_cut_tree_len with "Hcut_tree0") as %?.
      iDestruct (is_cut_tree_len with "Hcut_tree1") as %?.
      subst. apply app_inj_2 in Heq_proof1 as [-> ->]; [|lia].
      iDestruct (is_cut_tree_det with "Hright_hash0 Hcut_tree0") as %->.
      iDestruct (is_cut_tree_det with "Hright_hash1 Hcut_tree1") as %->.
      (* equal child hashes. *)
      iDestruct ("IH0" with "[] [] Hleft_hash0 Hrecur_proof0
        Hleft_hash1 Hrecur_proof1") as %->; [done..|].
      by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %->.
Qed.
*)

(** stuff that might need to be resurrected. *)

(*
(** code predicates. *)

Fixpoint minimal_tree t : Prop :=
  match t with
  | Inner child0 child1 =>
    minimal_tree child0 ∧
    minimal_tree child1 ∧
    size (tree_to_map t) > 1
    (* alternate rules for (child0, child1):
    disallow: (Empty, Empty); (Empty, Leaf).
    allow: (Empty, Inner); (Leaf, Leaf); (Leaf, Inner); (Inner, Inner). *)
  | _ => True
  end.

(** misc. *)

Lemma tree_to_map_det {t0 t1 depth} :
  tree_to_map t0 = tree_to_map t1 →
  sorted_tree t0 depth →
  sorted_tree t1 depth →
  is_cutless t0 →
  is_cutless t1 →
  minimal_tree t0 →
  minimal_tree t1 →
  t0 = t1.
Proof.
  revert t1 depth.
  induction t0 as [| ? | ? IH0 ? IH1 | ?];
    destruct t1; intros; try done; simpl in *.
  - apply (f_equal size) in H. rewrite map_size_empty in H. lia.
  - naive_solver.
  - apply (f_equal size) in H. rewrite map_size_singleton in H. lia.
  - apply (f_equal size) in H. rewrite map_size_empty in H. lia.
  - apply (f_equal size) in H. rewrite map_size_singleton in H. lia.
  - intuition.
    opose proof (tree_to_map_inner_eq _ _ _); [done..|intuition].
    opose proof (IH0 t1_1 _ _ _ _ _ _) as ->; try done.
    opose proof (IH1 t1_2 _ _ _ _ _ _) as ->; try done.
Qed.

Lemma is_map_det m dig0 dig1 :
  is_map m dig0 -∗
  is_map m dig1 -∗
  ⌜ dig0 = dig1 ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1". subst.
  opose proof (tree_to_map_det _ _ _ _ _ _ _) as ->; [done..|].
  by iDestruct (is_cut_tree_det with "Hcut_tree0 Hcut_tree1") as %?.
Qed.

Definition is_found (label: list w8)
    (found: option ((list w8) * (list w8))%type) (h: list w8) : iProp Σ :=
  ∃ t,
  "%Htree_path" ∷ ⌜ tree_path t label 0 found ⌝ ∗
  "#Hcut_tree" ∷ is_cut_tree t h.

Lemma tree_path_agree label depth found0 found1 h t0 t1:
  tree_path t0 label depth found0 →
  tree_path t1 label depth found1 →
  is_cut_tree t0 h -∗
  is_cut_tree t1 h -∗
  ⌜ found0 = found1 ⌝.
Proof.
  iInduction t0 as [| ? | ? IH0 ? IH1 | ?] forall (depth t1 h);
    destruct t1; simpl; iIntros "*"; try done;
    iNamedSuffix 1 "0";
    iNamedSuffix 1 "1";
    iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %?;
    try naive_solver.

  (* both leaves. use leaf encoding. *)
  - iPureIntro. list_simplifier.
    apply app_inj_1 in H as [Heq_len_label H]; [|len].
    apply (inj u64_le) in Heq_len_label.
    assert (length label0 = length label1) as ?.
    { rewrite Heq_len_label in Hinb_label0. word. }
    list_simplifier.
    apply app_inj_1 in H1; [naive_solver|].
    len.
  (* both inner. use inner encoding and next_pos same to get
  the same next_hash. then apply IH. *)
  - iDestruct (is_cut_tree_len with "Hleft_hash0") as %?.
    iDestruct (is_cut_tree_len with "Hleft_hash1") as %?.
    list_simplifier. apply app_inj_1 in H as [-> ->]; [|lia].
    case_match.
    + by iApply "IH1".
    + by iApply "IH0".
Qed.

Lemma is_found_agree label found0 found1 h:
  is_found label found0 h -∗
  is_found label found1 h -∗
  ⌜found0 = found1⌝.
Proof.
  iIntros "H0 H1".
  iDestruct "H0" as (?) "[% H0]".
  iDestruct "H1" as (?) "[% H1]".
  iApply (tree_path_agree with "H0 H1"); eauto.
Qed.
*)

End proof.

Hint Unfold find is_entry is_sorted is_full_tree is_map is_cutless_path
  is_limit cut_full_reln pure_put pure_newShell is_sibs : merkle.
