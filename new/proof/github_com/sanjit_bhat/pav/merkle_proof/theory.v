From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.proof Require Import proof_prelude.
From Perennial.Helpers Require Import bytes NamedProps.

From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi.

From New.proof.github_com.sanjit_bhat.pav.merkle_proof Require Import base.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.

Definition bytes_to_bits l := concat (byte_to_bits <$> l).

(* get_bit returns false if bit n of l is 0 (or the bit is past the length of l). *)
Definition get_bit l (n : w64) : bool :=
  match bytes_to_bits l !! (uint.nat n) with
  | None => false
  | Some bit => bit
  end.

(** tree defn. *)

(* [Cut]s denote a cut off tree.
1) for full trees, they come from invalid hashes. e.g.,
  - bytes that didn't come from the hash fn output.
  - a hash whose preimg isn't a valid node encoding.
  - running out of limit.
2) for partial trees, it's just an unknown-origin hash.

a different approach to invalid full trees bubbles invalidness all the way to the top.
that has the undesirable effect of an invalid inversion "stopping the proof". *)
Inductive tree :=
  | Empty
  | Leaf (label val : list w8)
  | Inner (child0 child1 : tree)
  | Cut (hash : list w8).

(** full trees. *)

Inductive dec_node :=
  | DecEmpty
  | DecLeaf (label val : list w8)
  | DecInner (hash0 hash1 : list w8) :
    Z.of_nat (length hash0) = cryptoffi.hash_len →
    Z.of_nat (length hash1) = cryptoffi.hash_len →
    dec_node
  | DecInvalid.

Local Definition decode_leaf (data : list w8) : option (list w8 * list w8) :=
  let rem0 := data in
  match bool_decide (length rem0 >= 8%nat) with
  | false => None
  | _ =>
    let label_len := uint.nat (le_to_u64 (take 8%nat rem0)) in
    let rem1 := drop 8%nat rem0 in
    match bool_decide (length rem1 >= label_len) with
    | false => None
    | _ =>
      let label := take label_len rem1 in
      let rem2 := drop label_len rem1 in
      match bool_decide (length rem2 >= 8%nat) with
      | false => None
      | _ =>
        let val_len := uint.nat (le_to_u64 (take 8%nat rem2)) in
        let rem3 := drop 8%nat rem2 in
        match bool_decide (length rem3 >= val_len) with
        | false => None
        | _ =>
          let val := take val_len rem3 in
          let rem4 := drop val_len rem3 in
          match bool_decide (rem4 = []) with
          | false => None
          | _ => Some (label, val)
          end
        end
      end
    end
  end.

(* [decode_node] lets us compute one dec_node of a tree inversion. *)
Local Program Definition decode_node (data : option $ list w8) : dec_node :=
  match data with
  | None => DecInvalid
  | Some d =>
    match d with
    | [] => DecInvalid
    | tag :: d' =>
      if decide (tag = emptyNodeTag ∧ d' = [])
      then DecEmpty
      else if decide (tag = leafNodeTag)
      then
        match decode_leaf d' with
        | None => DecInvalid
        | Some x => DecLeaf x.1 x.2
        end
      else if decide (tag = innerNodeTag ∧ Z.of_nat (length d') = 2 * cryptoffi.hash_len)
      then
        DecInner
          (take (Z.to_nat cryptoffi.hash_len) d')
          (drop (Z.to_nat cryptoffi.hash_len) d')
          _ _
      else DecInvalid
    end
  end.
Next Obligation. intros. rewrite length_take. lia. Qed.
Next Obligation. intros. rewrite length_drop. lia. Qed.

Lemma decode_empty_inj d :
  decode_node d = DecEmpty →
  d = Some [emptyNodeTag].
Proof.
  rewrite /decode_node. intros.
  case_match; [|done].
  case_match; [done|].
  case_decide; [naive_solver|].
  case_decide; [by case_match|].
  by case_decide.
Qed.

Local Lemma decode_leaf_inj_aux d l v :
  decode_leaf d = Some (l, v) →
  d = u64_le (W64 (length l)) ++ l ++ u64_le (W64 (length v)) ++ v.
Proof.
  rewrite /decode_leaf. intros.
  case_bool_decide; [|done].
  case_bool_decide; [|done].
  case_bool_decide; [|done].
  case_bool_decide; [|done].
  case_bool_decide; [|done].
  simplify_eq/=.
  remember d as rem0.

  rewrite -{1}(take_drop 8 rem0).
  rewrite -{1}(take_drop 8 (_ ++ _ ++ _ ++ _)).
  f_equal.
  { rewrite take_app_length'; [|len].
    rewrite length_take_le; [|lia].
    rewrite w64_to_nat_id.
    rewrite le_to_u64_le; [done|].
    rewrite length_take. lia. }
  remember (uint.nat (le_to_u64 (take 8 rem0))) as labelLen.
  remember (drop 8 rem0) as rem1.

  rewrite drop_app_length'; [|len].
  rewrite -{1}(take_drop labelLen rem1).
  f_equal.
  remember (drop labelLen rem1) as rem2.

  rewrite -{1}(take_drop 8 rem2).
  rewrite -{1}(take_drop 8 (_ ++ _)).
  f_equal.
  { rewrite take_app_length'; [|len].
    rewrite length_take_le; [|lia].
    rewrite w64_to_nat_id.
    rewrite le_to_u64_le; [done|].
    rewrite length_take. lia. }
  remember (uint.nat (le_to_u64 (take 8 rem2))) as valLen.
  remember (drop 8 rem2) as rem3.

  rewrite drop_app_length'; [|len].
  rewrite -{1}(take_drop valLen rem3).
  rewrite H4.
  by list_simplifier.
Qed.

Lemma decode_leaf_inj d l v :
  decode_node d = DecLeaf l v →
  d =
  Some $
    leafNodeTag ::
    u64_le (W64 (length l)) ++ l ++
    u64_le (W64 (length v)) ++ v.
Proof.
  rewrite /decode_node. intros.
  case_match; [|done].
  case_match; [done|].
  case_decide; [naive_solver|].
  case_decide. 2: { by case_decide. }
  case_match; [|done].
  destruct p. simplify_eq/=.
  opose proof (decode_leaf_inj_aux _ _ _ _) as Heq; [done|].
  by rewrite Heq.
Qed.

Lemma decode_inner_inj d h0 h1 {Hlen0 Hlen1} :
  decode_node d = DecInner h0 h1 Hlen0 Hlen1 →
  d = Some $ innerNodeTag :: h0 ++ h1.
Proof.
  rewrite /decode_node. intros.
  case_match; [|done].
  case_match; [done|].
  case_decide; [naive_solver|].
  case_decide. { by case_match. }
  case_decide; [|done].
  destruct_and!.
  simplify_eq/=.
  by rewrite take_drop.
Qed.

(* for every node, there's only one data that decodes to it. *)
Lemma decode_node_inj n d0 d1 :
  n = decode_node d0 →
  n = decode_node d1 →
  n ≠ DecInvalid →
  d0 = d1 ∧ is_Some d1.
Proof.
  intros. destruct n; try done.
  - opose proof (decode_empty_inj d0 _) as ->; [done|].
    by opose proof (decode_empty_inj d1 _) as ->.
  - opose proof (decode_leaf_inj d0 _ _ _) as ->; [done|].
    by opose proof (decode_leaf_inj d1 _ _ _) as ->.
  - opose proof (decode_inner_inj d0 _ _ _) as ->; [done|].
    by opose proof (decode_inner_inj d1 _ _ _) as ->.
Qed.

(* the overall structure of [is_full_tree] is a bit unconventional.
from the hash [h], it recursively computes (via [decode_node]) the tree [t].
a few consequences:
- it "resolves" the tree to the maximum extent possible.
- it limits invalid nodes only to when they're generated by decoding.
this allows proving [is_full_tree_inj].

[limit] prevents infinite recursion. *)
Fixpoint is_full_tree (t : tree) (h : list w8) (limit : nat) : iProp Σ :=
  ∃ d,
  "#His_hash" ∷ cryptoffi.is_hash d h ∗
  "#Hdecode" ∷ match decode_node d with
  | DecEmpty =>
    "%" ∷ ⌜ t = Empty ⌝
  | DecLeaf l v =>
    "%" ∷ ⌜ t = Leaf l v ⌝
  | DecInvalid =>
    "%" ∷ ⌜ t = Cut h ⌝
  | DecInner h0 h1 _ _ =>
    match limit with
    | 0%nat =>
      "%" ∷ ⌜ t = Cut h ⌝
    | S limit' =>
      ∃ t0 t1,
      "#Hrecur0" ∷ is_full_tree t0 h0 limit' ∗
      "#Hrecur1" ∷ is_full_tree t1 h1 limit' ∗
      "%" ∷ ⌜ t = Inner t0 t1 ⌝
    end
  end.

#[global] Instance is_full_tree_pers t h l : Persistent (is_full_tree t h l).
Proof.
  revert t h. induction l.
  - intros. apply exist_persistent. intros.
    case_match; apply _.
  - intros. apply exist_persistent. intros.
    case_match; apply _.
Qed.

Lemma is_full_tree_invert h limit :
  Z.of_nat (length h) = cryptoffi.hash_len → ⊢
  ∃ t, is_full_tree t h limit.
Proof.
  revert h. induction limit; intros.
  - iDestruct (cryptoffi.is_hash_invert h) as "[% $]"; [done|].
    destruct (decode_node data); try naive_solver.
  - iDestruct (cryptoffi.is_hash_invert h) as "[% $]"; [done|].
    destruct (decode_node data); try naive_solver.
    fold is_full_tree.
    iDestruct (IHlimit hash0) as "[% $]"; [done|].
    iDestruct (IHlimit hash1) as "[% $]"; [done|].
    naive_solver.
Qed.

Local Lemma DecInner_eq_pi h0 h1 H0 H1 H2 H3 :
  DecInner h0 h1 H0 H1 = DecInner h0 h1 H2 H3.
Proof. f_equal; apply proof_irrel. Qed.

(* if [Cut], carries the hash, so hashes must be equal.
otherwise, [decode_node_inj] says that Some preimg's are equal,
which implies the hashes are equal. *)
Lemma is_full_tree_det t h0 h1 limit0 limit1 :
  is_full_tree t h0 limit0 -∗
  is_full_tree t h1 limit1 -∗
  ⌜ h0 = h1 ⌝.
Proof.
  iInduction (limit0) as [] forall (t h0 h1 limit1); destruct limit1; simpl;
    iNamedSuffix 1 "0"; iNamedSuffix 1 "1";
    do 2 case_match;
    iNamedSuffix "Hdecode0" "0"; iNamedSuffix "Hdecode1" "1";
    simplify_eq/=; try done.
  1-8: (
    opose proof (decode_node_inj _ d d0 _ _ _) as (-> & [? ->]); [done..|];
    by iApply cryptoffi.is_hash_det
  ).
  iDestruct ("IHlimit0" with "Hrecur00 Hrecur01") as %->.
  iDestruct ("IHlimit0" with "Hrecur10 Hrecur11") as %->.
  rewrite -(DecInner_eq_pi _ _ e1 e2) in H.
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
  is_full_tree t0 h limit -∗
  is_full_tree t1 h limit -∗
  ⌜ t0 = t1 ⌝.
Proof.
  iInduction (limit) as [] forall (t0 t1 h); simpl;
    iNamedSuffix 1 "0"; iNamedSuffix 1 "1";
    iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %->;
    case_match;
    iNamedSuffix "Hdecode0" "0"; iNamedSuffix "Hdecode1" "1";
    simplify_eq/=; try done.
  iDestruct ("IHlimit" with "Hrecur00 Hrecur01") as %->.
  by iDestruct ("IHlimit" with "Hrecur10 Hrecur11") as %->.
Qed.

(** cut trees. *)
(* TODO: shorten these now that they're all module namespaced. *)
(* TODO: make bunch of these Local and Opaque. *)

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
    "%Hinb_label" ∷ ⌜ uint.Z (W64 (length label)) = length label ⌝ ∗
    "#His_hash" ∷
      cryptoffi.is_hash (Some $ [leafNodeTag] ++
        (u64_le $ length label) ++ label ++
        (u64_le $ length val) ++ val) h
  | Inner child0 child1 =>
    ∃ hl hr,
    "#Hleft_hash" ∷ is_cut_tree child0 hl ∗
    "#Hright_hash" ∷ is_cut_tree child1 hr ∗
    "#His_hash" ∷ cryptoffi.is_hash (Some $ [innerNodeTag] ++ hl ++ hr) h
  | Cut ch =>
    "%Heq_cut" ∷ ⌜ h = ch ⌝ ∗
    "%Hlen_hash" ∷ ⌜ Z.of_nat $ length h = cryptoffi.hash_len ⌝
  end.

#[global]
Instance is_cut_tree_persistent t h : Persistent (is_cut_tree t h).
Proof. revert h. induction t; apply _. Qed.

(* TODO: could potentially prove:
- every full tree is a cut tree.
- cutless cut trees are full trees.
- a terminating (non-cut) path down cut tree has the same path down the full tree. *)

Fixpoint tree_to_map t : gmap (list w8) (list w8) :=
  match t with
  | Empty => ∅
  | Leaf label val => {[label := val]}
  | Inner child0 child1 => (tree_to_map child0) ∪ (tree_to_map child1)
  | Cut h => ∅
  end.

Definition tree_labels_have_bit t n val : Prop :=
  ∀ l,
  l ∈ dom (tree_to_map t) →
  get_bit l n = val.

Fixpoint sorted_tree t depth : Prop :=
  match t with
  | Inner child0 child1 =>
    sorted_tree child0 (word.add depth (W64 1)) ∧
    tree_labels_have_bit child0 depth false ∧
    sorted_tree child1 (word.add depth (W64 1)) ∧
    tree_labels_have_bit child1 depth true
  | _ => True
  end.

Fixpoint cutless_path t (label : list w8) (depth : w64) : Prop :=
  match t with
  | Cut _ => False
  | Inner child0 child1 =>
    match get_bit label depth with
    | false => cutless_path child0 label (word.add depth (W64 1))
    | true  => cutless_path child1 label (word.add depth (W64 1))
    end
  | _ => True
  end.

Fixpoint cutless_tree t : Prop :=
  match t with
  | Inner child0 child1 => cutless_tree child0 ∧ cutless_tree child1
  | Cut _ => False
  | _ => True
  end.

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

(* [is_map] is when we talk about the underlying tree map.
this requires no cuts in the tree, since cuts could result in
different maps for the same tree hash. *)
Definition is_map (m: gmap (list w8) (list w8)) (h: list w8) : iProp Σ :=
  ∃ t,
  "%Heq_tree_map" ∷ ⌜ m = tree_to_map t ⌝ ∗
  "%Hsorted" ∷ ⌜ sorted_tree t 0 ⌝ ∗
  "%Hcutless" ∷ ⌜ cutless_tree t ⌝ ∗
  "%Hminimal" ∷ ⌜ minimal_tree t ⌝ ∗
  "#Hcut_tree" ∷ is_cut_tree t h.

Global Instance is_map_pers m h : Persistent (is_map m h) := _.

Fixpoint tree_path (t: tree) (label: list w8) (depth: w64)
    (result: option (list w8 * list w8)%type) : Prop :=
  match t with
  | Empty =>
    result = None
  | Leaf found_label found_val =>
    result = Some (found_label, found_val)
  | Inner child0 child1 =>
    match get_bit label depth with
    | false => tree_path child0 label (word.add depth (W64 1)) result
    | true  => tree_path child1 label (word.add depth (W64 1)) result
    end
  | Cut _ => False
  end.

Definition is_found (label: list w8)
    (found: option ((list w8) * (list w8))%type) (h: list w8) : iProp Σ :=
  ∃ t,
  "%Htree_path" ∷ ⌜ tree_path t label 0 found ⌝ ∗
  "#Hcut_tree" ∷ is_cut_tree t h.

Definition found_nonmemb (label: list w8)
    (found: option ((list w8) * (list w8))%type) :=
  match found with
  | None => True
  | Some (found_label, _) => label ≠ found_label
  end.

(* is_entry represents memb and nonmemb proofs
as Some and None option vals, providing a unified way of expressing them
that directly corresponds to a map entry. *)
Definition is_entry (label : list w8) (val : option $ list w8)
    (dig : list w8) : iProp Σ :=
  match val with
  | Some v =>
    "#Hfound" ∷ is_found label (Some (label, v)) dig
  | None =>
    ∃ found,
    "#Hfound" ∷ is_found label found dig ∗
    "%Hnonmemb" ∷ ⌜ found_nonmemb label found ⌝
  end.

Global Instance is_entry_pers l v d : Persistent (is_entry l v d) := _.

Fixpoint tree_sibs_proof (t: tree) (label: list w8) (depth : w64)
    (proof: list w8) : iProp Σ :=
  match t with
  | Empty =>
    "%Heq_proof" ∷ ⌜proof = []⌝
  | Leaf found_label found_val =>
    "%Heq_proof" ∷ ⌜proof = []⌝
  | Inner child0 child1 =>
    ∃ sibhash proof',
    "%Heq_proof" ∷ ⌜proof = proof' ++ sibhash ⌝ ∗
    "Hrecur" ∷
      match get_bit label depth with
      | false =>
        "Hrecur_proof" ∷ tree_sibs_proof child0 label (word.add depth (W64 1)) proof' ∗
        "#Hcut_tree" ∷ is_cut_tree child1 sibhash
      | true =>
        "Hrecur_proof" ∷ tree_sibs_proof child1 label (word.add depth (W64 1)) proof' ∗
        "#Hcut_tree" ∷ is_cut_tree child0 sibhash
      end
  | Cut _ => False
  end.

#[global]
Instance tree_sibs_proof_persistent t l d p : Persistent (tree_sibs_proof t l d p).
Proof.
  revert d p. induction t; try apply _.
  simpl. intros. case_match; apply _.
Qed.

Definition is_proof (label: list w8)
    (found: option ((list w8) * (list w8)%type)) (proof: list w8)
    (h: list w8) : iProp Σ :=
  ∃ t,
  "#Hhash" ∷ is_cut_tree t h ∗
  "#Hproof" ∷ tree_sibs_proof t label (W64 0) proof ∗
  "%Hpath" ∷ ⌜ tree_path t label (W64 0) found ⌝.

(** Derived facts about [is_cut_tree]. *)

Lemma cutless_tree_impl_paths t :
  cutless_tree t →
  ∀ l d, cutless_path t l d.
Proof.
  induction t; intros Hc ??; try done.
  simpl in *. destruct Hc.
  case_match; intuition.
Qed.

Lemma is_cut_tree_len t h:
  is_cut_tree t h -∗
  ⌜ Z.of_nat $ length h = cryptoffi.hash_len ⌝.
Proof. destruct t; iNamed 1; [..|done]; by iApply cryptoffi.is_hash_len. Qed.

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

Lemma tree_labels_have_bit_disjoint t0 t1 depth :
  tree_labels_have_bit t0 depth true →
  tree_labels_have_bit t1 depth false →
  dom (tree_to_map t0) ## dom (tree_to_map t1).
Proof.
  intros.
  apply elem_of_disjoint; intros.
  apply H in H1.
  apply H0 in H2.
  congruence.
Qed.

Lemma tree_to_map_lookup_None label depth bit t:
  get_bit label depth = (negb bit) →
  tree_labels_have_bit t depth bit →
  tree_to_map t !! label = None.
Proof.
  intros.
  destruct (tree_to_map t !! label) eqn:He; eauto.
  assert (get_bit label depth = bit).
  { apply H0. apply elem_of_dom; eauto. }
  rewrite H1 in H. destruct bit; simpl in *; congruence.
Qed.

Lemma tree_to_map_Some t label depth val:
  tree_to_map t !! label = Some val →
  sorted_tree t depth →
  tree_path t label depth (Some (label, val)).
Proof.
  revert depth.
  induction t; simpl; intros.
  - rewrite lookup_empty in H. congruence.
  - apply lookup_singleton_Some in H. intuition congruence.
  - intuition.
    eapply tree_labels_have_bit_disjoint in H4 as Hd; eauto.
    apply lookup_union_Some in H.
    2: apply map_disjoint_dom_2; eauto.
    destruct (get_bit label depth) eqn:Hbit.
    + eapply tree_to_map_lookup_None in H0; eauto. destruct H; try congruence.
      eapply IHt2; eauto.
    + eapply tree_to_map_lookup_None in H4; eauto. destruct H; try congruence.
      eapply IHt1; eauto.
  - rewrite lookup_empty in H. congruence.
Qed.

Lemma tree_to_map_None t label depth:
  tree_to_map t !! label = None →
  sorted_tree t depth →
  cutless_path t label depth →
  ∃ found,
    tree_path t label depth found ∧
    found_nonmemb label found.
Proof.
  revert depth.
  induction t; simpl; intros; [..|done].
  - rewrite lookup_empty in H. eexists; eauto.
  - apply lookup_singleton_None in H. eexists. split; eauto. simpl; congruence.
  - apply lookup_union_None in H. intuition.
    destruct (get_bit label depth); eauto.
Qed.

Lemma is_proof_to_is_found label found proof h:
  is_proof label found proof h -∗
  is_found label found h.
Proof. iNamed 1. iFrame "#%". Qed.

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

Lemma is_map_agree_entry m h label val :
  is_map m h -∗
  is_entry label val h -∗
  ⌜ m !! label = val ⌝.
Proof.
  iNamedSuffix 1 "0". subst.
  destruct (tree_to_map t !! label) eqn:He.
  - eapply tree_to_map_Some in He; eauto.
    destruct val; iNamedSuffix 1 "1"; [|iNamedSuffix "Hfound1" "1"];
      iDestruct (tree_path_agree with "Hcut_tree0 Hcut_tree1") as "%Hagree";
      try done; naive_solver.
  - eapply cutless_tree_impl_paths in Hcutless0.
    eapply tree_to_map_None in He as [? [? ?]]; eauto.
    destruct val; iNamedSuffix 1 "1"; [|iNamedSuffix "Hfound1" "1"];
      iDestruct (tree_path_agree with "Hcut_tree0 Hcut_tree1") as "%Hagree";
      try done; naive_solver.
Qed.

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

Lemma is_cut_tree_det t h0 h1 :
  is_cut_tree t h0 -∗
  is_cut_tree t h1 -∗
  ⌜ h0 = h1 ⌝.
Proof.
  iInduction t as [| ? | ? IH0 ? IH1 | ?] forall (h0 h1);
    simpl; iNamedSuffix 1 "0"; iNamedSuffix 1 "1".
  - by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %?.
  - by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %?.
  - iDestruct ("IH0" with "Hleft_hash0 Hleft_hash1") as %->.
    iDestruct ("IH1" with "Hright_hash0 Hright_hash1") as %->.
    by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %?.
  - naive_solver.
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

Lemma sorted_tree_pair_dom_eq {l0 l1 r0 r1 depth} :
  let t0 := Inner l0 l1 in
  let t1 := Inner r0 r1 in
  tree_to_map t0 = tree_to_map t1 →
  sorted_tree t0 depth →
  sorted_tree t1 depth →
  dom (tree_to_map l0) = dom (tree_to_map r0)
    ∧ dom (tree_to_map l1) = dom (tree_to_map r1).
Proof.
  intros. subst t0 t1. simpl in *.
  apply (f_equal dom) in H.
  rewrite !dom_union_L in H.
  opose proof (proj1 (set_eq _ _) H).
  intuition; apply set_eq; intros.
  - split; intros.
    + opose proof (proj1 (H2 x) _); [set_solver|].
      apply elem_of_union in H10. intuition.
      apply H1 in H7. apply H9 in H11. congruence.
    + opose proof (proj2 (H2 x) _); [set_solver|].
      apply elem_of_union in H10. intuition.
      apply H4 in H7. apply H8 in H11. congruence.
  - split; intros.
    + opose proof (proj1 (H2 x) _); [set_solver|].
      apply elem_of_union in H10. intuition.
      apply H8 in H7. apply H4 in H11. congruence.
    + opose proof (proj2 (H2 x) _); [set_solver|].
      apply elem_of_union in H10. intuition.
      apply H9 in H7. apply H1 in H11. congruence.
Qed.

Lemma tree_to_map_inner_eq {l0 l1 r0 r1 depth} :
  let t0 := Inner l0 l1 in
  let t1 := Inner r0 r1 in
  tree_to_map t0 = tree_to_map t1 →
  sorted_tree t0 depth →
  sorted_tree t1 depth →
  tree_to_map l0 = tree_to_map r0 ∧ tree_to_map l1 = tree_to_map r1.
Proof.
  intros. subst t0 t1. simpl in *. destruct_and?.
  opose proof (tree_labels_have_bit_disjoint l1 l0 _ _ _); [done..|].
  opose proof (tree_labels_have_bit_disjoint r1 r0 _ _ _); [done..|].
  apply map_disjoint_dom in H7, H9.
  opose proof (sorted_tree_pair_dom_eq H _ _); [done..|]. destruct_and?.
  by eapply map_union_dom_pair_eq.
Qed.

Lemma tree_to_map_det {t0 t1 depth} :
  tree_to_map t0 = tree_to_map t1 →
  sorted_tree t0 depth →
  sorted_tree t1 depth →
  cutless_tree t0 →
  cutless_tree t1 →
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

End proof.
