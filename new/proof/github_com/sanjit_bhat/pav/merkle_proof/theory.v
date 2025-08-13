From Corelib.Program Require Import Wf.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.proof Require Import proof_prelude.
From Perennial.Helpers Require Import bytes NamedProps.

From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi.

From New.proof.github_com.sanjit_bhat.pav.merkle_proof Require Import base.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

(* get_bit returns false if bit n of l is 0 (or the bit is past the length of l). *)
Definition get_bit l n : bool :=
  match bytes_to_bits l !! n with
  | None => false
  | Some bit => bit
  end.

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

(* need this gallina transl of Golang [merkle.put] for determ spec.
determ needed bc user might call [VerifyMemb] multiple times on same tree,
expecting dig to be equal across calls.
to guarantee that, [merkle.proofToTree] needs to determ make tree from
inputted proof, and [merkle.put] needs to determ update tree with label, val.

NOTE: the code has tricky termination reasoning due to put-into-leaf
expanding common label bits into inner nodes.
this reasoning is reflected into gallina using the depth measure.
NOTE: using fuel=max_depth would allow for normal Fixpoint,
which reduces more nicely (under concrete fuel).
but proving that (exists fuel => Some tree) might be more difficult
than working with Program Fixpoint, we'll see. *)
Program Fixpoint pure_put t depth label val {measure (max_depth - depth)} :=
  if decide (depth ≥ max_depth)
  then
    (* Golang put won't hit this. need for measure. *)
    None
  else match t with
  | Empty => Some (Leaf label val)
  | Leaf label' val' =>
    if decide (label = label')
    then Some (Leaf label val)
    else
      (* "unfolding" the two leaf puts lets us use [S depth] in
      recursive calls, which satisfies the depth measure. *)
      let (c0, c1) := if get_bit label' depth then (Empty, t) else (t, Empty) in
      let c := if get_bit label depth then c1 else c0 in
      let t' := pure_put c (S depth) label val in
      if get_bit label depth then Inner c0 <$> t' else (λ x, Inner x c1) <$> t'
  | Inner c0 c1 =>
    let c := if get_bit label depth then c1 else c0 in
    let t' := pure_put c (S depth) label val in
    if get_bit label depth then Inner c0 <$> t' else (λ x, Inner x c1) <$> t'
  | Cut _ =>
    (* Golang put won't hit this. *)
    None
  end.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Final Obligation. auto using lt_wf. Qed.

(* [sibs] order reversed from code. *)
Fixpoint pure_newShell label depth (sibs : list $ list w8) :=
  match sibs with
  | [] => Empty
  | h :: sibs' =>
    let c := Cut h in
    let t := pure_newShell label (S depth) sibs' in
    if get_bit label depth then Inner c t else Inner t c
  end.

Definition pure_proofToTree label sibs oleaf :=
  let t := pure_newShell label 0 sibs in
  match oleaf with
  | None => Some t
  | Some (l, v) => pure_put t 0 l v
  end.

Fixpoint pure_Digest t :=
  cryptoffi.pure_hash
    match t with
    | Empty => [emptyNodeTag]
    | Leaf l v =>
      leafNodeTag ::
      (u64_le $ length l) ++ l ++
      (u64_le $ length v) ++ v
    | Inner c0 c1 => innerNodeTag :: pure_Digest c0 ++ pure_Digest c1
    | Cut h => h
    end.

(** tree paths. *)

Fixpoint is_path t depth label found :=
  match t with
  | Empty =>
    found = None
  | Leaf found_label found_val =>
    found = Some (found_label, found_val)
  | Inner child0 child1 =>
    match bytes_to_bits label !! depth with
    | None => False
    | Some false => is_path child0 (S depth) label found
    | Some true => is_path child1 (S depth) label found
    end
  | Cut _ => False
  end.

Definition found_nonmemb label (found : option $ (list w8 * list w8)%type) :=
  match found with
  | None => True
  | Some (found_label, _) => label ≠ found_label
  end.

Definition is_entry t label oval :=
  ∃ f,
  is_path t 0 label f ∧
  match oval with
  | Some v => f = Some (label, v)
  | None => found_nonmemb label f
  end.

(** relation between trees and maps. *)

(* [to_map_aux] only collects leaves located in the right place. *)
Fixpoint to_map_aux t pref : gmap (list w8) (list w8) :=
  match t with
  | Empty => ∅
  | Leaf label val =>
    if decide (pref `prefix_of` bytes_to_bits label)
    then {[label := val]}
    else ∅
  | Inner child0 child1 =>
    to_map_aux child0 (pref ++ [false]) ∪
    to_map_aux child1 (pref ++ [true])
  | Cut _ => ∅
  end.
Definition to_map t := to_map_aux t [].

Lemma to_map_pref_Some t pref label :
  is_Some (to_map_aux t pref !! label) →
  pref `prefix_of` bytes_to_bits label.
Proof.
  revert pref.
  induction t; simpl; intros ? Hsome.
  - by simpl_map.
  - case_decide; [|by simpl_map].
    destruct (decide (label0 = label)).
    + by subst.
    + by simpl_map.
  - apply lookup_union_is_Some in Hsome.
    destruct_or!.
    + apply IHt1 in Hsome.
      by eapply prefix_app_l.
    + apply IHt2 in Hsome.
      by eapply prefix_app_l.
  - by simpl_map.
Qed.

Lemma to_map_pref_None t pref label :
  ¬ pref `prefix_of` bytes_to_bits label →
  to_map_aux t pref !! label = None.
Proof.
  revert pref.
  induction t; simpl; intros; [done|idtac..|done].
  - case_decide; [|by simpl_map].
    opose proof (prefix_neq _ _ _ _ _); [done..|].
    destruct (decide (label = label0)) as [Heq|?].
    + by apply (f_equal bytes_to_bits) in Heq.
    + by simpl_map.
  - apply lookup_union_None_2.
    + apply IHt1.
      by intros Hpref%prefix_app_l.
    + apply IHt2.
      by intros Hpref%prefix_app_l.
Qed.

Lemma to_map_disj t0 t1 pref :
  to_map_aux t0 (pref ++ [false]) ##ₘ to_map_aux t1 (pref ++ [true]).
Proof.
  apply map_disjoint_spec.
  intros **.
  opose proof (to_map_pref_Some _ _ _ _) as [? Hp0]; [done|].
  assert (¬ pref ++ [false] `prefix_of` bytes_to_bits i).
  { rewrite /prefix.
    intros [? Hp1].
    rewrite Hp1 in Hp0.
    list_simplifier. }
  opose proof (to_map_pref_None t0 _ _ _); [done|].
  by simplify_eq/=.
Qed.

Lemma entry_impl_lookup t label oval :
  is_entry t label oval →
  to_map t !! label = oval.
Proof.
  rewrite /is_entry /to_map.
  remember ([]) as pref.
  replace (0%nat) with (length pref) by (by subst).
  assert (pref `prefix_of` bytes_to_bits label).
  { subst. apply prefix_nil. }
  clear Heqpref.
  intros (?&?&?).
  generalize dependent pref.

  induction t; simpl; intros ?? Hpath; [..|done].
  - simpl_map. case_match; by subst.
  - case_match; simplify_eq/=; case_decide; by simpl_map.
  - opose proof (to_map_disj t1 t2 pref).
    case_match; [|done].
    case_match.
    + opose proof (IHt2 (pref ++ [true]) _ _) as Hl0.
      { by apply prefix_snoc. }
      { exact_eq Hpath. len. }
      opose proof (to_map_pref_None t1 (pref ++ [false]) label _) as Hl1.
      { intros ?%prefix_snoc_inv. naive_solver. }
      rewrite lookup_union Hl0 Hl1.
      by simplify_option_eq.
    + opose proof (IHt1 (pref ++ [false]) _ _) as Hl0.
      { by apply prefix_snoc. }
      { exact_eq Hpath. len. }
      opose proof (to_map_pref_None t2 (pref ++ [true]) label _) as Hl1.
      { intros ?%prefix_snoc_inv. naive_solver. }
      rewrite lookup_union Hl0 Hl1.
      by simplify_option_eq.
Qed.

(*
Definition labels_have_bit t n bit :=
  ∀ l,
  l ∈ dom (to_map t) →
  get_bit l n = bit.

Fixpoint is_sorted t depth :=
  match t with
  | Inner child0 child1 =>
    labels_have_bit child0 depth false ∧
    labels_have_bit child1 depth true ∧
    is_sorted child0 (S depth) ∧
    is_sorted child1 (S depth)
  | _ => True
  end.

Lemma labels_have_bit_disjoint t0 t1 depth :
  labels_have_bit t0 depth false →
  labels_have_bit t1 depth true →
  dom (to_map t0) ## dom (to_map t1).
Proof.
  intros Hb0 Hb1.
  apply elem_of_disjoint.
  intros ? Hd0 Hd1.
  apply Hb0 in Hd0.
  apply Hb1 in Hd1.
  congruence.
Qed.

Lemma bit_impl_lookup_None label depth bit t :
  get_bit label depth = bit →
  labels_have_bit t depth (negb bit) →
  to_map t !! label = None.
Proof.
  intros.
  destruct (to_map t !! label) eqn:He; eauto.
  assert (get_bit label depth = negb bit).
  { apply H0. apply elem_of_dom; eauto. }
  rewrite H1 in H. destruct bit; simpl in *; congruence.
Qed.

Lemma entry_impl_lookup t label oval :
  is_entry t label oval →
  is_sorted t 0 →
  to_map t !! label = oval.
Proof.
  intros He Hs.
  rewrite /is_entry in He.
  remember 0%nat as d.
  clear Heqd.
  revert d He Hs.
  induction t; simpl; intros ? He Hs.
  - case_match; [done|by simpl_map].
  - case_match; simpl in *.
    + by simplify_map_eq/=.
    + rewrite /found_nonmemb in He.
      destruct He as [[[??]|]?]; intuition; by simplify_map_eq/=.
  - intuition.
    opose proof (labels_have_bit_disjoint _ _ _ _ _); [done..|].
    case_match.
    + apply lookup_union_Some. { by apply map_disjoint_dom. }
      case_match; naive_solver.
    + apply lookup_union_None.
      case_match.
      all: opose proof (bit_impl_lookup_None _ _ _ _ _ _); [done..|];
        naive_solver.
  - by case_match.
Qed.

(* [is_sorted_prefix] is prefix-structured, which matches
the full-tree decoding form. *)
Fixpoint is_sorted_prefix t pref :=
  match t with
  | Leaf label _ => pref `prefix_of` (bytes_to_bits label)
  | Inner c0 c1 =>
    is_sorted_prefix c0 (pref ++ [false]) ∧
    is_sorted_prefix c1 (pref ++ [true])
  | _ => True
  end.

Lemma sorted_impl_map_prefix t pref :
  is_sorted_prefix t pref →
  (∀ l, l ∈ dom (to_map t) → pref `prefix_of` (bytes_to_bits l)).
Proof.
  revert pref.
  induction t; simpl; intros ? Hs **.
  - set_solver.
  - set_unfold. subst. done.
  - intuition.
    set_unfold. destruct_or!.
    + opose proof (IHt1 _ _ _ _) as Hpref; [done..|].
      by eapply prefix_app_l.
    + opose proof (IHt2 _ _ _ _) as Hpref; [done..|].
      by eapply prefix_app_l.
  - set_solver.
Qed.

Lemma sorted_impl_have_bit t pref :
  is_sorted_prefix t pref →
  ∀ n bit, pref !! n = Some bit → labels_have_bit t n bit.
Proof.
  intros ** ? **.
  opose proof (sorted_impl_map_prefix _ _ _ _ _); [done..|].
  rewrite /get_bit.
  by erewrite prefix_lookup_Some.
Qed.

Lemma sorted_prefix_impl_sorted t pref :
  is_sorted_prefix t pref →
  is_sorted t (length pref).
Proof.
  revert pref.
  induction t; intros; try done.
  simpl in *.
  destruct_and!.
  opose proof (IHt1 _ _) as Hs0; [done|].
  opose proof (IHt2 _ _ ) as Hs1; [done|].
  rewrite (comm app) in Hs0.
  rewrite (comm app) in Hs1.
  rewrite !length_app in Hs0 Hs1.
  simpl in *.
  intuition.
  - eapply sorted_impl_have_bit; [done|]. by rewrite lookup_snoc.
  - eapply sorted_impl_have_bit; [done|]. by rewrite lookup_snoc.
Qed.

Lemma sorted_impl_sorted_prefix t :
  is_sorted t 0 →
  is_sorted_prefix t [].
Proof. Admitted.
*)

(** full trees / maps. *)

Inductive dec_node :=
  | DecEmpty
  | DecLeaf (label val : list w8)
  | DecInner (hash0 hash1 : list w8)
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
Local Definition decode_node (data : option $ list w8) :=
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
      else DecInvalid
    end
  end.

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

Lemma decode_empty_det :
  decode_node (Some [emptyNodeTag]) = DecEmpty.
Proof.
  simpl.
  case_decide; [done|].
  naive_solver.
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

Lemma decode_leaf_det_aux l v :
  length l < 2^64 →
  length v < 2^64 →
  decode_leaf (
    u64_le (W64 (length l)) ++ l ++
    u64_le (W64 (length v)) ++ v
  ) = Some (l, v).
Proof.
  intros. rewrite /decode_leaf.
  repeat (rewrite take_app_length'; [|len]).
  rewrite u64_le_to_word.
  repeat (rewrite drop_app_length'; [|len]).
  repeat (rewrite take_app_length'; [|len]).
  rewrite u64_le_to_word.
  rewrite take_ge; [|word].
  rewrite drop_ge; [|word].

  case_bool_decide as Hif.
  2: { revert Hif. len. }
  clear Hif.
  case_bool_decide as Hif.
  2: { revert Hif. len. }
  clear Hif.
  case_bool_decide as Hif.
  2: { revert Hif. len. }
  clear Hif.
  case_bool_decide as Hif.
  2: { revert Hif. len. }
  clear Hif.
  by case_bool_decide.
Qed.

Lemma decode_leaf_det l v :
  length l < 2^64 →
  length v < 2^64 →
  decode_node (
    Some $ leafNodeTag ::
    u64_le (W64 (length l)) ++ l ++
    u64_le (W64 (length v)) ++ v
  ) = DecLeaf l v.
Proof.
  intros. simpl.
  case_decide; [naive_solver|].
  case_decide; [|done].
  by rewrite decode_leaf_det_aux.
Qed.

Lemma decode_inner_inj d h0 h1 :
  decode_node d = DecInner h0 h1 →
  d = Some $ innerNodeTag :: h0 ++ h1 ∧
    Z.of_nat $ length h0 = cryptoffi.hash_len ∧
    Z.of_nat $ length h1 = cryptoffi.hash_len.
Proof.
  rewrite /decode_node. intros.
  case_match; [|done].
  case_match; [done|].
  case_decide; [naive_solver|].
  case_decide. { by case_match. }
  case_decide; [|done].
  destruct_and!.
  simplify_eq/=.
  split; [|len].
  by rewrite take_drop.
Qed.

Lemma decode_inner_det h0 h1 :
  Z.of_nat $ length h0 = cryptoffi.hash_len →
  Z.of_nat $ length h1 = cryptoffi.hash_len →
  decode_node (Some $ innerNodeTag :: h0 ++ h1) = DecInner h0 h1.
Proof.
  intros. simpl.
  case_decide; [len|].
  case_decide; [done|].
  case_decide.
  2: { intuition. revert H3. len. }
  rewrite take_app_length'; [|lia].
  by rewrite drop_app_length'; [|lia].
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
  - opose proof (decode_inner_inj d0 _ _ _) as [-> ?]; [done|].
    by opose proof (decode_inner_inj d1 _ _ _) as [-> ?].
Qed.

(* the overall structure of [is_full_tree] is a bit unconventional.
from the hash [h], it recursively computes (via [decode_node]) the tree [t].
a few consequences:
- it "resolves" the tree to the maximum extent possible.
- it limits invalid nodes only to when they're generated by decoding.
this allows proving [is_full_tree_inj].

[limit] prevents infinite recursion. *)
Fixpoint is_full_tree t h limit : iProp Σ :=
  ∃ d,
  "#His_hash" ∷ cryptoffi.is_hash d h ∗
  "#Hdecode" ∷ match decode_node d with
  | DecEmpty =>
    "%" ∷ ⌜ t = Empty ⌝
  | DecLeaf l v =>
    "%" ∷ ⌜ t = Leaf l v ⌝
  | DecInvalid =>
    "%" ∷ ⌜ t = Cut h ⌝
  | DecInner h0 h1 =>
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
    repeat case_match; apply _.
  - intros. apply exist_persistent. intros.
    repeat case_match; apply _.
Qed.

Lemma is_full_tree_invert h l :
  Z.of_nat (length h) = cryptoffi.hash_len → ⊢
  ∃ t, is_full_tree t h l.
Proof.
  revert h. induction l; intros.
  - iDestruct (cryptoffi.is_hash_invert h) as "[% $]"; [done|].
    repeat case_match; naive_solver.
  - iDestruct (cryptoffi.is_hash_invert h) as "[% $]"; [done|].
    repeat case_match; try naive_solver.
    fold is_full_tree.
    opose proof (decode_inner_inj _ _ _ _) as (_&?&?); [done|].
    iDestruct (IHl hash0) as "[% $]"; [done|].
    iDestruct (IHl hash1) as "[% $]"; [done|].
    naive_solver.
Qed.

(* if [Cut], carries the hash, so hashes must be equal.
otherwise, [decode_node_inj] says that Some preimg's are equal,
which implies the hashes are equal. *)
Lemma is_full_tree_det t h0 h1 l0 l1 :
  is_full_tree t h0 l0 -∗
  is_full_tree t h1 l1 -∗
  ⌜ h0 = h1 ⌝.
Proof.
  iInduction (l0) as [] forall (t h0 h1 l1); destruct l1; simpl;
    iNamedSuffix 1 "0"; iNamedSuffix 1 "1";
    case_match; try case_decide;
    case_match; try case_decide;
    iNamedSuffix "Hdecode0" "0"; iNamedSuffix "Hdecode1" "1";
    simplify_eq/=; try done.
  1-8:
    opose proof (decode_node_inj _ d d0 _ _ _) as (-> & [? ->]); [done..|];
    by iApply cryptoffi.is_hash_det.
  iDestruct ("IHl0" with "Hrecur00 Hrecur01") as %->.
  iDestruct ("IHl0" with "Hrecur10 Hrecur11") as %->.
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
    repeat case_match;
    iNamedSuffix "Hdecode0" "0"; iNamedSuffix "Hdecode1" "1";
    simplify_eq/=; try done.
  iDestruct ("IHlimit" with "Hrecur00 Hrecur01") as %->.
  by iDestruct ("IHlimit" with "Hrecur10 Hrecur11") as %->.
Qed.

(*
Lemma is_full_tree_sorted_aux t h l p :
  is_full_tree t h l p -∗
  ⌜ is_sorted_prefix t p ⌝.
Proof.
  revert t h p. induction l; intros.
  - iNamed 1. repeat case_match; iNamed "Hdecode"; by simplify_eq/=.
  - iNamed 1. repeat case_match; iNamed "Hdecode"; simplify_eq/=; try done.
    fold is_full_tree.
    iDestruct (IHl with "Hrecur0") as %?.
    by iDestruct (IHl with "Hrecur1") as %?.
Qed.

Lemma is_full_tree_sorted t h l p :
  is_full_tree t h l p -∗
  ⌜ is_sorted t (length p) ⌝.
Proof.
  iIntros "H".
  iDestruct (is_full_tree_sorted_aux with "H") as "%".
  iPureIntro. by apply sorted_prefix_impl_sorted.
Qed.
*)

(* to prevent reducing [max_depth]. *)
#[local] Opaque is_full_tree.

Definition is_full_map m h : iProp Σ :=
  ∃ t,
  "%Heq_map" ∷ ⌜ m = to_map t ⌝ ∗
  "#His_tree" ∷ is_full_tree t h max_depth.

Lemma is_full_map_invert h :
  Z.of_nat (length h) = cryptoffi.hash_len → ⊢
  ∃ m, is_full_map m h.
Proof.
  intros.
  iDestruct is_full_tree_invert as "[% H]"; [done|].
  iFrame "#".
  iPureIntro. naive_solver.
Qed.

Lemma is_full_map_inj m0 m1 h :
  is_full_map m0 h -∗
  is_full_map m1 h -∗
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
    "#Hleft_hash" ∷ is_cut_tree child0 h0 ∗
    "#Hright_hash" ∷ is_cut_tree child1 h1 ∗
    "#His_hash" ∷ cryptoffi.is_hash (Some $ [innerNodeTag] ++ h0 ++ h1) h
  | Cut ch =>
    "%Heq_cut" ∷ ⌜ h = ch ⌝ ∗
    "%Hlen_hash" ∷ ⌜ Z.of_nat $ length h = cryptoffi.hash_len ⌝
  end.

#[global]
Instance is_cut_tree_persistent t h : Persistent (is_cut_tree t h).
Proof. revert h. induction t; apply _. Qed.

Fixpoint cutless_path t (label : list w8) depth : Prop :=
  match t with
  | Cut _ => False
  | Inner child0 child1 =>
    match get_bit label depth with
    | false => cutless_path child0 label (S depth)
    | true  => cutless_path child1 label (S depth)
    end
  | _ => True
  end.

Fixpoint cutless_tree t : Prop :=
  match t with
  | Inner child0 child1 => cutless_tree child0 ∧ cutless_tree child1
  | Cut _ => False
  | _ => True
  end.

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

(** full <-> cut tree reln. *)

Fixpoint is_limit t limit :=
  match t with
  | Inner c0 c1 =>
    match limit with
    | 0%nat => False
    | S l =>
      is_limit c0 l ∧
      is_limit c1 l
    end
  | _ => True
  end.

#[local] Transparent is_full_tree.

Lemma path_txfer t0 t1 h l d label found :
  is_cut_tree t0 h -∗
  is_full_tree t1 h l -∗
  ⌜ is_path t0 d label found ⌝ -∗
  ⌜ is_limit t0 l ⌝ -∗
  ⌜ is_path t1 d label found ⌝.
Proof.
  revert t1 h l d label found.
  induction t0; destruct l; simpl; intros;
    iNamedSuffix 1 "0";
    iNamedSuffix 1 "1";
    iIntros (??).
  (* TODO: duplication from destruct [limit]. *)
  (* TODO: could make smth like an induction principle for
  proving inductive properties across cut tree and full tree,
  which takes care of "unifying trees" for us. *)
  - iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %<-.
    rewrite decode_empty_det.
    iNamed "Hdecode1".
    naive_solver.
  - iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %<-.
    rewrite decode_empty_det.
    iNamed "Hdecode1".
    naive_solver.
  - iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %<-.
    rewrite decode_leaf_det; [|done..].
    (*
    case_decide; iNamed "Hdecode1".
    + naive_solver.
    + iPureIntro. subst. simpl. *)
      (* stuck: case when full tree has bad prefix, which turns leaf into cut.
      we need sorted_prefix assumption to contradict this;
      otherwise, can't establish path.
      let's push on alternate plan where to_map has prefix filtering.
      that would remove sorted reasoning from here,
      tho it might bring other complications. *)
Admitted.

(* TODO: overall plan for full-map Verify reasoning:
- user shows up with is_full_map m (hash:=comp proof) from merkle inversion.
- Verify checks path down cut tree (hash:=comp proof),
explicitly bounding depth.
- path down cut tree impl path down full tree, if both have same hash.
- path down full tree impl full map entry.

func VerifyMemb(label, val, proof []byte) (dig []byte, err bool) {
*)

(** tree proofs. *)

(*
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

(** tree to map relation. *)

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

(* TODO: stragglers. *)

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
