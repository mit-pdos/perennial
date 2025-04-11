From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang.lib Require Import encoding.
(* for sealed. *)
From Perennial Require Import base.
From Goose.github_com.mit_pdos.pav Require Import merkle.

From Perennial.Helpers Require Import bytes.
From Perennial.program_proof.pav Require Import cryptoffi cryptoutil.
From Perennial.program_proof Require Import std_proof marshal_stateless_proof.

Notation empty_node_tag := (W8 0) (only parsing).
Notation leaf_node_tag := (W8 1) (only parsing).
Notation inner_node_tag := (W8 2) (only parsing).

(* TODO: rm once seal merged in. *)
Program Definition u64_le_seal := sealed @u64_le.
Definition u64_le_unseal : u64_le_seal = _ := seal_eq _.
Lemma u64_le_seal_len x :
  length $ u64_le_seal x = 8%nat.
Proof. rewrite u64_le_unseal. done. Qed.
Global Instance u64_le_seal_inj : Inj eq eq u64_le_seal.
Proof. rewrite u64_le_unseal. apply _. Qed.

Module MerkleProof.
Record t :=
  mk {
    Siblings: list w8;
    FoundOtherLeaf: bool;
    LeafLabel: list w8;
    LeafVal: list w8;
  }.
Definition encodes (obj : t) (enc : list w8) : Prop :=
  uint.Z (W64 (length obj.(Siblings))) = length obj.(Siblings) ∧
  uint.Z (W64 (length obj.(LeafLabel))) = length obj.(LeafLabel) ∧
  uint.Z (W64 (length obj.(LeafVal))) = length obj.(LeafVal) ∧

  enc = u64_le_seal (length obj.(Siblings)) ++ obj.(Siblings) ++
  [(if obj.(FoundOtherLeaf) then W8 1 else W8 0)] ++
  u64_le_seal (length obj.(LeafLabel)) ++ obj.(LeafLabel) ++
  u64_le_seal (length obj.(LeafVal)) ++ obj.(LeafVal).

Lemma inj {obj0 obj1 enc0 enc1 tail0 tail1} :
  enc0 ++ tail0 = enc1 ++ tail1 →
  encodes obj0 enc0 →
  encodes obj1 enc1 →
  obj0 = obj1 ∧ enc0 = enc1 ∧ tail0 = tail1.
Proof.
  intros ? (?&?&? & Henc0) (?&?&? & Henc). subst.
  list_simplifier. move: H => Henc.
  apply app_inj_1 in Henc as [Hlen_sib Henc].
  2: { by rewrite !u64_le_seal_len. }
  apply (inj u64_le_seal) in Hlen_sib.
  apply app_inj_1 in Henc as [Heq_sib Henc]; [|word].
  inv Henc as [[Heq_found Henc']].
  (* FIXME(word): somehow word.unsigned gets unfolded here. *)
  apply app_inj_1 in Henc' as [Hlen_label Henc].
  2: { by rewrite !u64_le_seal_len. }
  apply (inj u64_le_seal) in Hlen_label.
  apply app_inj_1 in Henc as [Heq_label Henc]; [|word].
  apply app_inj_1 in Henc as [Hlen_val Henc].
  2: { by rewrite !u64_le_seal_len. }
  apply (inj u64_le_seal) in Hlen_val.
  assert (obj0.(FoundOtherLeaf) = obj1.(FoundOtherLeaf)) as ?.
  { by repeat case_match. }
  apply app_inj_1 in Henc as [Heq_val Henc]; [|word].
  destruct obj0, obj1. by simplify_eq/=.
Qed.

Section defs.
Context `{!heapGS Σ}.
Definition own ptr obj d : iProp Σ :=
  ∃ sl_sibs sl_leaf_label sl_leaf_val,
  "Hsl_sibs" ∷ own_slice_small sl_sibs byteT d obj.(Siblings) ∗
  "Hptr_sibs" ∷ ptr ↦[MerkleProof :: "Siblings"]{d} (slice_val sl_sibs) ∗
  "Hptr_found_other_leaf" ∷
    ptr ↦[MerkleProof :: "FoundOtherLeaf"]{d} #obj.(FoundOtherLeaf) ∗
  "Hsl_leaf_label" ∷ own_slice_small sl_leaf_label byteT d obj.(LeafLabel) ∗
  "Hptr_leaf_label" ∷ ptr ↦[MerkleProof :: "LeafLabel"]{d} (slice_val sl_leaf_label) ∗
  "Hsl_leaf_val" ∷ own_slice_small sl_leaf_val byteT d obj.(LeafVal) ∗
  "Hptr_leaf_val" ∷ ptr ↦[MerkleProof :: "LeafVal"]{d} (slice_val sl_leaf_val).

Lemma wp_dec sl_b d b :
  {{{
    "Hsl_b" ∷ own_slice_small sl_b byteT d b
  }}}
  MerkleProofDecode (slice_val sl_b)
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, slice_val sl_tail, #err);
    let wish := (λ enc obj tail,
      ("%Henc_obj" ∷ ⌜ encodes obj enc ⌝ ∗
      "%Heq_tail" ∷ ⌜ b = enc ++ tail ⌝) : iProp Σ) in
    "Hgenie" ∷
      (⌜ err = false ⌝ ∗-∗
      ∃ enc obj tail, wish enc obj tail) ∗
    "Herr" ∷
      (∀ enc obj tail, wish enc obj tail -∗
      "Hown_obj" ∷ own ptr_obj obj d ∗
      "Hsl_tail" ∷ own_slice_small sl_tail byteT d tail)
  }}}.
Proof. Admitted.

End defs.
End MerkleProof.

Section proof.
Context `{!heapGS Σ}.

Definition bytes_to_bits l := concat (byte_to_bits <$> l).

(* get_bit returns false if bit n of l is 0 (or the bit is past the length of l). *)
Definition get_bit l (n : w64) : bool :=
  match bytes_to_bits l !! (uint.nat n) with
  | None => false
  | Some bit => bit
  end.

Inductive tree :=
| Empty
| Leaf (label: list w8) (val: list w8)
| Inner (child0: tree) (child1: tree)
| Cut (hash: list w8).

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

Fixpoint is_tree_hash (t: tree) (h: list w8) : iProp Σ :=
  match t with
  | Empty =>
    "#His_hash" ∷ is_hash [empty_node_tag] h
  | Leaf label val =>
    "%Hinb_label" ∷ ⌜ uint.Z (W64 (length label)) = length label ⌝ ∗
    "#His_hash" ∷
      is_hash ([leaf_node_tag] ++
        (u64_le_seal $ length label) ++ label ++
        (u64_le_seal $ length val) ++ val) h
  | Inner child0 child1 =>
    ∃ hl hr,
    "#Hleft_hash" ∷ is_tree_hash child0 hl ∗
    "#Hright_hash" ∷ is_tree_hash child1 hr ∗
    "#His_hash" ∷ is_hash ([inner_node_tag] ++ hl ++ hr) h
  | Cut ch =>
    "%Heq_cut" ∷ ⌜ h = ch ⌝ ∗
    "%Hlen_hash" ∷ ⌜ Z.of_nat $ length h = hash_len ⌝
  end.

#[global]
Instance is_tree_hash_persistent t h : Persistent (is_tree_hash t h).
Proof. revert h. induction t; apply _. Qed.

Definition is_merkle_map (m: gmap (list w8) (list w8)) (h: list w8) : iProp Σ :=
  ∃ t,
  "%Heq_tree_map" ∷ ⌜ m = tree_to_map t ⌝ ∗
  "%Hsorted" ∷ ⌜ sorted_tree t 0 ⌝ ∗
  "%Hcutless" ∷ ⌜ cutless_tree t ⌝ ∗
  "%Hminimal" ∷ ⌜ minimal_tree t ⌝ ∗
  "#Htree_hash" ∷ is_tree_hash t h.

Definition is_merkle_found (label: list w8)
    (found: option ((list w8) * (list w8))%type) (h: list w8) : iProp Σ :=
  ∃ t,
  "%Htree_path" ∷ ⌜ tree_path t label 0 found ⌝ ∗
  "#Htree_hash" ∷ is_tree_hash t h.

Definition found_nonmemb (label: list w8)
    (found: option ((list w8) * (list w8))%type) :=
  match found with
  | None => True
  | Some (found_label, _) => label ≠ found_label
  end.

(* is_merkle_entry represents memb and nonmemb proofs
as Some and None option vals, providing a unified way of expressing them
that directly corresponds to a map entry. *)
Definition is_merkle_entry (label : list w8) (val : option $ list w8)
    (dig : list w8) : iProp Σ :=
  match val with
  | Some v =>
    "#Hfound" ∷ is_merkle_found label (Some (label, v)) dig
  | None =>
    ∃ found,
    "#Hfound" ∷ is_merkle_found label found dig ∗
    "%Hnonmemb" ∷ ⌜ found_nonmemb label found ⌝
  end.

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
        "#Htree_hash" ∷ is_tree_hash child1 sibhash
      | true =>
        "Hrecur_proof" ∷ tree_sibs_proof child1 label (word.add depth (W64 1)) proof' ∗
        "#Htree_hash" ∷ is_tree_hash child0 sibhash
      end
  | Cut _ => False
  end.

#[global]
Instance tree_sibs_proof_persistent t l d p : Persistent (tree_sibs_proof t l d p).
Proof.
  revert d p. induction t; try apply _.
  simpl. intros. case_match; apply _.
Qed.

Definition is_merkle_proof (label: list w8)
    (found: option ((list w8) * (list w8)%type)) (proof: list w8)
    (h: list w8) : iProp Σ :=
  ∃ t,
  "#Hhash" ∷ is_tree_hash t h ∗
  "#Hproof" ∷ tree_sibs_proof t label (W64 0) proof ∗
  "%Hpath" ∷ ⌜ tree_path t label (W64 0) found ⌝.

Definition wish_merkle_Verify (in_tree : bool) label val proof dig : iProp Σ :=
  ∃ found proof_obj proof' tail,
  "%Henc" ∷ ⌜ MerkleProof.encodes proof_obj proof' ⌝ ∗
  "%Heq_tail" ∷ ⌜ proof = proof' ++ tail ⌝ ∗
  "%Heq_found" ∷
    ⌜if in_tree
    then found = Some (label, val)
    else if proof_obj.(MerkleProof.FoundOtherLeaf)
      then found = Some (proof_obj.(MerkleProof.LeafLabel), proof_obj.(MerkleProof.LeafVal)) ∧
        label ≠ proof_obj.(MerkleProof.LeafLabel)
      else found = None ⌝ ∗
  "#His_proof" ∷ is_merkle_proof label found proof_obj.(MerkleProof.Siblings) dig.

Lemma wish_merkle_Verify_to_entry in_tree label val proof dig :
  wish_merkle_Verify in_tree label val proof dig -∗
  is_merkle_entry label (if in_tree then Some val else None) dig.
Proof.
  iNamed 1. iNamed "His_proof".
  repeat case_match; intuition; subst; by iFrame "#%".
Qed.

(* Derived facts. *)

Lemma is_tree_hash_len t h:
  is_tree_hash t h -∗
  ⌜ Z.of_nat $ length h = hash_len ⌝.
Proof. destruct t; iNamed 1; [..|done]; by iApply is_hash_len. Qed.

Lemma tree_path_agree label depth found0 found1 h t0 t1:
  tree_path t0 label depth found0 →
  tree_path t1 label depth found1 →
  is_tree_hash t0 h -∗
  is_tree_hash t1 h -∗
  ⌜ found0 = found1 ⌝.
Proof.
  iInduction t0 as [| ? | ? IH0 ? IH1 | ?] forall (depth t1 h);
    destruct t1; simpl; iIntros "*"; try done;
    iNamedSuffix 1 "0";
    iNamedSuffix 1 "1";
    iDestruct (is_hash_inj with "His_hash0 His_hash1") as %?;
    try naive_solver.

  (* both leaves. use leaf encoding. *)
  - iPureIntro. list_simplifier.
    apply app_inj_1 in H as [Heq_len_label H].
    2: { by rewrite !u64_le_seal_len. }
    apply (inj u64_le_seal) in Heq_len_label.
    assert (length label0 = length label1) as ?.
    { rewrite Heq_len_label in Hinb_label0. word. }
    list_simplifier.
    apply app_inj_1 in H1; [naive_solver|].
    by rewrite !u64_le_seal_len.
  (* both inner. use inner encoding and next_pos same to get
  the same next_hash. then apply IH. *)
  - iDestruct (is_tree_hash_len with "Hleft_hash0") as %?.
    iDestruct (is_tree_hash_len with "Hleft_hash1") as %?.
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
  cutless_tree t →
  ∃ found,
    tree_path t label depth found ∧
    found_nonmemb label found.
Proof.
  revert depth.
  induction t; simpl; intros.
  - rewrite lookup_empty in H. eexists; eauto.
  - apply lookup_singleton_None in H. eexists. split; eauto. simpl; congruence.
  - apply lookup_union_None in H. intuition.
    destruct (get_bit label depth); eauto.
  - inversion H1.
Qed.

Lemma is_merkle_proof_to_is_merkle_found label found proof h:
  is_merkle_proof label found proof h -∗
  is_merkle_found label found h.
Proof. iNamed 1. iFrame "#%". Qed.

Lemma is_merkle_found_agree label found0 found1 h:
  is_merkle_found label found0 h -∗
  is_merkle_found label found1 h -∗
  ⌜found0 = found1⌝.
Proof.
  iIntros "H0 H1".
  iDestruct "H0" as (?) "[% H0]".
  iDestruct "H1" as (?) "[% H1]".
  iApply (tree_path_agree with "H0 H1"); eauto.
Qed.

Lemma is_merkle_map_agree_entry m h label val :
  is_merkle_map m h -∗
  is_merkle_entry label val h -∗
  ⌜ m !! label = val ⌝.
Proof.
  iNamedSuffix 1 "0". subst.
  destruct (tree_to_map t !! label) eqn:He.
  - eapply tree_to_map_Some in He; eauto.
    destruct val; iNamedSuffix 1 "1"; [|iNamedSuffix "Hfound1" "1"];
      iDestruct (tree_path_agree with "Htree_hash0 Htree_hash1") as "%Hagree";
      try done; naive_solver.
  - eapply tree_to_map_None in He as [? [? ?]]; eauto.
    destruct val; iNamedSuffix 1 "1"; [|iNamedSuffix "Hfound1" "1"];
      iDestruct (tree_path_agree with "Htree_hash0 Htree_hash1") as "%Hagree";
      try done; naive_solver.
Qed.

Lemma tree_sibs_proof_len t label depth proof :
  tree_sibs_proof t label depth proof -∗
  ⌜ Z.of_nat (length proof) `mod` hash_len = 0 ⌝.
Proof.
  iInduction t as [| ? | ? IH0 ? IH1 | ?] forall (depth proof);
    simpl; iNamed 1; subst; simpl; [word..|idtac|done].
  rewrite length_app. case_match; iNamed "Hrecur";
    iDestruct (is_tree_hash_len with "Htree_hash") as %?.
  - iDestruct ("IH1" with "Hrecur_proof") as %?. word.
  - iDestruct ("IH0" with "Hrecur_proof") as %?. word.
Qed.

Lemma is_tree_hash_det t h0 h1 :
  is_tree_hash t h0 -∗
  is_tree_hash t h1 -∗
  ⌜ h0 = h1 ⌝.
Proof.
  iInduction t as [| ? | ? IH0 ? IH1 | ?] forall (h0 h1);
    simpl; iNamedSuffix 1 "0"; iNamedSuffix 1 "1".
  - by iDestruct (is_hash_det with "His_hash0 His_hash1") as %?.
  - by iDestruct (is_hash_det with "His_hash0 His_hash1") as %?.
  - iDestruct ("IH0" with "Hleft_hash0 Hleft_hash1") as %->.
    iDestruct ("IH1" with "Hright_hash0 Hright_hash1") as %->.
    by iDestruct (is_hash_det with "His_hash0 His_hash1") as %?.
  - naive_solver.
Qed.

Lemma is_merkle_proof_eq_dig label found proof hash0 hash1 :
  is_merkle_proof label found proof hash0 -∗
  is_merkle_proof label found proof hash1 -∗
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

  - by iDestruct (is_hash_det with "His_hash0 His_hash1") as %?.
  - naive_solver.
  - apply (f_equal length) in Heq_proof1.
    rewrite length_app in Heq_proof1.
    case_match; iNamed "Hrecur1";
      iDestruct (is_tree_hash_len with "Htree_hash") as %?;
      list_simplifier; word.
  - naive_solver.
  - simplify_eq/=.
    by iDestruct (is_hash_det with "His_hash0 His_hash1") as %?.
  - apply (f_equal length) in Heq_proof1.
    rewrite length_app in Heq_proof1.
    case_match; iNamed "Hrecur1";
      iDestruct (is_tree_hash_len with "Htree_hash") as %?;
      list_simplifier; word.
  - apply (f_equal length) in Heq_proof0.
    rewrite length_app in Heq_proof0.
    case_match; iNamed "Hrecur0";
      iDestruct (is_tree_hash_len with "Htree_hash") as %?;
      list_simplifier; word.
  - apply (f_equal length) in Heq_proof0.
    rewrite length_app in Heq_proof0.
    case_match; iNamed "Hrecur0";
      iDestruct (is_tree_hash_len with "Htree_hash") as %?;
      list_simplifier; word.
  - case_match;
      iNamedSuffix "Hrecur0" "0"; iNamedSuffix "Hrecur1" "1".
    + (* equal sib hashes. *)
      iDestruct (is_tree_hash_len with "Htree_hash0") as %?.
      iDestruct (is_tree_hash_len with "Htree_hash1") as %?.
      subst. apply app_inj_2 in Heq_proof1 as [-> ->]; [|lia].
      iDestruct (is_tree_hash_det with "Hleft_hash0 Htree_hash0") as %->.
      iDestruct (is_tree_hash_det with "Hleft_hash1 Htree_hash1") as %->.
      (* equal child hashes. *)
      iDestruct ("IH1" with "[] [] Hright_hash0 Hrecur_proof0
        Hright_hash1 Hrecur_proof1") as %->; [done..|].
      by iDestruct (is_hash_det with "His_hash0 His_hash1") as %->.
    + (* equal sib hashes. *)
      iDestruct (is_tree_hash_len with "Htree_hash0") as %?.
      iDestruct (is_tree_hash_len with "Htree_hash1") as %?.
      subst. apply app_inj_2 in Heq_proof1 as [-> ->]; [|lia].
      iDestruct (is_tree_hash_det with "Hright_hash0 Htree_hash0") as %->.
      iDestruct (is_tree_hash_det with "Hright_hash1 Htree_hash1") as %->.
      (* equal child hashes. *)
      iDestruct ("IH0" with "[] [] Hleft_hash0 Hrecur_proof0
        Hleft_hash1 Hrecur_proof1") as %->; [done..|].
      by iDestruct (is_hash_det with "His_hash0 His_hash1") as %->.
Qed.

Lemma map_union_dom_pair_eq (m0 m1 m2 m3 : gmap (list w8) (list w8)) :
  m0 ∪ m1 = m2 ∪ m3 →
  m0 ##ₘ m1 →
  m2 ##ₘ m3 →
  dom m0 = dom m2 →
  dom m1 = dom m3 →
  m0 = m2 ∧ m1 = m3.
Proof.
  intros. split; apply map_eq; intros ?;
    opose proof (proj1 (map_eq_iff _ _) H i).
  - destruct (m0 !! i) eqn:?.
    + erewrite lookup_union_Some_l in H4; [|done].
      destruct (m2 !! i) eqn:?; [by simpl_map|].
      apply elem_of_dom_2 in Heqo.
      apply not_elem_of_dom in Heqo0.
      set_solver.
    + erewrite lookup_union_r in H4; [|done].
      destruct (m2 !! i) eqn:?; [|done].
      apply elem_of_dom_2 in Heqo0.
      apply not_elem_of_dom in Heqo.
      set_solver.
  - destruct (m1 !! i) eqn:?.
    + erewrite lookup_union_Some_r in H4; [|done..].
      destruct (m3 !! i) eqn:?; [by simpl_map|].
      apply elem_of_dom_2 in Heqo.
      apply not_elem_of_dom in Heqo0.
      set_solver.
    + erewrite lookup_union_l in H4; [|done].
      destruct (m3 !! i) eqn:?; [|done].
      apply elem_of_dom_2 in Heqo0.
      apply not_elem_of_dom in Heqo.
      set_solver.
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

Lemma is_merkle_map_det m dig0 dig1 :
  is_merkle_map m dig0 -∗
  is_merkle_map m dig1 -∗
  ⌜ dig0 = dig1 ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1". subst.
  opose proof (tree_to_map_det _ _ _ _ _ _ _) as ->; [done..|].
  by iDestruct (is_tree_hash_det with "Htree_hash0 Htree_hash1") as %?.
Qed.

(* Program proof defs. *)

Fixpoint own_merkle_tree ptr t d : iProp Σ :=
  ∃ hash,
  "#Htree_hash" ∷ is_tree_hash t hash ∗
  match t with
  | Empty =>
    "%Heq_ptr" ∷ ⌜ ptr = null ⌝
  | Leaf label val =>
    ∃ sl_hash sl_label sl_val,
    "#Hsl_hash" ∷ own_slice_small sl_hash byteT DfracDiscarded hash ∗
    "Hptr_hash" ∷ ptr ↦[node :: "hash"]{d} (slice_val sl_hash) ∗
    "Hptr_child0" ∷ ptr ↦[node :: "child0"]{d} #null ∗
    "Hptr_child1" ∷ ptr ↦[node :: "child1"]{d} #null ∗
    "#Hsl_label" ∷ own_slice_small sl_label byteT DfracDiscarded label ∗
    "Hptr_label" ∷ ptr ↦[node :: "label"]{d} (slice_val sl_label) ∗
    "#Hsl_val" ∷ own_slice_small sl_val byteT DfracDiscarded val ∗
    "Hptr_val" ∷ ptr ↦[node :: "val"]{d} (slice_val sl_val)
  | Inner child0 child1 =>
    ∃ sl_hash ptr_child0 ptr_child1,
    "#Hsl_hash" ∷ own_slice_small sl_hash byteT DfracDiscarded hash ∗
    "Hptr_hash" ∷ ptr ↦[node :: "hash"]{d} (slice_val sl_hash) ∗
    "Hown_child0" ∷ own_merkle_tree ptr_child0 child0 d ∗
    "Hptr_child0" ∷ ptr ↦[node :: "child0"]{d} #ptr_child0 ∗
    "Hown_child1" ∷ own_merkle_tree ptr_child1 child1 d ∗
    "Hptr_child1" ∷ ptr ↦[node :: "child1"]{d} #ptr_child1 ∗
    "%Heq_children" ∷ ⌜ ptr_child0 ≠ null ∨ ptr_child1 ≠ null ⌝
  | Cut _ => False
  end.

Global Instance own_merkle_tree_fractional ptr t :
  Fractional (λ q, own_merkle_tree ptr t (DfracOwn q)).
Proof.
  intros ??. iSplit.
  - iIntros "H".
    iInduction t as [| ? | ? IH0 ? IH1 | ?] forall (ptr);
      iNamed "H"; [..|done].
    + iNamed "Htree_hash". iFrame "#%".
    + iNamed "H".
      iDestruct "Hptr_hash" as "[H2 H3]".
      iDestruct "Hptr_child0" as "[H4 H5]".
      iDestruct "Hptr_child1" as "[H6 H7]".
      iDestruct "Hptr_label" as "[H8 H9]".
      iDestruct "Hptr_val" as "[H10 H11]".
      iSplitL "H2 H4 H6 H8 H10"; iFrame "∗#".
    + fold own_merkle_tree. iNamed "H".
      iDestruct "Hptr_hash" as "[H2 H3]".
      iDestruct "Hptr_child0" as "[H4 H5]".
      iDestruct "Hptr_child1" as "[H6 H7]".
      iDestruct ("IH0" with "Hown_child0") as "[H8 H9]".
      iDestruct ("IH1" with "Hown_child1") as "[H10 H11]".
      iSplitL "H2 H4 H6 H8 H10"; iFrame "∗#%".
  - iIntros "[H0 H1]".
    iInduction t as [| ? | ? IH0 ? IH1 | ?] forall (ptr);
      iNamedSuffix "H0" "0"; iNamedSuffix "H1" "1"; [..|done].
    + iFrame "#%".
    + iNamedSuffix "H0" "0". iNamedSuffix "H1" "1".
      iDestruct (struct_field_pointsto_agree with
        "Hptr_hash0 Hptr_hash1") as %?.
      iDestruct (struct_field_pointsto_agree with
        "Hptr_label0 Hptr_label1") as %?.
      iDestruct (struct_field_pointsto_agree with
        "Hptr_val0 Hptr_val1") as %?.
      destruct sl_hash, sl_hash0, sl_label, sl_label0, sl_val, sl_val0.
      simplify_eq/=.
      iDestruct (own_slice_small_agree with "Hsl_hash0 Hsl_hash1") as %->.
      iCombine "Hptr_hash0 Hptr_hash1" as "H1".
      iCombine "Hptr_child00 Hptr_child01" as "H2".
      iCombine "Hptr_child10 Hptr_child11" as "H3".
      iCombine "Hptr_label0 Hptr_label1" as "H4".
      iCombine "Hptr_val0 Hptr_val1" as "H5".
      iFrame "∗#%".
    + fold own_merkle_tree.
      iNamedSuffix "H0" "0". iNamedSuffix "H1" "1".
      iDestruct (struct_field_pointsto_agree with
        "Hptr_hash0 Hptr_hash1") as %?.
      iDestruct (struct_field_pointsto_agree with
        "Hptr_child00 Hptr_child01") as %?.
      iDestruct (struct_field_pointsto_agree with
        "Hptr_child10 Hptr_child11") as %?.
      destruct sl_hash, sl_hash0, ptr_child0, ptr_child2, ptr_child1, ptr_child3.
      simplify_eq/=.
      iDestruct (own_slice_small_agree with "Hsl_hash0 Hsl_hash1") as %->.
      iCombine "Hptr_hash0 Hptr_hash1" as "H1".
      iCombine "Hptr_child00 Hptr_child01" as "H2".
      iCombine "Hptr_child10 Hptr_child11" as "H3".
      iDestruct ("IH0" with "Hown_child00 Hown_child01") as "H4".
      iDestruct ("IH1" with "Hown_child10 Hown_child11") as "H5".
      iFrame "∗#%".
Qed.

Global Instance own_merkle_tree_as_fractional ptr t q :
  AsFractional (own_merkle_tree ptr t (DfracOwn q))
    (λ q, own_merkle_tree ptr t (DfracOwn q)) q.
Proof. split; [auto|apply _]. Qed.

Definition own_merkle_map_aux ptr m depth d : iProp Σ :=
  ∃ t,
  "%Heq_tree_map" ∷ ⌜ m = tree_to_map t ⌝ ∗
  "%Hsorted" ∷ ⌜ sorted_tree t depth ⌝ ∗
  "%Hminimal" ∷ ⌜ minimal_tree t ⌝ ∗
  "Hown_tree" ∷ own_merkle_tree ptr t d.

Definition own_merkle_map ptr m d : iProp Σ :=
  own_merkle_map_aux ptr m (W64 0) d.

Lemma own_merkle_tree_cutless ptr t d :
  own_merkle_tree ptr t d -∗
  ⌜ cutless_tree t ⌝.
Proof.
  iIntros "H".
  iInduction t as [| ? | ? IH0 ? IH1 | ?] forall (ptr); iNamed "H"; [..|done].
  - iPureIntro. constructor.
  - iPureIntro. constructor.
  - fold own_merkle_tree. iNamed "H".
    iDestruct ("IH0" with "Hown_child0") as %?.
    iDestruct ("IH1" with "Hown_child1") as %?.
    iPureIntro. by constructor.
Qed.

Lemma own_merkle_map_to_is_merkle_map ptr m d:
  own_merkle_map ptr m d -∗
  ∃ h,
  is_merkle_map m h.
Proof.
  iNamed 1. destruct t;
    iDestruct (own_merkle_tree_cutless with "Hown_tree") as %?;
    iNamed "Hown_tree"; [..|done]; iFrame "%#".
Qed.

Lemma own_empty_tree t d :
  own_merkle_tree null t d -∗
  ⌜ t = Empty ⌝.
Proof.
  iIntros "H". destruct t; [done|..];
    iNamed "H"; [..|done]; iNamed "H";
    by iDestruct (struct_field_pointsto_not_null with "Hptr_hash") as %?.
Qed.

Lemma own_merkle_map_not_nil ptr elems depth d :
  elems ≠ ∅ →
  own_merkle_map_aux ptr elems depth d -∗
  ⌜ ptr ≠ null ⌝.
Proof.
  intros ?. iNamed 1.
  destruct t; [done|..]; iNamed "Hown_tree"; [..|done]; iNamed "Hown_tree";
    by iDestruct (struct_field_pointsto_not_null with "Hptr_hash") as %?.
Qed.

Lemma own_merkle_tree_to_hash ptr t d :
  own_merkle_tree ptr t d -∗
  ∃ dig, is_tree_hash t dig.
Proof. destruct t; iNamed 1; iFrame "#". Qed.

Definition own_context ptr d : iProp Σ :=
  ∃ sl_empty_hash empty_hash,
  "Hptr_empty_hash" ∷ ptr ↦[context :: "emptyHash"]{d} (slice_val sl_empty_hash) ∗
  "#Hsl_empty_hash" ∷ own_slice_small sl_empty_hash byteT DfracDiscarded empty_hash ∗
  "#His_empty_hash" ∷ is_hash [empty_node_tag] empty_hash.

Global Instance own_context_fractional ptr :
  Fractional (λ q, own_context ptr (DfracOwn q)).
Proof.
  intros ??. iSplit.
  - iNamed 1.
    iDestruct "Hptr_empty_hash" as "[H0 H1]".
    iSplitL "H0"; iFrame "∗#".
  - iIntros "[H0 H1]". iNamedSuffix "H0" "0". iNamedSuffix "H1" "1".
    iDestruct (struct_field_pointsto_agree with
      "Hptr_empty_hash0 Hptr_empty_hash1") as %Heq.
    destruct sl_empty_hash, sl_empty_hash0. simplify_eq/=.
    iCombine "Hptr_empty_hash0 Hptr_empty_hash1" as "H0".
    iDestruct (own_slice_small_agree with "Hsl_empty_hash0 Hsl_empty_hash1") as %->.
    iFrame "∗#".
Qed.

Global Instance own_context_as_fractional ptr q :
  AsFractional (own_context ptr (DfracOwn q)) (λ q, own_context ptr (DfracOwn q)) q.
Proof. split; [auto|apply _]. Qed.

Lemma own_context_to_null_tree ptr_ctx d0 :
  own_context ptr_ctx d0 -∗
  (own_context ptr_ctx d0 ∗ own_merkle_tree null Empty (DfracOwn 1)).
Proof. iNamed 1. by iFrame "∗#". Qed.

Definition own_Tree ptr elems d : iProp Σ :=
  ∃ ptr_ctx ptr_map,
  "Hown_ctx" ∷ own_context ptr_ctx d ∗
  "Hptr_ctx" ∷ ptr ↦[Tree :: "ctx"]{d} #ptr_ctx ∗
  "Hown_map" ∷ own_merkle_map ptr_map elems d ∗
  "Hptr_root" ∷ ptr ↦[Tree :: "root"]{d} #ptr_map.

Global Instance own_Tree_fractional ptr elems :
  Fractional (λ q, own_Tree ptr elems (DfracOwn q)).
Proof.
  intros ??. iSplit.
  - iNamed 1.
    iDestruct "Hown_ctx" as "[H0 H1]".
    iDestruct "Hptr_ctx" as "[H2 H3]".
    iNamed "Hown_map".
    iDestruct "Hown_tree" as "[H4 H5]".
    iDestruct "Hptr_root" as "[H6 H7]".
    iSplitL "H0 H2 H4 H6"; iFrame "∗%".
  - iIntros "[H0 H1]".
    iNamedSuffix "H0" "0". iNamedSuffix "H1" "1".
    iDestruct (struct_field_pointsto_agree with
      "Hptr_ctx0 Hptr_ctx1") as %?.
    iDestruct (struct_field_pointsto_agree with
      "Hptr_root0 Hptr_root1") as %?.
    destruct ptr_ctx, ptr_ctx0, ptr_map, ptr_map0.
    simplify_eq/=.
    iCombine "Hown_ctx0 Hown_ctx1" as "H0".
    iCombine "Hptr_ctx0 Hptr_ctx1" as "H1".
    iCombine "Hptr_root0 Hptr_root1" as "H2".
    iNamedSuffix "Hown_map0" "0".
    iNamedSuffix "Hown_map1" "1".
    iDestruct (own_merkle_tree_cutless with "Hown_tree0") as %?.
    iDestruct (own_merkle_tree_cutless with "Hown_tree1") as %?.
    subst.
    opose proof (tree_to_map_det Heq_tree_map1 _ _ _ _ _ _) as ->; [done..|].
    iCombine "Hown_tree0 Hown_tree1" as "H3".
    iFrame "∗%".
Qed.

Global Instance own_Tree_as_fractional ptr elems q :
  AsFractional (own_Tree ptr elems (DfracOwn q))
    (λ q, own_Tree ptr elems (DfracOwn q)) q.
Proof. split; [auto|apply _]. Qed.

(* Program proofs. *)

Lemma wp_compEmptyHash :
  {{{ True }}}
  compEmptyHash #()
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "Hsl_hash" ∷ own_slice sl_hash byteT (DfracOwn 1) hash ∗
    "#His_hash" ∷ is_hash [empty_node_tag] hash
  }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  wp_apply (wp_SliceSingleton _ _ _ (W8 _)).
  iIntros "* H".
  iDestruct (own_slice_to_small with "H") as "H".
  wp_apply (wp_Hash with "[$H]").
  iIntros "*". iNamed 1.
  iApply "HΦ". iFrame "∗#".
Qed.

Lemma wp_getNodeHash ptr_tr t d0 ptr_ctx d1 :
  {{{
    "Hown_tree" ∷ own_merkle_tree ptr_tr t d0 ∗
    "Hown_ctx" ∷ own_context ptr_ctx d1
  }}}
  getNodeHash #ptr_tr #ptr_ctx
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "Hown_tree" ∷ own_merkle_tree ptr_tr t d0 ∗
    "Hown_ctx" ∷ own_context ptr_ctx d1 ∗
    "#Hsl_hash" ∷ own_slice_small sl_hash byteT DfracDiscarded hash ∗
    "#Htree_hash" ∷ is_tree_hash t hash
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  iNamed "Hown_ctx".
  wp_if_destruct.
  { wp_loadField.
    iDestruct (own_empty_tree with "Hown_tree") as %->.
    iApply "HΦ". iFrame "∗#". }
  destruct t; iNamed "Hown_tree"; [done|..|done].
  - iNamed "Hown_tree". wp_loadField.
    iApply "HΦ". iFrame "∗#".
  - fold own_merkle_tree. iNamed "Hown_tree". wp_loadField.
    iApply "HΦ". iFrame "∗#%".
Qed.

Lemma wp_NewTree :
  {{{ True }}}
  NewTree #()
  {{{
    ptr, RET #ptr;
    "Hown_Tree" ∷ own_Tree ptr ∅ (DfracOwn 1)
  }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  wp_apply wp_compEmptyHash.
  iIntros "*". iNamed 1.
  iDestruct (own_slice_to_small with "Hsl_hash") as "Hsl_hash".
  iPersist "Hsl_hash".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros "* Hptr_ctx".
  iDestruct (struct_fields_split with "Hptr_ctx") as "H". iNamed "H".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros "* Hptr_Tree".
  iDestruct (struct_fields_split with "Hptr_Tree") as "H". iNamed "H".
  iApply "HΦ". iFrame "∗#".
  iExists Empty. repeat iSplit; try done. by iFrame "#".
Qed.

Lemma wp_Tree__Digest ptr elems d0 :
  {{{
    "Hown_Tree" ∷ own_Tree ptr elems d0
  }}}
  Tree__Digest #ptr
  {{{
    sl_dig dig, RET (slice_val sl_dig);
    "Hown_Tree" ∷ own_Tree ptr elems d0 ∗
    "#His_dig" ∷ is_merkle_map elems dig
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  iNamed "Hown_Tree". iNamed "Hown_map".
  do 2 wp_loadField.
  wp_apply (wp_getNodeHash with "[$Hown_tree $Hown_ctx]").
  iIntros "*". iNamed 1.
  iDestruct (own_merkle_tree_cutless with "Hown_tree") as %?.
  iApply "HΦ". iFrame "∗#%".
Qed.

Lemma wp_compLeafHash sl_label sl_val d0 d1 (label val : list w8) :
  {{{
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hsl_val" ∷ own_slice_small sl_val byteT d1 val
  }}}
  compLeafHash (slice_val sl_label) (slice_val sl_val)
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hsl_val" ∷ own_slice_small sl_val byteT d1 val ∗
    "Hsl_hash" ∷ own_slice sl_hash byteT (DfracOwn 1) hash ∗
    "#His_hash" ∷ is_hash
      (leaf_node_tag ::
      (u64_le_seal $ length label) ++ label ++
      (u64_le_seal $ length val) ++ val) hash
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  iDestruct (own_slice_small_sz with "Hsl_label") as %?.
  iDestruct (own_slice_small_sz with "Hsl_val") as %?.
  wp_apply wp_NewHasher.
  iIntros "*". iNamed 1.
  wp_apply (wp_SliceSingleton _ _ _ (W8 _)).
  iIntros "* H".
  iDestruct (own_slice_to_small with "H") as "H".
  wp_apply (wp_Hasher__Write with "[$Hown_hr $H]").
  iNamedSuffix 1 "0". wp_apply wp_slice_len.
  wp_apply (wp_WriteInt Slice.nil with "[]").
  { iApply own_slice_zero. }
  iIntros "* H".
  iDestruct (own_slice_to_small with "H") as "H".
  wp_apply (wp_Hasher__Write with "[$Hown_hr0 $H]").
  iNamedSuffix 1 "1".
  wp_apply (wp_Hasher__Write with "[$Hown_hr1 $Hsl_label]").
  iNamedSuffix 1 "2". wp_apply wp_slice_len.
  wp_apply (wp_WriteInt Slice.nil with "[]").
  { iApply own_slice_zero. }
  iIntros "* H".
  iDestruct (own_slice_to_small with "H") as "H".
  wp_apply (wp_Hasher__Write with "[$Hown_hr2 $H]").
  iNamedSuffix 1 "3".
  wp_apply (wp_Hasher__Write with "[$Hown_hr3 $Hsl_val]").
  iNamedSuffix 1 "4".
  wp_apply (wp_Hasher__Sum Slice.nil with "[$Hown_hr4]").
  { iApply own_slice_zero. }
  iIntros "*". iNamedSuffix 1 "5".
  iApply "HΦ". iFrame.
  list_simplifier. rewrite u64_le_unseal.
  apply (f_equal (λ x : nat, W64 x)) in H, H0.
  rewrite !w64_to_nat_id in H H0. rewrite -H -H0.
  iFrame "#".
Qed.

Lemma wp_compInnerHash sl_child0 sl_child1 sl_hash_in d0 d1 (child0 child1 : list w8) :
  {{{
    "Hsl_child0" ∷ own_slice_small sl_child0 byteT d0 child0 ∗
    "Hsl_child1" ∷ own_slice_small sl_child1 byteT d1 child1 ∗
    "Hsl_hash_in" ∷ own_slice sl_hash_in byteT (DfracOwn 1) ([] : list w8)
  }}}
  compInnerHash (slice_val sl_child0) (slice_val sl_child1) (slice_val sl_hash_in)
  {{{
    sl_hash_out hash, RET (slice_val sl_hash_out);
    "Hsl_child0" ∷ own_slice_small sl_child0 byteT d0 child0 ∗
    "Hsl_child1" ∷ own_slice_small sl_child1 byteT d1 child1 ∗
    "Hsl_hash_out" ∷ own_slice sl_hash_out byteT (DfracOwn 1) hash ∗
    "#His_hash" ∷ is_hash (inner_node_tag :: child0 ++ child1) hash
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_NewHasher.
  iIntros "*". iNamed 1.
  wp_apply (wp_SliceSingleton _ _ _ (W8 _)).
  iIntros "* H".
  iDestruct (own_slice_to_small with "H") as "H".
  wp_apply (wp_Hasher__Write with "[$Hown_hr $H]").
  iNamedSuffix 1 "0".
  wp_apply (wp_Hasher__Write with "[$Hown_hr0 $Hsl_child0]").
  iNamedSuffix 1 "1".
  wp_apply (wp_Hasher__Write with "[$Hown_hr1 $Hsl_child1]").
  iNamedSuffix 1 "2".
  wp_apply (wp_Hasher__Sum with "[$Hown_hr2 $Hsl_hash_in]").
  iIntros "*". iNamed 1.
  list_simplifier.
  iApply "HΦ". iFrame "∗#".
Qed.

Lemma length_bytes_to_bits b :
  length (bytes_to_bits b) = (8 * length b) % nat.
Proof.
  induction b; [done|].
  rewrite /= IHb. lia.
Qed.

Lemma bytes_to_bits_app a b : bytes_to_bits (a ++ b) = bytes_to_bits a ++ bytes_to_bits b.
Proof. rewrite /bytes_to_bits !fmap_app concat_app //. Qed.

Lemma LitByte_inv a b :
  LitByte a = LitByte b → a = b.
Proof. inversion 1. done. Qed.

Lemma bool_decide_w8_eq (a b : w8) :
  bool_decide (#a = #b) =
  bool_decide (uint.Z a = uint.Z b).
Proof.
  rewrite !bool_decide_decide.
  destruct decide.
  { rewrite decide_True //. naive_solver. }
  { rewrite decide_False //. naive_solver. }
Qed.

Lemma wp_getBit sl_b d0 (b : list w8) (n : w64) :
  {{{
    "Hsl_b" ∷ own_slice_small sl_b byteT d0 b
  }}}
  getBit (slice_val sl_b) #n
  {{{
    (bit : bool), RET #bit;
    "Hsl_b" ∷ own_slice_small sl_b byteT d0 b ∗
    "->" ∷ ⌜ bit = get_bit b n ⌝
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  iDestruct (own_slice_small_sz with "Hsl_b") as %?.
  wp_apply wp_slice_len. wp_if_destruct.
  - list_elem b (uint.nat (word.divu n (W64 8))) as byt.
    wp_apply (wp_SliceGet with "[$Hsl_b //]").
    iIntros "Hsl_b". wp_pures. iApply "HΦ". iFrame. iPureIntro.
    opose proof (lookup_lt_is_Some_2 (bytes_to_bits b) (uint.nat n) _) as [? ?].
    { rewrite length_bytes_to_bits. word. }
    rewrite /get_bit H0.
    clear -H0 Hbyt_lookup.
    (* XXX: could be a separate lemma. *)
    rename H0 into Hbit_lookup.
    pose proof (lookup_lt_Some _ _ _ Hbyt_lookup) as Hn.
    apply take_drop_middle in Hbyt_lookup.
    rewrite -Hbyt_lookup in Hbit_lookup.
    rewrite !bytes_to_bits_app in Hbit_lookup.
    rewrite lookup_app_r in Hbit_lookup.
    2:{ rewrite length_bytes_to_bits length_take. word. }
    rewrite length_bytes_to_bits length_take in Hbit_lookup.
    rewrite Nat.min_l in Hbit_lookup.
    2:{ word. }
    rewrite lookup_app_l in Hbit_lookup.
    2:{ simpl. word. }
    replace (uint.nat n - 8 * (uint.nat _))%nat with
      (uint.nat n `mod` 8)%nat in Hbit_lookup.
    2:{
      rewrite -> word.unsigned_divu_nowrap in * by word.
      rewrite -> (Nat.div_mod_eq (uint.nat n) 8) at 2.
      rewrite -> Z2Nat.inj_div by word.
      replace (uint.nat (W64 8)) with 8%nat by word.
      lia.
    }
    rewrite /byte_to_bits list_lookup_fmap in Hbit_lookup.
    rewrite lookup_seqZ_lt in Hbit_lookup.
    2:{
      replace 8 with (Z.of_nat 8%nat) by done.
      rewrite <- Nat2Z.inj_lt.
      by apply Nat.mod_upper_bound.
    }
    rewrite Nat2Z.inj_mod left_id /= in Hbit_lookup.
    injection Hbit_lookup as ?. subst.
    replace (uint.nat n `mod` 8%nat) with (uint.Z n `mod` 8) by word.
    rewrite bool_decide_w8_eq.
    rewrite -> word.unsigned_and_nowrap, word.unsigned_modu_nowrap, Automation.word.unsigned_slu' by word.
    rewrite left_id.
    replace (2^_) with (2^(uint.Z n `mod` 8)).
    2:{ f_equal. word. }
    rewrite wrap_small.
    2:{ split; first lia. apply Z.pow_lt_mono_r; word. }
    rewrite bool_decide_decide. destruct decide as [H|H].
    + apply (f_equal (λ x, Z.testbit x (uint.Z n `mod` 8))) in H.
      rewrite Z.land_spec Z.bits_0 /= in H.
      rewrite -> Z.pow2_bits_true in H by word.
      rewrite andb_true_r // in H.
    + simpl. apply Automation.word.decision_assume_opposite.
      intros H2. apply H. clear H. rename H2 into H.
      apply Z.bits_inj_iff. intros p.
      rewrite Z.land_spec Z.bits_0 /=.
      destruct (decide (p = (uint.Z n `mod` 8))).
      {
        subst. rewrite -> Z.pow2_bits_true by word. rewrite andb_true_r.
        destruct Z.testbit; done.
      }
      rewrite -> Z.pow2_bits_false by word.
      rewrite andb_false_r. done.
  - iApply "HΦ". iFrame. iPureIntro.
    rewrite /get_bit lookup_ge_None_2; [done|].
    rewrite length_bytes_to_bits. word.
Qed.

Lemma wp_getChild n d0 ptr_child0 ptr_child1 sl_label d1
    (label : list w8) (depth : w64) :
  {{{
    "Hptr_child0" ∷ n ↦[node :: "child0"]{d0} #ptr_child0 ∗
    "Hptr_child1" ∷ n ↦[node :: "child1"]{d0} #ptr_child1 ∗
    "Hsl_label" ∷ own_slice_small sl_label byteT d1 label
  }}}
  getChild #n (slice_val sl_label) #depth
  {{{
    ptr2_child_b ptr_child_nb, RET (#ptr2_child_b, #ptr_child_nb);
    if get_bit label depth
      then
      "->" ∷ ⌜ ptr_child_nb = ptr_child0 ⌝ ∗
      "Hptr_child0" ∷ n ↦[node :: "child0"]{d0} #ptr_child0 ∗
      "Hptr2_child1" ∷ ptr2_child_b ↦[ptrT]{d0} #ptr_child1 ∗
      "Hclose_child1" ∷ (∀ v, ptr2_child_b ↦[ptrT]{d0} #v -∗ n ↦[node :: "child1"]{d0} #v) ∗
      "Hsl_label" ∷ own_slice_small sl_label byteT d1 label
      else
      "->" ∷ ⌜ ptr_child_nb = ptr_child1 ⌝ ∗
      "Hptr_child1" ∷ n ↦[node :: "child1"]{d0} #ptr_child1 ∗
      "Hptr2_child0" ∷ ptr2_child_b ↦[ptrT]{d0} #ptr_child0 ∗
      "Hclose_child0" ∷ (∀ v,
        ptr2_child_b ↦[ptrT]{d0} #v -∗ n ↦[node :: "child0"]{d0} #v) ∗
      "Hsl_label" ∷ own_slice_small sl_label byteT d1 label
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply (wp_getBit with "[$Hsl_label]").
  iIntros "*". iNamed 1.
  wp_if_destruct.
  - wp_apply (wp_struct_fieldRef_pointsto with "[$Hptr_child0]"); [done|].
    iIntros "* [%Hclose H]". wp_loadField. wp_pures. rewrite Heqb.
    iApply "HΦ". iFrame. iIntros "!>". iSplit; [done|].
    iIntros (v) "H". specialize (Hclose #v).
    by iApply Hclose.
  - wp_apply (wp_struct_fieldRef_pointsto with "[$Hptr_child1]"); [done|].
    iIntros "* [%Hclose H]". wp_loadField. wp_pures. rewrite Heqb.
    iApply "HΦ". iFrame. iIntros "!>". iSplit; [done|].
    iIntros (v) "H". specialize (Hclose #v).
    by iApply Hclose.
Qed.

Lemma wp_getProofLen (depth : w64) :
  {{{ True }}}
  getProofLen #depth
  {{{
    (len : w64), RET #len;
    "%Hlt_len" ∷ ⌜ 8 <= uint.Z len ⌝
  }}}.
Proof. iIntros (Φ) "_ HΦ". wp_rec. wp_pures. iApply "HΦ". word. Qed.

Lemma wp_find sl_label d0 (label : list w8) ptr_ctx d1 ptr_n t (get_proof : bool) (depth : w64) :
  {{{
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hown_ctx" ∷ own_context ptr_ctx d1 ∗
    "Hown_tree" ∷ own_merkle_tree ptr_n t d1
  }}}
  find (slice_val sl_label) #get_proof #ptr_ctx #ptr_n #depth
  {{{
    sl_fd_label sl_fd_val sl_proof (found : bool) fd_label fd_val proof,
    RET (#found, slice_val sl_fd_label, slice_val sl_fd_val, slice_val sl_proof);
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hown_ctx" ∷ own_context ptr_ctx d1 ∗
    "Hown_tree" ∷ own_merkle_tree ptr_n t d1 ∗
    "#Hsl_fd_label" ∷ own_slice_small sl_fd_label byteT DfracDiscarded fd_label ∗
    "#Hsl_fd_val" ∷ own_slice_small sl_fd_val byteT DfracDiscarded fd_val ∗
    "Hsl_proof" ∷ own_slice sl_proof byteT (DfracOwn 1) proof ∗

    "%Hpath" ∷ ⌜ tree_path t label depth
      (if found then (Some (fd_label, fd_val)) else None) ⌝ ∗
    "Hproof" ∷ (if negb get_proof then True else
      ∃ x sibs,
      "%Henc_proof" ∷ ⌜ proof = x ++ sibs ⌝ ∗
      "%Hlen_x" ∷ ⌜ length x = 8%nat ⌝ ∗
      "#Hsibs_proof" ∷ tree_sibs_proof t label depth sibs)
  }}}.
Proof.
  iLöb as "IH" forall (ptr_n t depth).
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_if_destruct.
  { (* empty node. *)
    iDestruct (own_empty_tree with "Hown_tree") as %->.
    wp_apply wp_ref_of_zero; [done|].
    iIntros "* Hptr_proof".
    wp_if_destruct.
    - wp_apply wp_getProofLen. iIntros "*". iNamed 1.
      wp_apply wp_NewSliceWithCap; [word|].
      iIntros "* Hsl_proof". wp_store. wp_load.
      iDestruct (own_slice_zero _ (DfracOwn 1)) as "H0".
      iDestruct (own_slice_to_small with "H0") as "H1".
      iPersist "H1".

      wp_pures. iApply ("HΦ" $! Slice.nil Slice.nil).
      iFrame "∗#". iIntros "!>". iSplit; [done|].
      iExists _, [].
      iSplit; [by list_simplifier|].
      iSplit; [by rewrite length_replicate|done].

    - iDestruct own_slice_zero as "H0".
      iDestruct (own_slice_to_small with "H0") as "H1".
      iPersist "H1".
      wp_load. wp_pures. iApply ("HΦ" $! Slice.nil Slice.nil Slice.nil).
      by iFrame "∗#". }

  iRename "Hsl_label" into "Hsl_label_find".
  destruct t; iNamed "Hown_tree"; [done|..|done];
    iNamed "Hown_tree"; fold own_merkle_tree.
  { (* leaf node. *)
    wp_bind (If _ _ #false).
    wp_apply (wp_wand _ _ _
      (λ ret,
      "->" ∷ ⌜ ret = #true ⌝ ∗
      "Hptr_child0" ∷ ptr_n ↦[node::"child0"]{d1} #null ∗
      "Hptr_child1" ∷ ptr_n ↦[node::"child1"]{d1} #null
      )%I
      with "[Hptr_child0 Hptr_child1]"
    ).
    { do 2 wp_loadField. wp_pures. by iFrame. }
    iIntros "*". iNamed 1.
    wp_pures.

    wp_apply wp_ref_of_zero; [done|].
    iIntros "* Hptr_proof".
    wp_if_destruct.
    - wp_apply wp_getProofLen. iIntros "*". iNamed 1.
      wp_apply wp_NewSliceWithCap; [word|].
      iIntros "* Hsl_proof". wp_store. do 2 wp_loadField. wp_load.

      wp_pures. iApply "HΦ".
      iFrame "Hown_ctx ∗#". iIntros "!>". iSplit; [done|].
      iExists _, [].
      iSplit; [by list_simplifier|].
      iSplit; [by rewrite length_replicate|done].

    - iDestruct own_slice_zero as "H0".
      do 2 wp_loadField. wp_load.
      wp_pures. iApply ("HΦ" $! _ _ Slice.nil).
      by iFrame "∗#". }

  (* inner node. *)
  wp_bind (If _ _ #false).
  wp_apply (wp_wand _ _ _
    (λ ret,
    "->" ∷ ⌜ ret = #false ⌝ ∗
    "Hptr_child0" ∷ ptr_n ↦[node::"child0"]{d1} #ptr_child0 ∗
    "Hptr_child1" ∷ ptr_n ↦[node::"child1"]{d1} #ptr_child1
    )%I
    with "[Hptr_child0 Hptr_child1]"
  ).
  { wp_loadField. wp_if_destruct.
    - wp_loadField. wp_pures. iFrame. iPureIntro.
      case_bool_decide; naive_solver.
    - by iFrame. }
  iIntros "*". iNamed 1. wp_pures.
  wp_apply (wp_getChild with "[$Hptr_child0 $Hptr_child1 $Hsl_label_find]").
  iIntros "* H". wp_pures.

  destruct (get_bit _ _) eqn:Heq_bit; iNamed "H".
  - wp_load.
    wp_apply ("IH" with "[$Hsl_label $Hown_ctx $Hown_child1]").
    iIntros "*". iNamedSuffix 1 "1".
    wp_apply wp_ref_to; [done|]. iIntros "* Hptr_proof".
    wp_if_destruct.
    + iNamed "Hproof1".
      wp_apply (wp_getNodeHash with "[$Hown_child0 $Hown_ctx1]").
      iIntros "*". iNamedSuffix 1 "0". wp_load.
      wp_apply (wp_SliceAppendSlice with "[$Hsl_proof1 $Hsl_hash0]"); [done|].
      iIntros "* [Hsl_proof _]". wp_store. wp_load.
      iDestruct ("Hclose_child1" with "Hptr2_child1") as "Hptr_child1".
      wp_pures. iApply "HΦ". iFrame "Hown_ctx0 ∗ Htree_hash #".
      iIntros "!>". iSplit; [done|].
      iSplit. { simpl. by rewrite Heq_bit. }
      iExists x, (sibs ++ hash0).
      iSplit; [by list_simplifier|].
      iSplit; [done|].
      iExists _, _. fold tree_sibs_proof.
      iSplit; [done|].
      rewrite Heq_bit. naive_solver.

    + wp_load.
      iDestruct ("Hclose_child1" with "Hptr2_child1") as "Hptr_child1".
      wp_pures. iApply "HΦ". iFrame "Hown_ctx1 ∗#".
      iIntros "!>". iSplit; [done|].
      simpl. by rewrite Heq_bit.

  - wp_load.
    wp_apply ("IH" with "[$Hsl_label $Hown_ctx $Hown_child0]").
    iIntros "*". iNamedSuffix 1 "0".
    wp_apply wp_ref_to; [done|]. iIntros "* Hptr_proof".
    wp_if_destruct.
    + iNamed "Hproof0".
      wp_apply (wp_getNodeHash with "[$Hown_child1 $Hown_ctx0]").
      iIntros "*". iNamedSuffix 1 "1". wp_load.
      wp_apply (wp_SliceAppendSlice with "[$Hsl_proof0 $Hsl_hash1]"); [done|].
      iIntros "* [Hsl_proof _]". wp_store. wp_load.
      iDestruct ("Hclose_child0" with "Hptr2_child0") as "Hptr_child0".
      wp_pures. iApply "HΦ". iFrame "Hown_ctx1 ∗ Htree_hash #".
      iIntros "!>". iSplit; [done|].
      iSplit. { simpl. by rewrite Heq_bit. }
      iExists x, (sibs ++ hash0).
      iSplit; [by list_simplifier|].
      iSplit; [done|].
      iExists _, _. fold tree_sibs_proof.
      iSplit; [done|].
      rewrite Heq_bit. naive_solver.

    + wp_load.
      iDestruct ("Hclose_child0" with "Hptr2_child0") as "Hptr_child0".
      wp_pures. iApply "HΦ". iFrame "Hown_ctx0 ∗ Htree_hash #".
      iIntros "!>". iSplit; [done|].
      simpl. by rewrite Heq_bit.
Qed.

Lemma wp_UInt64Put' s x vs :
  length vs >= w64_bytes →
  {{{
    own_slice_small s byteT (DfracOwn 1) vs
  }}}
  UInt64Put (slice_val s) #x
  {{{
    RET #();
    own_slice_small s byteT (DfracOwn 1) (u64_le x ++ (drop w64_bytes vs))
  }}}.
Proof.
  iIntros (? Φ) "Hsl HΦ".
  wp_apply (wp_UInt64Put with "[$Hsl]").
  { by rewrite list_untype_length. }
  iIntros "Hsl". iApply "HΦ".
  by rewrite /own_slice_small list_untype_app list_untype_drop.
Qed.

Lemma wp_Tree__prove sl_label d0 (label : list w8) ptr_t elems d1 (get_proof : bool) :
  {{{
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hown_Tree" ∷ own_Tree ptr_t elems d1
  }}}
  Tree__prove #ptr_t (slice_val sl_label) #get_proof
  {{{
    sl_val sl_proof (in_tree : bool) (val proof : list w8) dig,
    RET (#in_tree, slice_val sl_val, slice_val sl_proof);
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hown_Tree" ∷ own_Tree ptr_t elems d1 ∗
    "#Hsl_val" ∷ own_slice_small sl_val byteT DfracDiscarded val ∗
    "Hsl_proof" ∷ own_slice_small sl_proof byteT (DfracOwn 1) proof ∗
    "#His_dig" ∷ is_merkle_map elems dig ∗
    "#Hmemb" ∷ is_merkle_entry label (if in_tree then Some val else None) dig ∗
    "#Hwish" ∷ (if negb get_proof then True else wish_merkle_Verify in_tree label val proof dig)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  iNamed "Hown_Tree". iNamed "Hown_map". do 2 wp_loadField.
  wp_apply (wp_find with "[$Hsl_label $Hown_ctx $Hown_tree]").
  iIntros "*". iNamed 1.
  wp_apply wp_ref_to; [done|]. iIntros "* Hptr_proof".
  wp_pures. wp_bind (If _ _ _).
  wp_apply (wp_wand _ _ _
    (λ _,
    ∃ proof',
    "Hsl_proof" ∷ own_slice sl_proof byteT (DfracOwn 1) proof' ∗
    "Hptr_proof" ∷ l ↦[slice.T byteT] sl_proof ∗
    "Hproof" ∷ if negb get_proof
      then True
      else
      ∃ sibs : list w8, "%Henc_proof" ∷ ⌜proof' = u64_le (W64 $ length sibs) ++ sibs⌝ ∗
        "#Hsibs_proof" ∷ tree_sibs_proof t label (W64 0) sibs
    )%I
    with "[Hproof Hptr_proof Hsl_proof]"
  ).
  { iDestruct (own_slice_sz with "Hsl_proof") as "%Hlen_proof".
    wp_if_destruct.
    - iNamed "Hproof". wp_load. wp_apply wp_slice_len. wp_load.
      iDestruct (own_slice_small_acc with "[$Hsl_proof]") as "[Hsl_proof Hclose]".
      wp_apply (wp_UInt64Put' with "[$Hsl_proof]").
      { apply (f_equal length) in Henc_proof.
        rewrite length_app in Henc_proof. word. }
      iIntros "Hsl_proof".
      iDestruct ("Hclose" with "Hsl_proof") as "Hsl_proof".
      iFrame "∗#". iPureIntro.
      rewrite Henc_proof. list_simplifier.
      apply app_inv_tail_iff.
      rewrite length_app in Hlen_proof.
      f_equal. word.
    - by iFrame. }
  iIntros (tmp). iNamed 1. wp_pures. clear tmp.

  wp_if_destruct.
  { wp_if_destruct.
    - iNamed "Hproof". wp_load.
      wp_apply (wp_WriteBool with "[$Hsl_proof]").
      iIntros "* Hsl". wp_store. wp_load.
      wp_apply (wp_WriteInt with "[$Hsl]").
      iIntros "* Hsl". wp_store. wp_load.
      wp_apply (wp_WriteInt with "[$Hsl]").
      iIntros "* Hsl_proof". wp_store. wp_load.

      iDestruct (own_slice_to_small with "Hsl_proof") as "Hsl_proof".
      iDestruct (own_slice_small_sz with "Hsl_proof") as %Hlen_proof.
      iDestruct (own_slice_zero _ (DfracOwn 1)) as "H0".
      iDestruct (own_slice_to_small with "H0") as "H1".
      iPersist "H1".
      iDestruct (own_merkle_tree_to_hash with "Hown_tree") as "[% #Htree_hash]".
      iDestruct (own_merkle_tree_cutless with "Hown_tree") as %Hcutless.

      wp_pures. iApply ("HΦ" $! Slice.nil). iFrame "∗#%".
      iIntros "!>". do 2 (iSplit; [done|]).
      iExists (MerkleProof.mk _ false [] []), _, []. simpl.
      iFrame "#". iPureIntro. split; [|by list_simplifier].
      rewrite /MerkleProof.encodes. simpl.
      apply (f_equal length) in Henc_proof.
      rewrite -!u64_le_unseal !app_length !u64_le_seal_len in Henc_proof Hlen_proof |-*.
      repeat split; [word|].
      by list_simplifier.

    - wp_load.
      iDestruct (own_slice_to_small with "Hsl_proof") as "Hsl_proof".
      iDestruct (own_slice_zero _ (DfracOwn 1)) as "H0".
      iDestruct (own_slice_to_small with "H0") as "H1".
      iPersist "H1".
      iDestruct (own_merkle_tree_to_hash with "Hown_tree") as "[% #Htree_hash]".
      iDestruct (own_merkle_tree_cutless with "Hown_tree") as %Hcutless.
      wp_pures. iApply ("HΦ" $! Slice.nil). by iFrame "∗#%". }

  wp_apply (wp_BytesEqual sl_fd_label sl_label with "[$Hsl_fd_label $Hsl_label]").
  iIntros "[_ Hsl_label]".
  wp_if_destruct.
  { wp_if_destruct.
    - iNamed "Hproof". wp_load.
      wp_apply (wp_WriteBool with "[$Hsl_proof]").
      iIntros "* Hsl". wp_store. wp_apply wp_slice_len. wp_load.
      wp_apply (wp_WriteInt with "[$Hsl]").
      iIntros "* Hsl". wp_store. wp_load.
      wp_apply (wp_WriteBytes with "[$Hsl $Hsl_fd_label]").
      iIntros "* [Hsl _]". wp_store. wp_apply wp_slice_len. wp_load.
      wp_apply (wp_WriteInt with "[$Hsl]").
      iIntros "* Hsl". wp_store. wp_load.
      wp_apply (wp_WriteBytes with "[$Hsl $Hsl_fd_val]").
      iIntros "* [Hsl_proof _]". wp_store. wp_load.
      iDestruct (own_slice_small_sz with "Hsl_fd_label") as %Hlen_label.
      iDestruct (own_slice_small_sz with "Hsl_fd_val") as %Hlen_val.

      iDestruct (own_slice_to_small with "Hsl_proof") as "Hsl_proof".
      iDestruct (own_slice_small_sz with "Hsl_proof") as %Hlen_proof.
      iDestruct (own_slice_zero _ (DfracOwn 1)) as "H0".
      iDestruct (own_slice_to_small with "H0") as "H1".
      iPersist "H1".
      iDestruct (own_merkle_tree_to_hash with "Hown_tree") as "[% #Htree_hash]".
      iDestruct (own_merkle_tree_cutless with "Hown_tree") as %Hcutless.

      wp_pures. iApply ("HΦ" $! Slice.nil). iFrame "∗#%".
      iIntros "!>". do 3 (iSplit; [done|]).
      iExists (MerkleProof.mk _ true fd_label fd_val), _, []. simpl.
      iFrame "#". iPureIntro. split; [|by list_simplifier].
      rewrite /MerkleProof.encodes. simpl.
      apply (f_equal length) in Henc_proof.
      rewrite -!u64_le_unseal !app_length !u64_le_seal_len in Henc_proof Hlen_proof |-*.
      repeat split; [word..|].
      apply (f_equal (λ x : nat, W64 x)) in Hlen_label, Hlen_val.
      rewrite !w64_to_nat_id in Hlen_label Hlen_val.
      rewrite -Hlen_label -Hlen_val.
      by list_simplifier.

    - wp_load.
      iDestruct (own_slice_to_small with "Hsl_proof") as "Hsl_proof".
      iDestruct (own_slice_zero _ (DfracOwn 1)) as "H0".
      iDestruct (own_slice_to_small with "H0") as "H1".
      iPersist "H1".
      iDestruct (own_merkle_tree_to_hash with "Hown_tree") as "[% #Htree_hash]".
      iDestruct (own_merkle_tree_cutless with "Hown_tree") as %Hcutless.
      wp_pures. iApply ("HΦ" $! Slice.nil). by iFrame "∗#%". }

  subst. wp_if_destruct.
  { iNamed "Hproof". wp_load.
    wp_apply (wp_WriteBool with "[$Hsl_proof]").
    iIntros "* Hsl". wp_store. wp_load.
    wp_apply (wp_WriteInt with "[$Hsl]").
    iIntros "* Hsl". wp_store. wp_load.
    wp_apply (wp_WriteInt with "[$Hsl]").
    iIntros "* Hsl_proof". wp_store. wp_load.

    iDestruct (own_slice_to_small with "Hsl_proof") as "Hsl_proof".
    iDestruct (own_slice_small_sz with "Hsl_proof") as %Hlen_proof.
    iDestruct (own_merkle_tree_to_hash with "Hown_tree") as "[% #Htree_hash]".
    iDestruct (own_merkle_tree_cutless with "Hown_tree") as %Hcutless.

    wp_pures. iApply "HΦ". iFrame "∗#%".
    iIntros "!>". do 2 (iSplit; [done|]).
    iExists (MerkleProof.mk _ false [] []), _, []. simpl.
    iFrame "#". iPureIntro. split; [|by list_simplifier].
    rewrite /MerkleProof.encodes. simpl.
    apply (f_equal length) in Henc_proof.
    rewrite -!u64_le_unseal !app_length !u64_le_seal_len in Henc_proof Hlen_proof |-*.
    repeat split; [word|].
    by list_simplifier. }

  iDestruct (own_slice_to_small with "Hsl_proof") as "Hsl_proof".
  iDestruct (own_merkle_tree_to_hash with "Hown_tree") as "[% #Htree_hash]".
  iDestruct (own_merkle_tree_cutless with "Hown_tree") as %Hcutless.

  wp_load. wp_pures. iApply "HΦ". by iFrame "∗#%".
Qed.

Lemma wp_Tree__Get sl_label d0 (label : list w8) ptr_t elems d1 :
  {{{
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hown_Tree" ∷ own_Tree ptr_t elems d1
  }}}
  Tree__Get #ptr_t (slice_val sl_label)
  {{{
    sl_val (in_tree : bool) (val : list w8),
    RET (#in_tree, slice_val sl_val);
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hown_Tree" ∷ own_Tree ptr_t elems d1 ∗
    "#Hsl_val" ∷ own_slice_small sl_val byteT DfracDiscarded val ∗

    "%Hlook_elems" ∷ ⌜ elems !! label = (if in_tree then Some val else None) ⌝
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply (wp_Tree__prove with "[$Hsl_label $Hown_Tree]").
  iIntros "*". iNamed 1.
  wp_pures. iApply "HΦ". iFrame "∗#".
  case_match;
    by iDestruct (is_merkle_map_agree_entry with "His_dig Hmemb") as %?.
Qed.

Lemma wp_Tree__Prove sl_label d0 (label : list w8) ptr_t elems d1 :
  {{{
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hown_Tree" ∷ own_Tree ptr_t elems d1
  }}}
  Tree__Prove #ptr_t (slice_val sl_label)
  {{{
    sl_val sl_proof (in_tree : bool) (val : list w8) proof dig,
    RET (#in_tree, slice_val sl_val, slice_val sl_proof);
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hown_Tree" ∷ own_Tree ptr_t elems d1 ∗
    "#Hsl_val" ∷ own_slice_small sl_val byteT DfracDiscarded val ∗
    "Hsl_proof" ∷ own_slice_small sl_proof byteT (DfracOwn 1) proof ∗

    "#His_dig" ∷ is_merkle_map elems dig ∗
    "%Hlook_elems" ∷ ⌜ elems !! label = (if in_tree then Some val else None) ⌝ ∗
    "#Hwish" ∷ wish_merkle_Verify in_tree label val proof dig
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply (wp_Tree__prove with "[$Hsl_label $Hown_Tree]").
  iIntros "*". iNamed 1.
  wp_pures. iApply "HΦ". iFrame "∗#".
  case_match;
    by iDestruct (is_merkle_map_agree_entry with "His_dig Hmemb") as %?.
Qed.

Lemma wp_put n0 ptr_n (depth : w64) elems sl_label sl_val (label val : list w8) ptr_ctx :
  {{{
    "Hown_merkle" ∷ own_merkle_map_aux ptr_n elems depth (DfracOwn 1) ∗
    "Hptr_n0" ∷ n0 ↦[ptrT] #ptr_n ∗
    "Hsl_label" ∷ own_slice_small sl_label byteT DfracDiscarded label ∗
    "Hsl_val" ∷ own_slice_small sl_val byteT DfracDiscarded val ∗
    "Hown_ctx" ∷ own_context ptr_ctx (DfracOwn 1)
  }}}
  put #n0 #depth (slice_val sl_label) (slice_val sl_val) #ptr_ctx
  {{{
    ptr_n', RET #();
    "Hown_merkle" ∷ own_merkle_map_aux ptr_n' (<[label:=val]>elems) depth (DfracOwn 1) ∗
    "Hptr_n0" ∷ n0 ↦[ptrT] #ptr_n' ∗
    "Hown_ctx" ∷ own_context ptr_ctx (DfracOwn 1)
  }}}.
Proof.
  (* NOTE: there's a lot of similar proofs to solve the
  different values of get_bit. it's hard to combine them together since:
  (1) the choice of get_bit impacts things like struct field selection,
  (2) code like getChild uses child 0 first and then child 1,
  (3) re-establishing invariants uses slightly different fin_maps lemmas
  for each case.
  to follow the case-work, look for the iExists at the end of a case,
  which gives the tree structure before returning. *)
  iLöb as "IH" forall (n0 ptr_n elems depth).
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_rec. wp_load. wp_if_destruct.
  { (* empty node. *)
    iClear "IH". iNamed "Hown_merkle".
    iDestruct (own_empty_tree with "Hown_tree") as %->.

    wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "Hptr_leaf".
    iDestruct (struct_fields_split with "Hptr_leaf") as "H". iNamed "H".
    wp_store. wp_rec. do 2 wp_loadField.
    wp_apply (wp_compLeafHash sl_label sl_val with "[$Hsl_label $Hsl_val]").
    iIntros "*". iNamed 1.
    iDestruct (own_slice_to_small with "Hsl_hash") as "Hsl_hash".
    iPersist "Hsl_hash".
    wp_storeField.
    wp_pures. iApply "HΦ".
    iDestruct (own_slice_small_sz with "Hsl_label") as %?.
    iFrame "Hown_ctx ∗". iExists (Leaf label val).
    iFrame "hash label val ∗#".
    iIntros "!>". iSplit; [naive_solver|word]. }

  iNamed "Hown_merkle".
  iRename "Hsl_label" into "Hsl_label_put".
  iRename "Hsl_val" into "Hsl_val_put".
  destruct t; iNamed "Hown_tree"; [done|..|done];
    iNamed "Hown_tree"; fold own_merkle_tree.
  { (* leaf node. *)
    wp_bind (If _ _ #false).
    wp_apply (wp_wand _ _ _
      (λ ret,
      "%Hret" ∷ ⌜ ret = #true ⌝ ∗
      "Hptr_child0" ∷ ptr_n ↦[node::"child0"] #null ∗
      "Hptr_child1" ∷ ptr_n ↦[node::"child1"] #null
      )%I
      with "[Hptr_child0 Hptr_child1]"
    ).
    { do 2 wp_loadField. wp_pures. by iFrame. }
    iIntros "*". iNamed 1. subst. wp_loadField.
    iDestruct "Hsl_label" as "-#Hsl_label".
    iDestruct "Hsl_val" as "-#Hsl_val".
    wp_apply (wp_BytesEqual with "[$Hsl_label $Hsl_label_put]").
    iIntros "[Hsl_label Hsl_label_put]".
    wp_if_destruct.
    { subst. iClear "IH". wp_storeField. wp_rec. do 2 wp_loadField.
      wp_apply (wp_compLeafHash with "[$Hsl_label $Hsl_val_put]").
      iIntros "*". iNamedSuffix 1 "_n".
      iDestruct (own_slice_to_small with "Hsl_hash_n") as "Hsl_hash_out".
      iPersist "Hsl_hash_out".
      iDestruct (own_slice_small_sz with "Hsl_label_put") as %?.
      wp_storeField. wp_pures. iApply "HΦ". iFrame "Hown_ctx ∗".
      iIntros "!>". iExists (Leaf label val). iSplit; [|iSplit]; try done.
      - by rewrite insert_singleton.
      - iFrame "Hptr_hash Hptr_label Hptr_val ∗#%". word. }

    wp_apply wp_allocStruct; [val_ty|].
    iIntros (?) "H".
    iDestruct (struct_fields_split with "H") as "H". iNamed "H".
    wp_store. wp_loadField.
    wp_apply (wp_getChild with "[$child0 $child1 $Hsl_label]").
    iIntros "*". case_match; iNamedSuffix 1 "_in";
      iRename "Hsl_label_in" into "Hsl_label".
    - wp_store.
      iDestruct ("Hclose_child1_in" with "Hptr2_child1_in") as "Hptr_child1_in".
      wp_apply (wp_getChild with "[$Hptr_child0_in $Hptr_child1_in $Hsl_label_put]").
      iIntros "*".
      case_match; iNamedSuffix 1 "_in";
        iRename "Hsl_label_in" into "Hsl_label_put".

      + wp_apply ("IH" with "[Hsl_hash Hptr_hash Hptr_label Hsl_label
          Hptr_val Hsl_val Hptr_child0 Hptr_child1
          $Hptr2_child1_in $Hsl_label_put $Hsl_val_put $Hown_ctx]").
        { iFrame "%". iSplit; [done|].
          iFrame "Hptr_hash Hptr_label Hptr_val ∗#". }
        iIntros "*". iNamedSuffix 1 "_ch".
        iDestruct (own_merkle_map_not_nil with "Hown_merkle_ch") as %?.
        { simpl. intros Heq. apply (f_equal dom) in Heq.
          rewrite insert_union_singleton_l dom_union_L in Heq.
          set_solver. }
        wp_pures. wp_rec. wp_loadField.
        iDestruct (own_context_to_null_tree with "Hown_ctx_ch") as "[Hown_ctx Hown_null]".
        wp_apply (wp_getNodeHash _ Empty  with "[$Hown_null $Hown_ctx]").
        iIntros "*". iNamedSuffix 1 "_ch0".
        iDestruct ("Hclose_child1_in" with "Hptr_n0_ch") as "Hptr_n0_ch".
        wp_loadField.
        iNamedSuffix "Hown_merkle_ch" "_ch".
        wp_apply (wp_getNodeHash with "[$Hown_tree_ch $Hown_ctx_ch0]").
        iIntros "*". iNamedSuffix 1 "_ch".
        wp_apply (wp_compInnerHash sl_hash0 sl_hash1 Slice.nil).
        { iFrame "#". iApply own_slice_zero. }
        iIntros "*". iNamed 1.
        iDestruct (own_slice_to_small with "Hsl_hash_out") as "Hsl_hash_out".
        iPersist "Hsl_hash_out".
        wp_storeField.

        wp_pures. iApply "HΦ". iFrame "Hown_ctx_ch Hptr_n0".
        iExists (Inner Empty t). iIntros "!>".
        iSplit; [|iSplit; [|iSplit]]; [iPureIntro..|].
        * simpl. by rewrite -Heq_tree_map_ch map_empty_union.
        * repeat split; try done.
          intros label'. rewrite -Heq_tree_map_ch. set_solver.
        * repeat split; [done|].
          simpl. rewrite -Heq_tree_map_ch map_empty_union. simpl.
          rewrite map_size_insert. simpl_map.
          by rewrite map_size_singleton.
        * iFrame "hash Hptr_n0_ch ∗#". naive_solver.

      + iDestruct (own_context_to_null_tree with "Hown_ctx") as "[Hown_ctx Hown_null]".
        wp_apply ("IH" with "[Hown_null
          $Hptr2_child0_in $Hsl_label_put $Hsl_val_put $Hown_ctx]").
        { iExists Empty. by iFrame "∗%". }
        iIntros "*". iNamedSuffix 1 "_ch".
        iDestruct (own_merkle_map_not_nil with "Hown_merkle_ch") as %?; [done|].
        iNamedSuffix "Hown_merkle_ch" "_ch".
        wp_pures. wp_rec.
        iDestruct ("Hclose_child0_in" with "Hptr_n0_ch") as "Hptr_n0_ch".
        wp_loadField.
        wp_apply (wp_getNodeHash with "[$Hown_tree_ch $Hown_ctx_ch]").
        iIntros "*". iNamedSuffix 1 "_ch".
        wp_loadField.
        wp_apply (wp_getNodeHash _ (Leaf label0 val0)
          with "[Hptr_hash Hptr_label Hptr_val
          Hptr_child0 Hptr_child1 Hsl_hash Hsl_label Hsl_val $Hown_ctx_ch]").
        { iFrame "Hptr_hash ∗#". }
        iIntros "*". iNamedSuffix 1 "_ch0".
        wp_apply (wp_compInnerHash sl_hash0 sl_hash1 Slice.nil).
        { iFrame "#". iApply own_slice_zero. }
        iIntros "*". iNamed 1.
        iDestruct (own_slice_to_small with "Hsl_hash_out") as "Hsl_hash_out".
        iPersist "Hsl_hash_out".
        wp_storeField.

        wp_pures. iApply "HΦ". iFrame "Hown_ctx_ch0 Hptr_n0".
        iExists (Inner t (Leaf label0 val0)). iIntros "!>".
        iSplit; [|iSplit; [|iSplit]]; [iPureIntro..|].
        * simpl.
          by rewrite -Heq_tree_map_ch insert_empty insert_union_singleton_l.
        * repeat split; try done; [|set_solver].
          intros label'. rewrite -Heq_tree_map_ch. set_solver.
        * repeat split; [done|]. simpl.
          rewrite -Heq_tree_map_ch insert_empty -insert_union_singleton_l.
          rewrite map_size_insert. simpl_map.
          by rewrite map_size_singleton.
        * iFrame "Hown_tree_ch Hown_tree_ch0 hash ∗#". naive_solver.

    - wp_store.
      iDestruct ("Hclose_child0_in" with "Hptr2_child0_in") as "Hptr_child0_in".
      wp_apply (wp_getChild with "[$Hptr_child1_in $Hptr_child0_in $Hsl_label_put]").
      iIntros "*".
      case_match; iNamedSuffix 1 "_in";
        iRename "Hsl_label_in" into "Hsl_label_put".

      + iDestruct (own_context_to_null_tree with "Hown_ctx") as "[Hown_ctx Hown_null]".
        wp_apply ("IH" with "[Hown_null
          $Hptr2_child1_in $Hsl_label_put $Hsl_val_put $Hown_ctx]").
        { iExists Empty. by iFrame "∗%". }
        iIntros "*". iNamedSuffix 1 "_ch".
        iDestruct (own_merkle_map_not_nil with "Hown_merkle_ch") as %?; [done|].
        iNamedSuffix "Hown_merkle_ch" "_ch".
        wp_pures. wp_rec.
        iDestruct ("Hclose_child1_in" with "Hptr_n0_ch") as "Hptr_n0_ch".
        wp_loadField.
        wp_apply (wp_getNodeHash _ (Leaf label0 val0)
          with "[Hptr_hash Hptr_label Hptr_val
          Hptr_child0 Hptr_child1 Hsl_hash Hsl_label Hsl_val $Hown_ctx_ch]").
        { iFrame "Hptr_hash ∗#". }
        iIntros "*". iNamedSuffix 1 "_ch0".
        wp_loadField.
        wp_apply (wp_getNodeHash with "[$Hown_tree_ch $Hown_ctx_ch0]").
        iIntros "*". iNamedSuffix 1 "_ch1".
        wp_apply (wp_compInnerHash sl_hash0 sl_hash1 Slice.nil).
        { iFrame "#". iApply own_slice_zero. }
        iIntros "*". iNamed 1.
        iDestruct (own_slice_to_small with "Hsl_hash_out") as "Hsl_hash_out".
        iPersist "Hsl_hash_out".
        wp_storeField.

        wp_pures. iApply "HΦ". iFrame "Hown_ctx_ch1 Hptr_n0".
        iExists (Inner (Leaf label0 val0) t). iIntros "!>".
        iSplit; [|iSplit; [|iSplit]]; [iPureIntro..|].
        * simpl.
          rewrite -Heq_tree_map_ch insert_empty insert_union_singleton_l.
          rewrite map_union_comm; [done|].
          apply map_disjoint_dom. set_solver.
        * repeat split; try done; [set_solver|].
          intros label'. rewrite -Heq_tree_map_ch. set_solver.
        * repeat split; [done|]. simpl.
          rewrite -Heq_tree_map_ch insert_empty -insert_union_singleton_l.
          rewrite map_size_insert. simpl_map.
          by rewrite map_size_singleton.
        * iFrame "Hown_tree_ch0 Hown_tree_ch1 hash ∗#". naive_solver.

      + wp_apply ("IH" with "[Hsl_hash Hptr_hash Hptr_label Hsl_label
          Hptr_val Hsl_val Hptr_child0 Hptr_child1
          $Hptr2_child0_in $Hsl_label_put $Hsl_val_put $Hown_ctx]").
        { iExists (Leaf label0 val0). do 3 (iSplit; [done|]).
          iFrame "Hptr_hash Hptr_label Hptr_val ∗#". }
        iIntros "*". iNamedSuffix 1 "_ch".
        iDestruct (own_merkle_map_not_nil with "Hown_merkle_ch") as %?.
        { simpl. intros Heq. apply (f_equal dom) in Heq.
          rewrite insert_union_singleton_l dom_union_L in Heq.
          set_solver. }
        wp_pures. wp_rec.
        iDestruct ("Hclose_child0_in" with "Hptr_n0_ch") as "Hptr_n0_ch".
        wp_loadField.
        iNamedSuffix "Hown_merkle_ch" "_ch0".
        wp_apply (wp_getNodeHash with "[$Hown_tree_ch0 $Hown_ctx_ch]").
        iIntros "*". iNamedSuffix 1 "_ch0".
        iDestruct (own_context_to_null_tree with "Hown_ctx_ch0") as "[Hown_ctx Hown_null]".
        wp_loadField.
        wp_apply (wp_getNodeHash _ Empty  with "[$Hown_null $Hown_ctx]").
        iIntros "*". iNamedSuffix 1 "_ch1".
        wp_apply (wp_compInnerHash sl_hash0 sl_hash1 Slice.nil).
        { iFrame "#". iApply own_slice_zero. }
        iIntros "*". iNamed 1.
        iDestruct (own_slice_to_small with "Hsl_hash_out") as "Hsl_hash_out".
        iPersist "Hsl_hash_out".
        wp_storeField.

        wp_pures. iApply "HΦ". iFrame "Hown_ctx_ch1 Hptr_n0".
        iExists (Inner t Empty). iIntros "!>".
        iSplit; [|iSplit; [|iSplit]]; [iPureIntro..|].
        * simpl. by rewrite -Heq_tree_map_ch0 map_union_empty.
        * repeat split; try done.
          intros label'. rewrite -Heq_tree_map_ch0. set_solver.
        * repeat split; [done|]. simpl.
          rewrite -Heq_tree_map_ch0 map_union_empty. simpl.
          rewrite map_size_insert. simpl_map.
          by rewrite map_size_singleton.
        * iFrame "Hown_tree_ch0 Hown_tree_ch1 hash ∗#". naive_solver. }

  (* inner node. *)
  wp_bind (If _ _ #false).
  wp_apply (wp_wand _ _ _
    (λ ret,
    "%Hret" ∷ ⌜ ret = #false ⌝ ∗
    "Hptr_child0" ∷ ptr_n ↦[node::"child0"] #ptr_child0 ∗
    "Hptr_child1" ∷ ptr_n ↦[node::"child1"] #ptr_child1
    )%I
    with "[Hptr_child0 Hptr_child1]"
  ).
  { wp_loadField. wp_if_destruct.
    - wp_loadField. wp_pures. iFrame. iPureIntro.
      case_bool_decide; naive_solver.
    - by iFrame. }
  iIntros "*". iNamed 1. subst.
  wp_apply (wp_getChild with "[$Hptr_child0 $Hptr_child1 $Hsl_label_put]").
  iIntros "* H". wp_pures.

  case_match; iNamed "H".
  - wp_apply ("IH" with "[Hown_child1 $Hptr2_child1
      $Hsl_label $Hsl_val_put $Hown_ctx]").
    { iFrame "∗%". naive_solver. }
    iIntros "* H". iNamedSuffix "H" "_ch1".
    iDestruct (own_merkle_map_not_nil with "Hown_merkle_ch1") as %?.
    { intros Heq. apply (f_equal dom) in Heq. set_solver. }
    iDestruct ("Hclose_child1" with "Hptr_n0_ch1") as "Hptr_child1".
    wp_pures. wp_rec. wp_loadField.
    wp_apply (wp_getNodeHash with "[$Hown_child0 $Hown_ctx_ch1]").
    iIntros "*". iNamedSuffix 1 "0". wp_loadField.
    iNamedSuffix "Hown_merkle_ch1" "1".
    wp_apply (wp_getNodeHash with "[$Hown_tree1 $Hown_ctx0]").
    iIntros "*". iNamedSuffix 1 "1".
    wp_apply (wp_compInnerHash sl_hash0 sl_hash1 Slice.nil).
    { iFrame "#". iApply own_slice_zero. }
    iIntros "*". iNamed 1.
    iDestruct (own_slice_to_small with "Hsl_hash_out") as "Hsl_hash_out".
    iPersist "Hsl_hash_out".
    wp_storeField.

    wp_pures. iApply "HΦ". iFrame "Hown_ctx1 Hptr_n0".
    iExists (Inner t1 t). iIntros "!>".
    destruct Hsorted as (? & Hbit_t1 & ? & Hbit_t2).
    iSplit; [|iSplit; [|iSplit]]; [iPureIntro..|].
    + simpl. rewrite -Heq_tree_map1.
      opose proof (tree_to_map_lookup_None _ _ _ _ _ Hbit_t1) as ?; [done|].
      by rewrite insert_union_r.
    + repeat split; try done.
      unfold tree_labels_have_bit in *. rewrite -Heq_tree_map1.
      intros label'. destruct (decide (label = label')); subst; [done|].
      intros ?. opose proof (Hbit_t2 label' _) as ?; [set_solver|done].
    + simpl in *. destruct_and?.
      repeat split; [done..|].
      rewrite -Heq_tree_map1.
      opose proof (tree_to_map_lookup_None _ _ _ _ _ Hbit_t1) as ?; [done|].
      rewrite -insert_union_r; [|done].
      rewrite map_size_insert. case_match; eauto with lia.
    + iFrame "Hown_tree0 Hown_tree1 Hptr_hash ∗#". naive_solver.

  - wp_apply ("IH" with "[Hown_child0 $Hptr2_child0
      $Hsl_label $Hsl_val_put $Hown_ctx]").
    { iFrame "∗%". naive_solver. }
    iIntros "* H". iNamedSuffix "H" "0".
    iDestruct (own_merkle_map_not_nil with "Hown_merkle0") as %?.
    { intros Heq. apply (f_equal dom) in Heq. set_solver. }
    iDestruct ("Hclose_child0" with "Hptr_n00") as "Hptr_child0".
    wp_pures. wp_rec. wp_loadField.
    iNamedSuffix "Hown_merkle0" "0".
    wp_apply (wp_getNodeHash with "[$Hown_tree0 $Hown_ctx0]").
    iIntros "*". iNamedSuffix 1 "0". wp_loadField.
    wp_apply (wp_getNodeHash with "[$Hown_child1 $Hown_ctx0]").
    iIntros "*". iNamedSuffix 1 "1".
    wp_apply (wp_compInnerHash sl_hash0 sl_hash1 Slice.nil).
    { iFrame "#". iApply own_slice_zero. }
    iIntros "*". iNamed 1.
    iDestruct (own_slice_to_small with "Hsl_hash_out") as "Hsl_hash_out".
    iPersist "Hsl_hash_out".
    wp_storeField.

    wp_pures. iApply "HΦ". iFrame "Hown_ctx1 Hptr_n0".
    iExists (Inner t t2). iIntros "!>".
    destruct Hsorted as (? & Hbit_t1 & ? & Hbit_t2).
    iSplit; [|iSplit; [|iSplit]]; [iPureIntro..|].
    + simpl. by rewrite -Heq_tree_map0 insert_union_l.
    + repeat split; try done.
      unfold tree_labels_have_bit in *. rewrite -Heq_tree_map0.
      intros label'. destruct (decide (label = label')); subst; [done|].
      intros ?. opose proof (Hbit_t1 label' _) as ?; [set_solver|done].
    + simpl in *. destruct_and?.
      repeat split; [done..|].
      rewrite -Heq_tree_map0.
      opose proof (tree_to_map_lookup_None _ _ _ _ _ Hbit_t2) as ?; [done|].
      rewrite -insert_union_l.
      rewrite map_size_insert. case_match; eauto with lia.
    + iFrame "Hown_tree0 Hown_tree1 Hptr_hash ∗#". naive_solver.
Qed.

Lemma wp_Tree__Put ptr_tr elems sl_label sl_val (label val : list w8) :
  {{{
    "Hown_Tree" ∷ own_Tree ptr_tr elems (DfracOwn 1) ∗
    "Hsl_label" ∷ own_slice_small sl_label byteT DfracDiscarded label ∗
    "Hsl_val" ∷ own_slice_small sl_val byteT DfracDiscarded val
  }}}
  Tree__Put #ptr_tr (slice_val sl_label) (slice_val sl_val)
  {{{
    err, RET #err;
    "Hgenie" ∷
      (⌜ err = false ⌝ ∗-∗
      "%Hlen_hash" ∷ ⌜ Z.of_nat $ length label = hash_len ⌝) ∗
    "Herr" ∷
      ("%Hlen_hash" ∷ ⌜ Z.of_nat $ length label = hash_len ⌝
      -∗
      "Hown_Tree" ∷ own_Tree ptr_tr (<[label:=val]>elems) (DfracOwn 1))
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_slice_len.
  iDestruct (own_slice_small_sz with "Hsl_label") as %?.
  wp_if_destruct.
  { iApply "HΦ". iIntros "!>". iSplit.
    - iSplit; [done|word].
    - iIntros "%". word. }
  iNamed "Hown_Tree".
  wp_loadField.
  wp_apply (wp_struct_fieldRef_pointsto with "[$Hptr_root]"); [done|].
  iIntros "* [%Hclose Hptr2_root]".
  wp_apply (wp_put with "[$Hown_ctx $Hown_map $Hsl_label $Hsl_val $Hptr2_root]").
  iIntros "*". iNamed 1.
  wp_pures. iApply "HΦ". iIntros "!>". iSplit.
  - iSplit; [word|done].
  - iIntros "_".
    specialize (Hclose #ptr_n').
    iDestruct (Hclose with "Hptr_n0") as "Hptr_root".
    iFrame.
Qed.

Lemma wp_verifySiblings sl_label sl_last_hash sl_sibs sl_dig
    d0 d1 d2 (label last_hash sibs dig : list w8) last_node found :
  {{{
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hsl_last_hash" ∷ own_slice sl_last_hash byteT (DfracOwn 1) last_hash ∗
    "Hsl_sibs" ∷ own_slice_small sl_sibs byteT d1 sibs ∗
    "Hsl_dig" ∷ own_slice_small sl_dig byteT d2 dig ∗

    "#Hlast_hash" ∷ is_tree_hash last_node last_hash ∗
    "%Hlast_path" ∷ ⌜ ∀ depth, tree_path last_node label depth found ⌝ ∗
    "#Hlast_proof" ∷ (∀ depth, tree_sibs_proof last_node label depth [])
  }}}
  verifySiblings (slice_val sl_label) (slice_val sl_last_hash)
    (slice_val sl_sibs) (slice_val sl_dig)
  {{{
    (err : bool), RET #err;
    let wish := ("#His_proof" ∷ is_merkle_proof label found sibs dig : iProp Σ) in
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hsl_dig" ∷ own_slice_small sl_dig byteT d2 dig ∗
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗ wish)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_slice_len. wp_if_destruct.
  { iDestruct (own_slice_small_sz with "Hsl_sibs") as %?.
    iApply "HΦ". iFrame. iIntros "!>". iSplit. { by iIntros (?). }
    iNamed 1. iNamed "His_proof".
    iDestruct (tree_sibs_proof_len with "Hproof") as %?.
    word. }

  wp_apply wp_ref_to; [done|]. iIntros (ptr_curr_hash) "Hptr_curr_hash".
  wp_apply wp_NewSliceWithCap; [done|]. iIntros (?) "Hsl_hash_out".
  wp_apply wp_ref_to; [done|]. iIntros (ptr_hash_out) "Hptr_hash_out".
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_depth_inv) "Hptr_depth_inv".
  remember (word.divu _ _) as max_depth.

  iPersist "Hsl_sibs".
  wp_apply (wp_forUpto
    (λ depth_inv, ∃ tr sl_curr_hash curr_hash sl_hash_out,
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hsl_curr_hash" ∷ own_slice sl_curr_hash byteT (DfracOwn 1) curr_hash ∗
    "Hptr_curr_hash" ∷ ptr_curr_hash ↦[slice.T byteT] sl_curr_hash ∗
    "Hsl_hash_out" ∷ own_slice sl_hash_out byteT (DfracOwn 1) [] ∗
    "Hptr_hash_out" ∷ ptr_hash_out ↦[slice.T byteT] sl_hash_out ∗

    "#Htree_hash" ∷ is_tree_hash tr curr_hash ∗
    "%Htree_path" ∷ ⌜ tree_path tr label (word.sub max_depth depth_inv) found ⌝ ∗
    "#Htree_proof" ∷ tree_sibs_proof tr label (word.sub max_depth depth_inv)
      (take (Z.to_nat (uint.Z depth_inv * hash_len)%Z) sibs)
    )%I
    with "[] [Hptr_depth_inv Hsl_label Hsl_last_hash Hptr_curr_hash
      Hsl_hash_out Hptr_hash_out]"
  ).
  3: { specialize (Hlast_path max_depth).
    iSpecialize ("Hlast_proof" $! max_depth).
    iFrame "Hptr_curr_hash Hptr_hash_out ∗#".
    replace (word.sub _ _) with (max_depth) by word.
    change (Z.to_nat _) with (0%nat). rewrite take_0.
    iFrame "%#". }
  { word. }

  (* return. *)
  2: { iClear "Hlast_hash Hlast_proof".
    iIntros "[H Hptr_depth_inv]". iNamed "H". wp_load.
    iDestruct (own_slice_to_small with "Hsl_curr_hash") as "Hsl_curr_hash".
    wp_apply (wp_BytesEqual with "[$Hsl_curr_hash $Hsl_dig]").
    iIntros "[_ Hsl_dig]".
    replace (word.sub _ _) with (W64 0) in *; [|word].
    iDestruct (own_slice_small_sz with "Hsl_sibs") as %?.
    rewrite take_ge; [|word].
    case_bool_decide; wp_pures.
    2: { (* wish says we have valid is_proof to dig.
      therefore, program is_proof must also talk about dig. *)
      iApply "HΦ". iFrame. iIntros "!>". iSplit. { by iIntros (?). }
      iNamed 1.
      iDestruct (is_merkle_proof_eq_dig _ _ _ _ curr_hash with "His_proof []") as %?.
      { iFrame "#%". }
      done. }
    iApply "HΦ". subst. iFrame "∗#".
    iIntros "!>". iSplit; [|naive_solver].
    iIntros (_). iFrame "#%". }

  (* loop body. *)
  iIntros (depth_inv Φ2) "!> (H & Hptr_depth_inv & %Hlt_depth) HΦ2". iNamed "H".
  do 2 wp_load.
  iDestruct (own_slice_small_sz with "Hsl_sibs") as "%Hlen_sibs".
  assert (sl_sibs.(Slice.sz) = word.mul max_depth (W64 32)) as Hlen_sibs0; [word|].
  assert (uint.Z (word.mul max_depth (W64 32)) = uint.Z max_depth * uint.Z 32) as Hnoof; [word|].
  wp_apply wp_SliceSubslice_small.
  3: iFrame "#".
  { apply _. }
  { word. }
  iIntros (?) "#Hsl_sibs_sub". wp_load.
  match goal with
  | |- context[own_slice_small s' _ _ ?x] => set (sibs_sub:=x)
  end.
  wp_pures.
  remember (word.sub (word.sub _ _) _) as depth.

  iDestruct (own_slice_small_sz with "Hsl_label") as %?.
  wp_apply (wp_getBit with "[$Hsl_label]").
  iIntros "*". iNamed 1. iRename "Hsl_b" into "Hsl_label".
  wp_pures. wp_bind (If _ _ _).
  wp_apply (wp_wand _ _ _
    (λ _,
    ∃ new_sl_hash_out new_hash_out,
    "Hsl_curr_hash" ∷ own_slice sl_curr_hash byteT (DfracOwn 1) curr_hash ∗
    "Hptr_curr_hash" ∷ ptr_curr_hash ↦[slice.T byteT] sl_curr_hash ∗
    "Hsl_hash_out" ∷ own_slice new_sl_hash_out byteT (DfracOwn 1) new_hash_out ∗
    "Hptr_hash_out" ∷ ptr_hash_out ↦[slice.T byteT] new_sl_hash_out ∗
    "#His_hash" ∷
      match get_bit label depth with
      | false => is_hash (inner_node_tag :: curr_hash ++ sibs_sub) new_hash_out
      | true => is_hash (inner_node_tag :: sibs_sub ++ curr_hash) new_hash_out
      end
    )%I
    with "[Hsl_curr_hash Hptr_curr_hash Hsl_hash_out Hptr_hash_out]"
  ).
  { wp_if_destruct.
    - do 2 wp_load.
      iDestruct (own_slice_small_read with "Hsl_curr_hash") as "[Hsl_curr_hash Hclose]".
      wp_apply (wp_compInnerHash with "[$Hsl_curr_hash $Hsl_sibs_sub $Hsl_hash_out]").
      iIntros "*". iNamed 1. wp_store.
      iDestruct ("Hclose" with "Hsl_child0") as "Hsl_curr_hash".
      rewrite Heqb0. by iFrame "∗#".
    - do 2 wp_load.
      iDestruct (own_slice_small_read with "Hsl_curr_hash") as "[Hsl_curr_hash Hclose]".
      wp_apply (wp_compInnerHash with "[Hsl_curr_hash $Hsl_hash_out]").
      { iFrame "∗#". }
      iIntros "*". iNamed 1. wp_store.
      iDestruct ("Hclose" with "Hsl_child1") as "Hsl_curr_hash".
      rewrite Heqb0. by iFrame "∗#". }
  iIntros (tmp). iNamed 1. wp_pures. clear tmp.

  do 2 wp_load.
  wp_apply (wp_SliceTake_full with "[$Hsl_curr_hash]"); [word|].
  iIntros "Hsl_curr_hash". rewrite take_0.
  iDestruct (own_slice_small_read with "Hsl_hash_out") as "[Hsl_hash_out Hclose]".
  wp_apply (wp_SliceAppendSlice with "[$Hsl_curr_hash $Hsl_hash_out]"); [done|].
  iIntros (?) "[Hsl_curr_hash Hsl_hash_out]".
  iDestruct ("Hclose" with "Hsl_hash_out") as "Hsl_hash_out".
  wp_store. wp_load.
  wp_apply (wp_SliceTake_full with "[$Hsl_hash_out]"); [word|].
  iIntros "Hsl_hash_out". rewrite take_0. wp_store.
  iApply "HΦ2". iFrame "Hptr_curr_hash Hptr_hash_out ∗".

  replace (word.sub _ (word.add _ _)) with (depth); [|word].
  assert (Z.of_nat (length sibs_sub) = hash_len).
  { rewrite subslice_length; word. }
  case_match.
  - iExists (Inner (Cut sibs_sub) tr).
    simpl. rewrite H1.
    replace (word.add depth _) with (word.sub max_depth depth_inv); [|word].
    iFrame "#%". iPureIntro. repeat split.
    (* FIXME(word): word has bad perf with lots of things in context. *)
    clear -Hlt_depth Hnoof. subst sibs_sub.
    replace (uint.Z (word.mul (word.add _ _) (W64 32))) with
        (uint.Z (word.add depth_inv (W64 1)) * 32); [|word].
    replace (Z.to_nat _) with (uint.nat depth_inv * 32 + 32)%nat; [|word].
    replace (uint.nat (word.mul depth_inv (W64 32))) with (uint.nat depth_inv * 32)%nat; [|word].
    replace (Z.to_nat (uint.Z depth_inv * 32)) with (uint.nat depth_inv * 32)%nat; [|word].
    by rewrite -subslice_take_drop' take_take_drop.
  - iExists (Inner tr (Cut sibs_sub)).
    simpl. rewrite H1.
    replace (word.add depth _) with (word.sub max_depth depth_inv); [|word].
    iFrame "#%". iPureIntro. repeat split.
    (* FIXME(word): word has bad perf with lots of things in context. *)
    clear -Hlt_depth Hnoof. subst sibs_sub.
    replace (uint.Z (word.mul (word.add _ _) (W64 32))) with
        (uint.Z (word.add depth_inv (W64 1)) * 32); [|word].
    replace (Z.to_nat _) with (uint.nat depth_inv * 32 + 32)%nat; [|word].
    replace (uint.nat (word.mul depth_inv (W64 32))) with (uint.nat depth_inv * 32)%nat; [|word].
    replace (Z.to_nat (uint.Z depth_inv * 32)) with (uint.nat depth_inv * 32)%nat; [|word].
    by rewrite -subslice_take_drop' take_take_drop.
Qed.

Lemma wp_Verify sl_label sl_val sl_proof sl_dig (in_tree : bool)
    d0 d1 d2 d3 (label val proof dig : list w8) :
  {{{
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hsl_val" ∷ own_slice_small sl_val byteT d1 val ∗
    "Hsl_proof" ∷ own_slice_small sl_proof byteT d2 proof ∗
    "Hsl_dig" ∷ own_slice_small sl_dig byteT d3 dig
  }}}
  Verify #in_tree (slice_val sl_label) (slice_val sl_val)
    (slice_val sl_proof) (slice_val sl_dig)
  {{{
    (err : bool), RET #err;
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hsl_val" ∷ own_slice_small sl_val byteT d1 val ∗
    "Hsl_dig" ∷ own_slice_small sl_dig byteT d3 dig ∗
    "Hgenie" ∷
      (⌜ err = false ⌝ ∗-∗ wish_merkle_Verify in_tree label val proof dig)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply (MerkleProof.wp_dec with "Hsl_proof"). iIntros "*". iNamed 1.
  wp_if_destruct.
  { (* wish requires encoding to succeed. *)
    iDestruct "Hgenie" as "[_ Hgenie]".
    iApply "HΦ". iFrame. iIntros "!>". iSplit. { by iIntros (?). }
    iNamed 1. iDestruct ("Hgenie" with "[]") as %?; [naive_solver|done]. }
  iDestruct "Hgenie" as "[Hgenie _]".
  iDestruct ("Hgenie" with "[//]") as "H". iNamed "H".
  iDestruct ("Herr" with "[//]") as "H". iNamed "H".
  iClear (err Heqb sl_tail) "Hsl_tail". iNamed "Hown_obj".

  (* leaf hash. *)
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_last_hash) "Hptr_last_hash".
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_err1) "Hptr_err1".
  wp_pures. wp_bind (if: _ then _ else _)%E.
  wp_apply (wp_wand _ _ _
    (λ _,
    ∃ last_node found sl_last_hash (last_hash : list w8) (err1 : bool),
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hsl_val" ∷ own_slice_small sl_val byteT d1 val ∗
    "Hsl_leaf_label" ∷ own_slice_small sl_leaf_label byteT d2
      obj.(MerkleProof.LeafLabel) ∗
    "Hptr_leaf_label" ∷ ptr_obj ↦[MerkleProof::"LeafLabel"]{d2} sl_leaf_label ∗
    "Hsl_leaf_val" ∷ own_slice_small sl_leaf_val byteT d2
      obj.(MerkleProof.LeafVal) ∗
    "Hptr_leaf_val" ∷ ptr_obj ↦[MerkleProof::"LeafVal"]{d2} sl_leaf_val ∗
    "Hptr_last_hash" ∷ ptr_last_hash ↦[slice.T byteT] (slice_val sl_last_hash) ∗
    "Hsl_last_hash" ∷ own_slice sl_last_hash byteT (DfracOwn 1) last_hash ∗
    "Hptr_err1" ∷ ptr_err1 ↦[boolT] #err1 ∗

    "#Htree_hash" ∷ is_tree_hash last_node last_hash ∗
    "%Htree_path" ∷ ⌜ ∀ depth, tree_path last_node label depth found ⌝ ∗
    "#Htree_proof" ∷ (∀ depth, tree_sibs_proof last_node label depth []) ∗
    "%Heq_found" ∷
      ⌜if in_tree
      then found = Some (label, val)
      else if obj.(MerkleProof.FoundOtherLeaf)
        then found = Some (obj.(MerkleProof.LeafLabel), obj.(MerkleProof.LeafVal)) ∧
          (if err1
          then label = obj.(MerkleProof.LeafLabel)
          else label ≠ obj.(MerkleProof.LeafLabel))
        else found = None ⌝ ∗
    "%Herr1" ∷ ⌜ err1 = true → in_tree = false ∧ obj.(MerkleProof.FoundOtherLeaf) = true ⌝
    )%I
    with "[Hsl_label Hsl_val Hptr_found_other_leaf
      Hsl_leaf_label Hptr_leaf_label
      Hptr_leaf_val Hsl_leaf_val Hptr_last_hash Hptr_err1]"
  ).
  { wp_if_destruct.
    - wp_apply (wp_compLeafHash with "[$Hsl_label $Hsl_val]").
      iIntros "*". iNamed 1. wp_store.
      iDestruct (own_slice_small_sz with "Hsl_label") as %Hlen_label.
      iExists (Leaf label val), _. iFrame "∗#".
      iIntros "!>". iSplit; [word|naive_solver].
    - wp_loadField. wp_if_destruct.
      + do 2 wp_loadField.
        wp_apply (wp_compLeafHash with "[$Hsl_leaf_label $Hsl_leaf_val]").
        iIntros "*". iNamedSuffix 1 "_leaf". wp_store.
        iDestruct (own_slice_small_sz with "Hsl_label_leaf") as %Hlen_label.
        wp_loadField.
        wp_apply (wp_BytesEqual with "[$Hsl_label $Hsl_label_leaf]").
        iIntros "[Hsl_label Hsl_label_leaf]".
        wp_if_destruct.
        * wp_store.
          iExists (Leaf obj.(MerkleProof.LeafLabel) obj.(MerkleProof.LeafVal)), _.
          iFrame "∗#". iIntros "!>". iSplit; [word|done].
        * iExists (Leaf obj.(MerkleProof.LeafLabel) obj.(MerkleProof.LeafVal)), _.
          iFrame "∗#". iIntros "!>". iSplit; [word|done].
      + wp_apply wp_compEmptyHash.
        iIntros "*". iNamed 1. wp_store.
        iExists Empty, _. by iFrame "∗#". }
  iIntros (tmp). iNamed 1. wp_pures. clear tmp.

  wp_load. wp_if_destruct.
  { (* wish requires label to be diff than leaf label. *)
    opose proof (Herr1 _) as [-> Heq]; [done|].
    iApply "HΦ". iFrame. iIntros "!>". iSplit. { by iIntros (?). }
    iNamed 1. subst.
    opose proof (MerkleProof.inj Heq_tail0 Henc_obj Henc) as (->&->&->).
    rewrite !Heq in Heq_found Heq_found0. naive_solver. }

  clear Herr1. wp_loadField. wp_load.
  wp_apply (wp_verifySiblings with "[$Hsl_label $Hsl_last_hash
    $Hsl_sibs $Hsl_dig]").
  { iFrame "#%". }
  iClear (Htree_path) "Htree_hash". iIntros (err). iNamed 1.
  iApply "HΦ". iFrame. destruct err.
  { (* wish has is_proof, but inner genie says it's impossible to have that. *)
    iDestruct "Hgenie" as "[_ Hgenie]".
    iSplit. { by iIntros (?). }
    iNamed 1. subst.
    opose proof (MerkleProof.inj Heq_tail0 Henc_obj Henc) as (->&->&->).
    assert (found = found0) as ->.
    { repeat case_match; subst; try done. naive_solver. }
    by iDestruct ("Hgenie" with "His_proof") as %?. }

  iDestruct "Hgenie" as "[Hgenie _]".
  iDestruct ("Hgenie" with "[//]") as "Hgenie". iNamed "Hgenie".
  iSplit; [|naive_solver]. iIntros (_).
  iFrame "∗#%".
Qed.

End proof.
