From Perennial.program_proof Require Import grove_prelude.
From Perennial Require Import base.
From Goose.github_com.mit_pdos.pav Require Import merkle.

From Perennial.Helpers Require Import bytes.
From Perennial.program_proof.pav Require Import cryptoffi cryptoutil.
From Perennial.program_proof Require Import std_proof marshal_stateless_proof.

Notation empty_node_tag := (W8 0) (only parsing).
Notation inner_node_tag := (W8 1) (only parsing).
Notation leaf_node_tag := (W8 2) (only parsing).

Module MerkleProof.
Record t :=
  mk {
    Siblings: list w8;
    d0: dfrac;
    LeafLabel: list w8;
    d1: dfrac;
    LeafVal: list w8;
    d2: dfrac;
  }.
Definition encodes (obj : t) : list w8 :=
  u64_le (length obj.(Siblings)) ++ obj.(Siblings) ++
  u64_le (length obj.(LeafLabel)) ++ obj.(LeafLabel) ++
  u64_le (length obj.(LeafVal)) ++ obj.(LeafVal).

Section defs.
Context `{!heapGS Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ sl_sibs sl_leaf_label sl_leaf_val,
  "Hsl_sibs" ∷ own_slice_small sl_sibs byteT obj.(d0) obj.(Siblings) ∗
  "Hptr_sibs" ∷ ptr ↦[MerkleProof :: "Siblings"] (slice_val sl_sibs) ∗
  "Hsl_leaf_label" ∷ own_slice_small sl_leaf_label byteT obj.(d1) obj.(LeafLabel) ∗
  "Hptr_leaf_label" ∷ ptr ↦[MerkleProof :: "LeafLabel"] (slice_val sl_leaf_label) ∗
  "Hsl_leaf_val" ∷ own_slice_small sl_leaf_val byteT obj.(d2) obj.(LeafVal) ∗
  "Hptr_leaf_val" ∷ ptr ↦[MerkleProof :: "LeafVal"] (slice_val sl_leaf_val).

Lemma wp_dec sl_enc d0 enc :
  {{{
    "Hsl_enc" ∷ own_slice_small sl_enc byteT d0 enc
  }}}
  MerkleProofDecode (slice_val sl_enc)
  {{{
    ptr_obj sl_tail err, RET (#ptr_obj, slice_val sl_tail, #err);
    "Hgenie" ∷
      (⌜ err = false ⌝ ∗-∗
      ∃ obj tail,
      "%Henc_obj" ∷ ⌜ enc = encodes obj ++ tail ⌝) ∗
    "Herr" ∷
      (∀ obj tail,
      "%Henc_obj" ∷ ⌜ enc = encodes obj ++ tail ⌝
      -∗
      "Hown_obj" ∷ own ptr_obj obj ∗
      "Hsl_tail" ∷ own_slice_small sl_tail byteT d0 tail)
  }}}.
Proof. Admitted.

End defs.
End MerkleProof.

Section proof.
Context `{!heapGS Σ}.

(* get_bit returns false if bit n of l is 0 (or the bit is past the length of l). *)
Definition get_bit (l : list w8) (n : nat) : bool :=
  match mjoin (byte_to_bits <$> l) !! n with
  | Some bit => bit
  | None     => false
  end.

Inductive tree :=
| Empty
| Leaf (label: list w8) (val: list w8)
| Inner (l: tree) (r: tree)
| Cut (hash: list w8).

Fixpoint tree_to_gmap (t: tree) : gmap (list w8) (list w8) :=
  match t with
  | Empty => ∅
  | Leaf label val => {[label := val]}
  | Inner lt rt => (tree_to_gmap lt) ∪ (tree_to_gmap rt)
  | Cut h => ∅
  end.

Definition tree_labels_have_bit (t: tree) (nbit: nat) (val: bool) : Prop :=
  forall l,
    l ∈ dom (tree_to_gmap t) ->
    get_bit l nbit = val.

Fixpoint sorted_tree (t: tree) (depth: nat) : Prop :=
  match t with
  | Empty => True
  | Leaf label val => length label = hash_len
  | Inner lt rt =>
    sorted_tree lt (depth+1) ∧ tree_labels_have_bit lt depth false ∧
    sorted_tree rt (depth+1) ∧ tree_labels_have_bit rt depth true
  | Cut h => True
  end.

Inductive cutless_tree : ∀ (t: tree), Prop :=
  | CutlessEmpty : cutless_tree Empty
  | CutlessLeaf : ∀ label val, cutless_tree (Leaf label val)
  | CutlessInner : ∀ lt rt, cutless_tree lt -> cutless_tree rt -> cutless_tree (Inner lt rt).

Fixpoint tree_path (t: tree) (label: list w8) (label_depth: nat) (result: option (list w8 * list w8)%type) : Prop :=
  match t with
  | Empty =>
    result = None
  | Leaf found_label found_val =>
    result = Some (found_label, found_val) ∧ length found_label = hash_len
  | Inner lt rt =>
    match get_bit label label_depth with
    | false => tree_path lt label (label_depth+1) result
    | true  => tree_path rt label (label_depth+1) result
    end
  | Cut _ => False
  end.

Fixpoint is_tree_hash (t: tree) (h: list w8) : iProp Σ :=
  match t with
  | Empty =>
    is_hash [empty_node_tag] h
  | Leaf label val =>
    is_hash ([leaf_node_tag] ++ label ++ (u64_le $ length val) ++ val) h
  | Inner lt rt =>
    ∃ hl hr,
    is_tree_hash lt hl ∗
    is_tree_hash rt hr ∗
    is_hash ([inner_node_tag] ++ hl ++ hr) h
  | Cut ch =>
    ⌜h = ch ∧ length h = hash_len⌝
  end.

Lemma is_tree_hash_len t h:
  is_tree_hash t h -∗
  ⌜length h = hash_len⌝.
Proof.
  induction t; simpl; iIntros "H".
  - iApply is_hash_len; done.
  - iApply is_hash_len; done.
  - iDestruct "H" as (??) "(_ & _ & H)". iApply is_hash_len; done.
  - iDestruct "H" as "%". intuition.
Qed.

Theorem tree_path_agree label label_depth found0 found1 h t0 t1:
  tree_path t0 label label_depth found0 ->
  tree_path t1 label label_depth found1 ->
  is_tree_hash t0 h -∗
  is_tree_hash t1 h -∗
  ⌜found0 = found1⌝.
Proof.
  revert label_depth t1 h.
  induction t0; simpl; intros; eauto.
  - iIntros "H0 H1".
    destruct t1; simpl in *; intuition subst; eauto.
    * iDestruct (is_hash_inj with "H0 H1") as "%Hinj". naive_solver.
    * iDestruct "H1" as (??) "(_ & _ & H1)".
      iDestruct (is_hash_inj with "H0 H1") as "%Hinj". naive_solver.
  - iIntros "H0 H1".
    destruct t1; simpl in *; intuition subst; eauto.
    * iDestruct (is_hash_inj with "H0 H1") as "%Hinj". naive_solver.
    * iDestruct (is_hash_inj with "H0 H1") as "%Hinj".
      inversion Hinj as [Hinj2].
      apply app_inj_1 in Hinj2; last by congruence.
      destruct Hinj2 as [-> Hinj2].
      apply app_inj_1 in Hinj2; last by rewrite !u64_le_length //.
      destruct Hinj2 as [Hlen ->].
      done.
    * iDestruct "H1" as (??) "(_ & _ & H1)".
      iDestruct (is_hash_inj with "H0 H1") as "%Hinj". naive_solver.
  - iIntros "H0 H1".
    iDestruct "H0" as (hl0 hr0) "(Htl0 & Htr0 & Hh0)".
    destruct t1; simpl in *; intuition subst; eauto.
    * iDestruct (is_hash_inj with "Hh0 H1") as "%Hinj". naive_solver.
    * iDestruct (is_hash_inj with "Hh0 H1") as "%Hinj". naive_solver.
    * iDestruct "H1" as (hl1 hr1) "(Htl1 & Htr1 & Hh1)".
      iDestruct (is_hash_inj with "Hh0 Hh1") as "%Hinj".
      iDestruct (is_tree_hash_len with "Htl0") as "%Htllen0".
      iDestruct (is_tree_hash_len with "Htr0") as "%Htrlen0".
      iDestruct (is_tree_hash_len with "Htl1") as "%Htllen1".
      iDestruct (is_tree_hash_len with "Htr1") as "%Htrlen1".
      inversion Hinj; list_simplifier.
      destruct (get_bit label label_depth).
      + iApply (IHt0_2 with "Htr0 Htr1"); eauto.
      + iApply (IHt0_1 with "Htl0 Htl1"); eauto.
Qed.

Lemma tree_labels_have_bit_disjoint t0 t1 depth:
  tree_labels_have_bit t0 depth true ->
  tree_labels_have_bit t1 depth false ->
  disjoint (dom (tree_to_gmap t0)) (dom (tree_to_gmap t1)).
Proof.
  intros.
  apply elem_of_disjoint; intros.
  apply H in H1.
  apply H0 in H2.
  congruence.
Qed.

Lemma tree_to_gmap_lookup_None label depth bit t:
  get_bit label depth = (negb bit) ->
  tree_labels_have_bit t depth bit ->
  tree_to_gmap t !! label = None.
Proof.
  intros.
  destruct (tree_to_gmap t !! label) eqn:He; eauto.
  assert (get_bit label depth = bit).
  { apply H0. apply elem_of_dom; eauto. }
  rewrite H1 in H. destruct bit; simpl in *; congruence.
Qed.

Theorem tree_to_gmap_Some t label depth val:
  tree_to_gmap t !! label = Some val ->
  sorted_tree t depth ->
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
    + eapply tree_to_gmap_lookup_None in H0; eauto. destruct H; try congruence.
      eapply IHt2; eauto.
    + eapply tree_to_gmap_lookup_None in H4; eauto. destruct H; try congruence.
      eapply IHt1; eauto.
  - rewrite lookup_empty in H. congruence.
Qed.

Definition found_nonmembership (label: list w8) (found: option ((list w8) * (list w8))%type) :=
  match found with
  | None => True
  | Some (found_label, _) => label ≠ found_label
  end.

Theorem tree_to_gmap_None t label depth:
  tree_to_gmap t !! label = None ->
  sorted_tree t depth ->
  cutless_tree t ->
  ∃ found,
    tree_path t label depth found ∧
    found_nonmembership label found.
Proof.
  revert depth.
  induction t; simpl; intros.
  - rewrite lookup_empty in H. eexists; eauto.
  - apply lookup_singleton_None in H. eexists. split; eauto. simpl; congruence.
  - apply lookup_union_None in H; intuition.
    inversion H1; subst.
    destruct (get_bit label depth); eauto.
  - inversion H1.
Qed.

Definition is_merkle_map (m: gmap (list w8) (list w8)) (h: list w8) : iProp Σ :=
  ∃ t,
    ⌜m = tree_to_gmap t ∧ sorted_tree t 0 ∧ cutless_tree t⌝ ∗
    is_tree_hash t h.

Definition is_merkle_found (label: list w8) (found: option ((list w8) * (list w8))%type) (h: list w8) : iProp Σ :=
  ∃ t,
    ⌜tree_path t label 0 found⌝ ∗
    is_tree_hash t h.

Definition is_merkle_membership (label: list w8) (val: list w8) (h: list w8) : iProp Σ :=
  is_merkle_found label (Some (label, val)) h.

Definition is_merkle_nonmembership (label: list w8) (h: list w8) : iProp Σ :=
  ∃ found,
    is_merkle_found label found h ∗
    ⌜found_nonmembership label found⌝.

Fixpoint tree_siblings_proof (t: tree) (label: list w8) (label_depth: nat) (proof: list $ list w8) : iProp Σ :=
  match t with
  | Empty => ⌜proof = []⌝
  | Leaf found_label found_val => ⌜proof = []⌝
  | Inner lt rt =>
    ∃ sibhash proof', ⌜proof = sibhash :: proof'⌝ ∗
      match get_bit label label_depth with
      | false => tree_siblings_proof lt label (label_depth+1) proof' ∗ is_tree_hash rt sibhash
      | true  => tree_siblings_proof rt label (label_depth+1) proof' ∗ is_tree_hash lt sibhash
      end
  | Cut _ => False
  end.

Definition is_merkle_proof (label: list w8) (found: option ((list w8) * (list w8)%type)) (proof: list $ list w8) (h: list w8) : iProp Σ :=
  ∃ t,
    is_tree_hash t h ∗
    tree_siblings_proof t label 0 proof ∗
    ⌜tree_path t label 0 found⌝.

Fixpoint own_merkle_tree (ptr: loc) (t: tree) : iProp Σ :=
  ∃ hash,
    is_tree_hash t hash ∗
    match t with
    | Empty => ⌜ptr = null⌝
    | Leaf label val =>
      ∃ sl_hash sl_label sl_val,
        ptr ↦[node :: "hash"] (slice_val sl_hash) ∗
        ptr ↦[node :: "child0"] #null ∗
        ptr ↦[node :: "child1"] #null ∗
        ptr ↦[node :: "label"] (slice_val sl_label) ∗
        ptr ↦[node :: "val"] (slice_val sl_val) ∗
        own_slice_small sl_label byteT DfracDiscarded label ∗
        own_slice_small sl_val byteT DfracDiscarded val ∗
        own_slice_small sl_hash byteT DfracDiscarded hash
    | Inner lt rt =>
      ∃ sl_hash (ptr_l ptr_r : loc),
        ptr ↦[node :: "hash"] (slice_val sl_hash) ∗
        ptr ↦[node :: "child0"] #ptr_l ∗
        ptr ↦[node :: "child1"] #ptr_r ∗
        ptr ↦[node :: "label"] #null ∗
        ptr ↦[node :: "val"] #null ∗
        own_merkle_tree ptr_l lt ∗
        own_merkle_tree ptr_r rt ∗
        own_slice_small sl_hash byteT DfracDiscarded hash
    | Cut _ => False
    end.

Definition own_merkle_map (ptr: loc) (m: gmap (list w8) (list w8)) : iProp Σ :=
  ∃ t,
    ⌜m = tree_to_gmap t ∧ sorted_tree t 0 ∧ cutless_tree t⌝ ∗
    own_merkle_tree ptr t.

(* Some facts that might be helpful to derive from the above: *)

Lemma own_merkle_map_to_is_merkle_map ptr m:
  own_merkle_map ptr m -∗
  ∃ h,
    is_merkle_map m h.
Proof.
  iIntros "H".
  iDestruct "H" as (t) "[% H]".
  destruct t; iDestruct "H" as (h) "[H _]"; iExists _; iFrame; iPureIntro; intuition eauto.
Qed.

Lemma is_merkle_proof_to_is_merkle_found label found proof h:
  is_merkle_proof label found proof h -∗
  is_merkle_found label found h.
Proof.
  iIntros "H".
  iDestruct "H" as (?) "(Ht & Hsib & %)".
  iExists _; iFrame. done.
Qed.

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

Lemma is_merkle_map_agree_is_merkle_found m h label found:
  is_merkle_map m h -∗
  is_merkle_found label found h -∗
  ⌜ ( ∃ val, m !! label = Some val ∧ found = Some (label, val) ) ∨
    ( m !! label = None ∧ found_nonmembership label found ) ⌝.
Proof.
  iIntros "Hm Hf".
  iDestruct "Hm" as (?) "[% Hm]". intuition subst.
  iDestruct "Hf" as (?) "[%Hf Hf]".
  destruct (tree_to_gmap t !! label) eqn:He.
  - eapply tree_to_gmap_Some in He; eauto.
    iDestruct (tree_path_agree with "Hm Hf") as "%Hagree"; eauto.
  - eapply tree_to_gmap_None in He; eauto.
    destruct He as [? [? ?]].
    iDestruct (tree_path_agree with "Hm Hf") as "%Hagree"; eauto.
    iPureIntro. right. intuition subst; eauto.
Qed.

(* Program proofs. *)

Lemma wp_compEmptyHash :
  {{{ True }}}
  compEmptyHash #()
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "Hsl_hash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
    "#His_hash" ∷ is_hash [empty_node_tag] hash
  }}}.
Proof. Admitted.

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
    "Hsl_hash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
    "#His_hash" ∷ is_hash
      (leaf_node_tag :: label ++ (u64_le $ length val) ++ val) hash
  }}}.
Proof. Admitted.

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
    "Herr" ∷ (if err then True else
      if in_tree then
        is_merkle_membership label val dig
      else
        is_merkle_nonmembership label dig)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_slice_len.
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  wp_apply (MerkleProof.wp_dec with "Hsl_proof"). iIntros "*". iNamed 1.
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  iDestruct "Hgenie" as "[Hgenie _]".
  iDestruct ("Hgenie" with "[//]") as "H". iNamed "H".
  iDestruct ("Herr" with "[//]") as "H". iNamed "H". iClear "Hsl_tail".
  iNamed "Hown_obj". wp_loadField. wp_apply wp_slice_len.
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  wp_if_destruct. { iApply "HΦ". by iFrame. }

  (* leaf hash. *)
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_curr_hash) "Hptr_curr_hash".
  wp_pures. wp_bind (if: _ then _ else _)%E.
  wp_apply (wp_wand _ _ _
    (λ _,
    ∃ sl_curr_hash (curr_hash : list w8),
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hsl_val" ∷ own_slice_small sl_val byteT d1 val ∗
    "Hsl_leaf_label" ∷ own_slice_small sl_leaf_label byteT
                         obj.(MerkleProof.d1) obj.(MerkleProof.LeafLabel) ∗
    "Hptr_leaf_label" ∷ ptr_obj ↦[MerkleProof::"LeafLabel"] sl_leaf_label ∗
    "Hsl_leaf_val" ∷ own_slice_small sl_leaf_val byteT
                       obj.(MerkleProof.d2) obj.(MerkleProof.LeafVal) ∗
    "Hptr_leaf_val" ∷ ptr_obj ↦[MerkleProof::"LeafVal"] sl_leaf_val ∗

    "Hptr_curr_hash" ∷ ptr_curr_hash ↦[slice.T byteT] (slice_val sl_curr_hash) ∗
    "Hsl_curr_hash" ∷ own_slice_small sl_curr_hash byteT (DfracOwn 1) curr_hash ∗
    "#Hlast_hash" ∷
      is_tree_hash
      (if in_tree then Leaf label val else
        match obj.(MerkleProof.LeafLabel) with
        | [] => Empty
        | _ => Leaf obj.(MerkleProof.LeafLabel) obj.(MerkleProof.LeafVal)
        end)
      curr_hash
    )%I
    with "[Hsl_label Hsl_val Hsl_leaf_label Hptr_leaf_label
    Hptr_leaf_val Hsl_leaf_val Hptr_curr_hash]"
  ).
  { wp_if_destruct.
    - wp_apply (wp_compLeafHash with "[$Hsl_label $Hsl_val]").
      iIntros "*". iNamed 1. wp_store. by iFrame.
    - wp_loadField. wp_apply wp_slice_len.
      wp_if_destruct.
      + do 2 wp_loadField.
        wp_apply (wp_compLeafHash with "[$Hsl_leaf_label $Hsl_leaf_val]").
        iIntros "*". iNamedSuffix 1 "_leaf". wp_store.
        iDestruct (own_slice_small_sz with "Hsl_label_leaf") as %Hlen_label.
        iFrame. case_match; [|done]. simpl in *. word.
      + wp_apply wp_compEmptyHash.
        iIntros "*".  iNamed 1. wp_store.
        iDestruct (own_slice_small_sz with "Hsl_leaf_label") as %Hlen_label.
        iFrame. case_match; [done|]. simpl in *. word. }
  iIntros (tmp). iNamed 1. wp_pures. clear tmp.
Admitted.

End proof.
