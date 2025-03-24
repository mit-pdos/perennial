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
  | Inner lt rt =>
    sorted_tree lt (depth+1) ∧ tree_labels_have_bit lt depth false ∧
    sorted_tree rt (depth+1) ∧ tree_labels_have_bit rt depth true
  | _ => True
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
    result = Some (found_label, found_val)
  | Inner lt rt =>
    match get_bit label label_depth with
    | false => tree_path lt label (label_depth+1) result
    | true  => tree_path rt label (label_depth+1) result
    end
  | Cut _ => False
  end.

(* TODO: rm once seal merged in. *)
Program Definition u64_le_seal := sealed @u64_le.
Definition u64_le_unseal : u64_le_seal = _ := seal_eq _.
Lemma u64_le_seal_len x :
  length $ u64_le_seal x = 8%nat.
Proof. Admitted.

Fixpoint is_tree_hash (t: tree) (h: list w8) : iProp Σ :=
  match t with
  | Empty =>
    "#His_hash" ∷ is_hash [empty_node_tag] h
  | Leaf label val =>
    "%Hlen_label" ∷ ⌜ length label = hash_len ⌝ ∗
    "#His_hash" ∷ is_hash ([leaf_node_tag] ++ label ++ (u64_le_seal $ length val) ++ val) h
  | Inner lt rt =>
    ∃ hl hr,
    "#Hleft_hash" ∷ is_tree_hash lt hl ∗
    "#Hright_hash" ∷ is_tree_hash rt hr ∗
    "#His_hash" ∷ is_hash ([inner_node_tag] ++ hl ++ hr) h
  | Cut ch =>
    "%Heq_cut" ∷ ⌜ h = ch ⌝ ∗
    "%Hlen_hash" ∷ ⌜ length h = hash_len ⌝
  end.

#[global]
Instance is_tree_hash_persistent t h : Persistent (is_tree_hash t h).
Proof. revert h. induction t; apply _. Qed.

Lemma is_tree_hash_len t h:
  is_tree_hash t h -∗
  ⌜length h = hash_len⌝.
Proof. destruct t; iNamed 1; [..|done]; by iApply is_hash_len. Qed.

Theorem tree_path_agree label label_depth found0 found1 h t0 t1:
  tree_path t0 label label_depth found0 →
  tree_path t1 label label_depth found1 →
  is_tree_hash t0 h -∗
  is_tree_hash t1 h -∗
  ⌜found0 = found1⌝.
Proof.
  iInduction t0 as [| ? | ? IH0 ? IH1 | ?] forall (label_depth t1 h);
    destruct t1; simpl; iIntros "*"; try done;
    iNamedSuffix 1 "0";
    iNamedSuffix 1 "1";
    iDestruct (is_hash_inj with "His_hash0 His_hash1") as %?;
    try naive_solver.

  (* both leaves. use leaf encoding. *)
  - iPureIntro. list_simplifier.
    apply app_inj_1 in H0; [naive_solver|].
    by rewrite !u64_le_seal_len.
  (* both inner. use inner encoding and next_pos same to get
  the same next_hash. then apply IH. *)
  - iDestruct (is_tree_hash_len with "Hleft_hash0") as %?.
    iDestruct (is_tree_hash_len with "Hleft_hash1") as %?.
    list_simplifier. case_match.
    + by iApply "IH1".
    + by iApply "IH0".
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

Definition found_nonmemb (label: list w8) (found: option ((list w8) * (list w8))%type) :=
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
    found_nonmemb label found.
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

Definition is_merkle_memb (label: list w8) (val: list w8) (h: list w8) : iProp Σ :=
  is_merkle_found label (Some (label, val)) h.

Definition is_merkle_nonmemb (label: list w8) (h: list w8) : iProp Σ :=
  ∃ found,
    is_merkle_found label found h ∗
    ⌜found_nonmemb label found⌝.

Fixpoint tree_sibs_proof (t: tree) (label: list w8) (label_depth: nat) (proof: list $ list w8) : iProp Σ :=
  match t with
  | Empty => ⌜proof = []⌝
  | Leaf found_label found_val => ⌜proof = []⌝
  | Inner lt rt =>
    ∃ sibhash proof', ⌜proof = sibhash :: proof'⌝ ∗
      match get_bit label label_depth with
      | false => tree_sibs_proof lt label (label_depth+1) proof' ∗ is_tree_hash rt sibhash
      | true  => tree_sibs_proof rt label (label_depth+1) proof' ∗ is_tree_hash lt sibhash
      end
  | Cut _ => False
  end.

Definition is_merkle_proof (label: list w8) (found: option ((list w8) * (list w8)%type)) (proof: list $ list w8) (h: list w8) : iProp Σ :=
  ∃ t,
    is_tree_hash t h ∗
    tree_sibs_proof t label 0 proof ∗
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
    ( m !! label = None ∧ found_nonmemb label found ) ⌝.
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
    "Hsl_hash" ∷ own_slice sl_hash byteT (DfracOwn 1) hash ∗
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
    "Hsl_hash" ∷ own_slice sl_hash byteT (DfracOwn 1) hash ∗
    "#His_hash" ∷ is_hash
      (leaf_node_tag :: label ++ (u64_le_seal $ length val) ++ val) hash
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
        is_merkle_memb label val dig
      else
        is_merkle_nonmemb label dig)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_slice_len.
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  wp_apply (MerkleProof.wp_dec with "Hsl_proof"). iIntros "*". iNamed 1.
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  iDestruct "Hgenie" as "[Hgenie _]".
  iDestruct ("Hgenie" with "[//]") as "H". iNamed "H".
  iDestruct ("Herr" with "[//]") as "H". iNamed "H".
  iClear (err Heqb0 tail sl_tail Henc_obj) "Hsl_tail".
  iNamed "Hown_obj". wp_loadField. wp_apply wp_slice_len.
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  remember (word.divu _ _) as max_depth.
  wp_loadField. wp_apply (wp_BytesEqual with "[$Hsl_label $Hsl_leaf_label]").
  iIntros "[Hsl_label Hsl_leaf_label]".
  wp_if_destruct. { iApply "HΦ". by iFrame. }

  (* leaf hash. *)
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_curr_hash) "Hptr_curr_hash".
  wp_pures. wp_bind (if: _ then _ else _)%E.
  wp_apply (wp_wand _ _ _
    (λ _,
    ∃ last_node found sl_curr_hash (curr_hash : list w8),
    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hsl_val" ∷ own_slice_small sl_val byteT d1 val ∗
    "Hsl_leaf_label" ∷ own_slice_small sl_leaf_label byteT
                         obj.(MerkleProof.d1) obj.(MerkleProof.LeafLabel) ∗
    "Hptr_leaf_label" ∷ ptr_obj ↦[MerkleProof::"LeafLabel"] sl_leaf_label ∗
    "Hsl_leaf_val" ∷ own_slice_small sl_leaf_val byteT
                       obj.(MerkleProof.d2) obj.(MerkleProof.LeafVal) ∗
    "Hptr_leaf_val" ∷ ptr_obj ↦[MerkleProof::"LeafVal"] sl_leaf_val ∗

    "Hptr_curr_hash" ∷ ptr_curr_hash ↦[slice.T byteT] (slice_val sl_curr_hash) ∗
    "Hsl_curr_hash" ∷ own_slice sl_curr_hash byteT (DfracOwn 1) curr_hash ∗

    "#Htree_hash" ∷ is_tree_hash last_node curr_hash ∗
    "%Htree_path" ∷ ⌜ tree_path last_node label (uint.nat max_depth) found ⌝ ∗
    "%Hfound" ∷ ⌜ if in_tree then found = Some (label, val)
      else found_nonmemb label found ⌝
    )%I
    with "[Hsl_label Hsl_val Hsl_leaf_label Hptr_leaf_label
    Hptr_leaf_val Hsl_leaf_val Hptr_curr_hash]"
  ).
  { wp_if_destruct.
    - wp_apply (wp_compLeafHash with "[$Hsl_label $Hsl_val]").
      iIntros "*". iNamed 1. wp_store.
      iDestruct (own_slice_small_sz with "Hsl_label") as %Hlen_label.
      iExists (Leaf label val), _. iFrame "∗#".
      iIntros "!>". iSplit; [word|naive_solver].
    - wp_loadField. wp_apply wp_slice_len.
      wp_if_destruct.
      + do 2 wp_loadField.
        wp_apply (wp_compLeafHash with "[$Hsl_leaf_label $Hsl_leaf_val]").
        iIntros "*". iNamedSuffix 1 "_leaf". wp_store.
        iDestruct (own_slice_small_sz with "Hsl_label_leaf") as %Hlen_label.
        iExists (Leaf obj.(MerkleProof.LeafLabel) obj.(MerkleProof.LeafVal)), _.
        iFrame "∗#". iIntros "!>". iSplit; [word|naive_solver].
      + wp_apply wp_compEmptyHash.
        iIntros "*". iNamed 1. wp_store.
        iDestruct (own_slice_small_sz with "Hsl_leaf_label") as %Hlen_label.
        iExists Empty, _. iFrame "∗#". naive_solver. }
  iIntros (tmp). iNamed 1. wp_pures. clear tmp Heqb Heqb2.

  (* hash up the tree. *)
  wp_apply wp_NewSliceWithCap; [done|]. iIntros (sl_hash_out) "Hsl_hash_out".
  iDestruct (own_slice_to_small with "Hsl_hash_out") as "Hsl_hash_out".
  wp_apply wp_ref_to; [done|]. iIntros (ptr_hash_out) "Hptr_hash_out".
  wp_apply wp_ref_to; [naive_solver|]. iIntros (ptr_depth) "Hptr_depth".

  destruct (uint.nat max_depth) eqn:Hzero_depth.
  { wp_pures. wp_rec. wp_load. wp_if_destruct; [word|]. wp_load.
    iDestruct (own_slice_to_small with "Hsl_curr_hash") as "Hsl_curr_hash".
    wp_apply (wp_BytesEqual with "[$Hsl_curr_hash $Hsl_dig]").
    iIntros "[_ Hsl_dig]". case_bool_decide; wp_pures.
    2: { iApply "HΦ". by iFrame. }
    iApply "HΦ". iFrame.
    case_match; subst; by iFrame "#%". }

  iMod (own_slice_small_persist with "Hsl_sibs") as "#Hsl_sibs".
  wp_apply (wp_forBreak_cond
    (λ cond, ∃ tr (depth : w64) curr_hash' sl_hash_out' hash_out',
    "Hptr_depth" ∷ ptr_depth ↦[uint64T] #depth ∗
    "%Hcond" ∷ ⌜ bool_decide (uint.Z depth >= 1) = cond ⌝ ∗
    "%Hlt_depth" ∷ ⌜ uint.Z depth <= uint.Z max_depth ⌝ ∗

    "Hsl_label" ∷ own_slice_small sl_label byteT d0 label ∗
    "Hptr_sibs" ∷ ptr_obj ↦[MerkleProof::"Siblings"] sl_sibs ∗
    "Hsl_curr_hash" ∷ own_slice sl_curr_hash byteT (DfracOwn 1) curr_hash' ∗
    "Hptr_curr_hash" ∷ ptr_curr_hash ↦[slice.T byteT] sl_curr_hash ∗
    "Hsl_hash_out" ∷ own_slice_small sl_hash_out' byteT (DfracOwn 1) hash_out' ∗
    "Hptr_hash_out" ∷ ptr_hash_out ↦[slice.T byteT] sl_hash_out' ∗

    "#Htree_hash" ∷ is_tree_hash tr curr_hash' ∗
    "%Htree_path" ∷ ⌜ tree_path tr label (uint.nat depth) found ⌝
    )%I
    with "[] [Hptr_depth Hsl_label Hsl_sibs Hptr_sibs
      Hsl_curr_hash Hptr_curr_hash Hsl_hash_out Hptr_hash_out]"
  ).
  2: { iFrame "∗#%". iSplit.
    - case_bool_decide; [done|word].
    - by rewrite -Hzero_depth in Htree_path. }
  { iClear (Hzero_depth Htree_path Hfound) "Htree_hash".
    iIntros (Φ2) "!> H HΦ2". iNamed "H".
    apply bool_decide_eq_true in Hcond.
    wp_load. wp_if_destruct; [|word].
    do 2 wp_load. wp_loadField.
    iDestruct (own_slice_small_sz with "Hsl_sibs") as "%Hlen_sibs".
    (* FIXME(word) *)
    assert (sl_sibs.(Slice.sz) = word.mul max_depth (W64 32)) as Hlen_sibs0.
    { apply w64_val_f_equal in Heqb0 as [Heqb0 _].
      rewrite word.unsigned_modu_nowrap in Heqb0; [|word].
      subst. word. }
    (* FIXME(word): word should probably do subst. *)
    assert (uint.Z (word.mul max_depth (W64 32)) = uint.Z max_depth * uint.Z 32) as Hnoof.
    { subst. word. }
    wp_apply wp_SliceSubslice_small.
    3: iFrame "#".
    { apply _. }
    { word. }
    iIntros (?) "Hsl_sibs_sub".
Admitted.

End proof.
