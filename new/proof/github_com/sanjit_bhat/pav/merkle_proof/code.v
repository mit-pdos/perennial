From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import merkle.
From Perennial.Helpers Require Import bytes NamedProps.

From New.proof.github_com.goose_lang Require Import primitive std.
From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi cryptoutil safemarshal.
From New.proof.github_com.tchajed Require Import marshal.

From New.proof.github_com.sanjit_bhat.pav.merkle_proof Require Import base serde theory.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

(** ownership preds. *)

Fixpoint own_tree ptr t d : iProp Σ :=
  ∃ hash,
  "#Htree_hash" ∷ is_cut_tree t hash ∗
  match t with
  | Empty =>
    "%Heq_ptr" ∷ ⌜ ptr = null ⌝
  | Leaf label val =>
    ∃ sl_hash sl_label sl_val,
    "Hnode" ∷ ptr ↦{d}
      (merkle.node.mk leafNodeTy sl_hash null null sl_label sl_val) ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_val" ∷ sl_val ↦*□ val
  | Inner child0 child1 =>
    ∃ sl_hash ptr_child0 ptr_child1,
    "Hnode" ∷ ptr ↦{d}
      (merkle.node.mk innerNodeTy sl_hash ptr_child0 ptr_child1 slice.nil slice.nil) ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash ∗
    "Hown_child0" ∷ own_tree ptr_child0 child0 d ∗
    "Hown_child1" ∷ own_tree ptr_child1 child1 d
  | Cut _ =>
    ∃ sl_hash,
    "Hnode" ∷ ptr ↦{d}
      (merkle.node.mk cutNodeTy sl_hash null null slice.nil slice.nil) ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash
  end.

Definition own ptr m d : iProp Σ :=
  ∃ ptr_root t,
  "HMap" ∷ ptr ↦{d} (merkle.Map.mk ptr_root) ∗
  "%Heq_tree" ∷ ⌜ m = to_map t ⌝ ∗
  "Hown_tree" ∷ own_tree ptr_root t d ∗
  "%His_cutless" ∷ ⌜ is_cutless t ⌝ ∗
  "%His_limit" ∷ ⌜ is_limit t max_depth ⌝.

Lemma own_tree_to_hash ptr t d :
  own_tree ptr t d -∗
  ∃ dig, is_cut_tree t dig.
Proof. destruct t; iNamed 1; iFrame "#". Qed.

Lemma own_to_is_map ptr m d :
  own ptr m d -∗
  ∃ dig, is_map m dig.
Proof.
  iNamed 1.
  iFrame "%".
  iDestruct (own_tree_to_hash with "Hown_tree") as "[% #His_tree]".
  by iDestruct (cutless_to_full with "His_tree [] []") as "$".
Qed.

Lemma own_empty_tree t d :
  own_tree null t d -∗
  ⌜ t = Empty ⌝.
Proof.
  iIntros "H". destruct t; [done|..];
    iNamed "H"; iNamed "H";
    (iDestruct (typed_pointsto_not_null with "Hnode") as %?; [|done]);
    by rewrite go_type_size_unseal.
Qed.

(** program proofs. *)

Lemma wp_compLeafHash sl_label sl_val (label val : list w8) :
  {{{
    is_pkg_init merkle ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_val" ∷ sl_val ↦*□ val
  }}}
  @! merkle.compLeafHash #sl_label #sl_val
  {{{
    sl_hash hash, RET #sl_hash;
    "Hsl_hash" ∷ sl_hash ↦* hash ∗
    "#His_hash" ∷ cryptoffi.is_hash
      (Some $ leafNodeTag ::
      (u64_le $ length label) ++ label ++
      (u64_le $ length val) ++ val)
      hash
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply cryptoffi.wp_NewHasher as "* @".
  wp_apply wp_slice_literal as "* Hsl_b".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr $Hsl_b]") as "@".
  iClear "Hsl_b".
  wp_apply wp_WriteInt as "* [Hsl_b _]".
  { iDestruct own_slice_nil as "$".
    iDestruct own_slice_cap_nil as "$". }
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr $Hsl_b]") as "@".
  iClear "Hsl_b".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr $Hsl_label]") as "@".
  iClear "Hsl_b".
  wp_apply wp_WriteInt as "* [Hsl_b _]".
  { iDestruct own_slice_nil as "$".
    iDestruct own_slice_cap_nil as "$". }
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr $Hsl_b]") as "@".
  iClear "Hsl_b".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr $Hsl_val]") as "@".
  iClear "Hsl_b".
  wp_apply (cryptoffi.wp_Hasher_Sum with "[$Hown_hr]") as "* @".
  { iDestruct own_slice_nil as "$". }

  list_simplifier.
  iDestruct (own_slice_len with "Hsl_label") as %->.
  iDestruct (own_slice_len with "Hsl_val") as %->.
  iApply "HΦ". iFrame.
  iExactEq "His_hash".
  rewrite /named. repeat f_equal; word.
Qed.

Lemma wp_compInnerHash sl_child0 sl_child1 (child0 child1 : list w8) :
  {{{
    is_pkg_init merkle ∗
    "#Hsl_child0" ∷ sl_child0 ↦*□ child0 ∗
    "#Hsl_child1" ∷ sl_child1 ↦*□ child1
  }}}
  @! merkle.compInnerHash #sl_child0 #sl_child1
  {{{
    sl_hash hash, RET #sl_hash;
    "Hsl_hash" ∷ sl_hash ↦* hash ∗
    "#His_hash" ∷ cryptoffi.is_hash
      (Some $ innerNodeTag :: child0 ++ child1)
      hash
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply cryptoffi.wp_NewHasher as "* @".
  wp_apply wp_slice_literal as "* Hsl_b".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr $Hsl_b]") as "@".
  iClear "Hsl_b".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr $Hsl_child0]") as "@".
  iClear "Hsl_b".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr $Hsl_child1]") as "@".
  iClear "Hsl_b".
  wp_apply (cryptoffi.wp_Hasher_Sum with "[$Hown_hr]") as "* @".
  { iDestruct own_slice_nil as "$". }
  list_simplifier.
  iApply "HΦ". iFrame "∗#".
Qed.

Lemma length_bytes_to_bits b :
  length (bytes_to_bits b) = (8 * length b) % nat.
Proof.
  induction b; [done|].
  rewrite /= IHb. lia.
Qed.
(* TODO: add #[global] when upstream. *)
Hint Rewrite length_bytes_to_bits : len.

Lemma bytes_to_bits_app a b :
  bytes_to_bits (a ++ b) = bytes_to_bits a ++ bytes_to_bits b.
Proof. rewrite /bytes_to_bits !fmap_app join_app //. Qed.

Lemma join_lookup_Some_same_length''' {A : Type} ls c i (x : A) :
  (0 < c)%nat →
  Forall (λ l, length l = c) ls →
  mjoin ls !! i = Some x ↔
  ∃ l, ls !! (i `div` c)%nat = Some l ∧ l !! (i `mod` c)%nat = Some x.
Proof.
  intros ??.
  rewrite {1}(Nat.div_mod_eq i c) (comm Nat.mul).
  apply join_lookup_Some_same_length'; [done|].
  apply Nat.mod_upper_bound. lia.
Qed.

Lemma testbit_spec a n :
  0 ≤ n →
  Z.testbit a n = bool_decide (Z.land a (2 ^ n) ≠ 0).
Proof.
  intros. case_bool_decide as Heq.
  - apply Automation.word.decision_assume_opposite.
    intros Ht. apply Heq. clear Heq. rename Ht into Heq.
    apply not_true_is_false in Heq.
    apply Z.bits_inj_iff. intros p.
    rewrite Z.land_spec Z.bits_0.
    destruct (decide (p = n)).
    { subst.
      rewrite Z.pow2_bits_true; [|word].
      by rewrite andb_true_r. }
    rewrite Z.pow2_bits_false; [|word].
    by rewrite andb_false_r.
  - apply (f_equal (λ x, Z.testbit x n)) in Heq.
    rewrite Z.land_spec Z.bits_0 Z.pow2_bits_true in Heq; [|done].
    by rewrite andb_true_r in Heq.
Qed.

Lemma lookup_byte_to_bits byt i :
  (i < 8)%nat →
  byte_to_bits byt !! i =
    Some $ bool_decide (word.and byt (word.slu (W8 1) (W8 i)) ≠ W8 0).
Proof.
  intros. rewrite /byte_to_bits.
  assert (∀ x, bool_decide (x ≠ W8 0) = bool_decide (uint.Z x ≠ 0)) as ->.
  { intros. repeat case_bool_decide; word. }
  rewrite word.unsigned_and_nowrap.
  rewrite Automation.word.unsigned_slu'; [|word].
  rewrite left_id.
  replace (uint.Z (W8 i)) with (Z.of_nat i) by word.
  rewrite wrap_small.
  2: { split; [lia|]. apply Z.pow_lt_mono_r; word. }

  rewrite list_lookup_fmap.
  rewrite lookup_seqZ_lt; [|lia].
  rewrite left_id /=.
  f_equal.
  rewrite testbit_spec; [done|lia].
Qed.

Lemma bool_decide_ite_not (P : Prop) {dec : Decision P} :
  (if bool_decide P then false else true) = bool_decide (¬P).
Proof. by rewrite bool_decide_not. Qed.

(* TODO: upstream some helper lemmas. *)
Lemma wp_getBit sl_bs bs (n : w64) :
  {{{
    is_pkg_init merkle ∗
    "#Hsl_bs" ∷ sl_bs ↦*□ bs
  }}}
  @! merkle.getBit #sl_bs #n
  {{{
    bit, RET #bit;
    "->" ∷ ⌜ bit = get_bit bs (uint.nat n) ⌝
  }}}.
Proof.
  wp_start as "@". wp_auto.
  iDestruct (own_slice_len with "Hsl_bs") as %?.

  (* deal with OOB case. *)
  rewrite /get_bit list_lookup_total_alt.
  destruct (_ !! _) eqn:Hbs.
  2:{ apply lookup_ge_None in Hbs.
    rewrite length_bytes_to_bits in Hbs.
    wp_if_destruct; [word|].
    by iApply "HΦ". }

  (* in pure, extract bit. *)
  opose proof (lookup_lt_Some _ _ _ Hbs) as Hlt_n.
  rewrite length_bytes_to_bits in Hlt_n.
  rewrite /bytes_to_bits in Hbs.
  eapply join_lookup_Some_same_length''' in Hbs as (?&Hb&Ho).
  3: { apply Forall_fmap, Forall_true. naive_solver. }
  2: lia.
  apply list_lookup_fmap_Some in Hb as (byt&->&Hb).

  (* in golang, extract byte. *)
  wp_if_destruct; [|word].
  wp_auto.
  wp_apply (wp_load_slice_elem with "[$Hsl_bs]") as "_".
  { iPureIntro. exact_eq Hb.
    f_equal.
    rewrite word.unsigned_divu_nowrap; [|word].
    rewrite Z2Nat.inj_div; [done|word..]. }

  (* show equal. *)
  iApply "HΦ". iPureIntro.
  rewrite lookup_byte_to_bits in Ho.
  2: { by apply Nat.mod_upper_bound. }
  rewrite bool_decide_ite_not.
  replace (Z.of_nat (uint.nat n `mod` 8)%nat) with (uint.Z n `mod` 8) in Ho.
  2: { rewrite Nat2Z.inj_mod. word. }
  simplify_eq/=. clear.
  assert (∀ x y, x = y → bool_decide (x ≠ W8 0) = bool_decide (y ≠ W8 0))
    as Ht by naive_solver.
  f_equal. apply Ht. repeat f_equal. word.
Qed.

Lemma wp_node_getChild n d nodeTy sl_hash ptr_child0 ptr_child1 sl_label sl_val label (depth : w64) :
  {{{
    is_pkg_init merkle ∗
    "Hnode" ∷ n ↦{d}
      (merkle.node.mk nodeTy sl_hash ptr_child0 ptr_child1 sl_label sl_val) ∗
    "#Hsl_label" ∷ sl_label ↦*□ label
  }}}
  n @ (ptrT.id merkle.node.id) @ "getChild" #sl_label #depth
  {{{
    ptr_cb ptr_cnb, RET (#ptr_cb, #ptr_cnb);
    let (cb, cnb) := if get_bit label (uint.nat depth)
      then (ptr_child1, ptr_child0) else (ptr_child0, ptr_child1) in
    "Hcb" ∷ ptr_cb ↦{d} cb ∗
    "Hcnb" ∷ ptr_cnb ↦{d} cnb ∗
    "Hclose" ∷ (∀ ab anb,
      "Hab" ∷ ptr_cb ↦{d} ab -∗
      "Hanb" ∷ ptr_cnb ↦{d} anb -∗
      let (c0, c1) := if get_bit label (uint.nat depth)
        then (anb, ab) else (ab, anb) in
      "Hnode" ∷ n ↦{d}
        (merkle.node.mk nodeTy sl_hash c0 c1 sl_label sl_val))
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply (wp_getBit with "[$Hsl_label]") as "* @".
  destruct (get_bit _ _).
  - wp_auto. iApply "HΦ".
    iDestruct (struct_fields_split with "Hnode") as "H".
    iNamed "H". simpl. iFrame.
    iIntros (??) "@ @".
    iDestruct (struct_fields_combine (v:=merkle.node.mk _ _ _ _ _ _)
      with "[$HnodeTy $Hhash $Hlabel $Hval $Hab $Hanb]") as "$".
  - wp_auto. iApply "HΦ".
    iDestruct (struct_fields_split with "Hnode") as "H".
    iNamed "H". simpl. iFrame.
    iIntros (??) "@ @".
    iDestruct (struct_fields_combine (v:=merkle.node.mk _ _ _ _ _ _)
      with "[$HnodeTy $Hhash $Hlabel $Hval $Hab $Hanb]") as "$".
Qed.

Lemma wp_put n0 n t depth sl_label sl_val label val :
  {{{
    is_pkg_init merkle ∗ is_initialized ∗
    "Hn0" ∷ n0 ↦ n ∗
    "Hown_tree" ∷ own_tree n t 1 ∗
    "#Hlabel" ∷ sl_label ↦*□ label ∗
    "#Hval" ∷ sl_val ↦*□ val
  }}}
  @! merkle.put #n0 #depth #sl_label #sl_val
  {{{
    n' t', RET #();
    "Hn0" ∷ n0 ↦ n' ∗
    "%HSome_tree" ∷ ⌜ pure_put t label val (max_depth - uint.nat depth)%nat = Some t' ⌝ ∗
    "Hown_tree" ∷ own_tree n' t' 1
  }}}.
Proof.
  wp_start as "[Hinit @]". wp_auto.
  wp_if_destruct.
  { iDestruct (own_empty_tree with "Hown_tree") as %->.
    wp_auto.
    wp_apply wp_alloc as "* Hnode".
Admitted.

(*
Definition wish_Verify (in_tree : bool) label val proof dig : iProp Σ :=
  ∃ found proof_obj proof' tail,
  "%Henc" ∷ ⌜ MerkleProof.encodes proof_obj proof' ⌝ ∗
  "%Heq_tail" ∷ ⌜ proof = proof' ++ tail ⌝ ∗
  "%Heq_found" ∷
    ⌜if in_tree
    then found = Some (label, val)
    else if proof_obj.(MerkleProof.IsOtherLeaf)
      then found = Some (proof_obj.(MerkleProof.LeafLabel), proof_obj.(MerkleProof.LeafVal)) ∧
        label ≠ proof_obj.(MerkleProof.LeafLabel)
      else found = None ⌝ ∗
  "#His_proof" ∷ is_proof label found proof_obj.(MerkleProof.Siblings) dig.

Global Instance wish_Verify_pers i l v p d :
  Persistent (wish_Verify i l v p d) := _.

Lemma wish_Verify_to_entry in_tree label val proof dig :
  wish_Verify in_tree label val proof dig -∗
  is_entry label (if in_tree then Some val else None) dig.
Proof.
  iNamed 1. iNamed "His_proof".
  repeat case_match; intuition; subst; by iFrame "#%".
Qed.

Lemma wp_VerifyMemb sl_label sl_val sl_proof d0 d1 d2 (label val proof : list w8) :
  {{{
    is_pkg_init merkle ∗
    "Hsl_label" ∷ sl_label ↦*{d0} label ∗
    "Hsl_val" ∷ sl_val ↦*{d1} val ∗
    "Hsl_proof" ∷ sl_proof ↦*{d2} proof
  }}}
  merkle @ "VerifyMemb" #sl_label #sl_val #sl_proof
  {{{
    sl_dig err, RET (sl_dig, err);
    True
  }}}.
Proof. Admitted.
*)

End proof.
