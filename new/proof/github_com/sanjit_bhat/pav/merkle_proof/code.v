From New.generatedproof.github_com.sanjit_bhat.pav Require Import merkle.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From Stdlib.micromega Require Import ZifyNat.

From New.proof Require Import bytes.
From New.proof.github_com.goose_lang Require Import primitive std.
From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi cryptoutil safemarshal.
From New.proof.github_com.tchajed Require Import marshal.

From New.proof.github_com.sanjit_bhat.pav.merkle_proof Require Import base serde theory.

Module merkle.
Import base.merkle serde.merkle theory.merkle.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

(** tree predicates. *)

Fixpoint own_tree ptr t d : iProp Σ :=
  ∃ hash,
  "#Htree_hash" ∷ is_cut_tree t hash ∗
  match t with
  | Empty =>
    "%Heq_ptr" ∷ ⌜ptr = null⌝
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

Lemma own_tree_to_hash ptr t d :
  own_tree ptr t d -∗
  ∃ hash, is_cut_tree t hash.
Proof. destruct t; iNamed 1; iFrame "#". Qed.

Lemma own_empty_tree t d :
  own_tree null t d -∗
  ⌜t = Empty⌝.
Proof.
  iIntros "H". destruct t; [done|..];
    iNamed "H"; iNamed "H";
    (by iDestruct (typed_pointsto_not_null with "Hnode") as %?; [done|]).
Qed.

#[global] Instance own_tree_dfrac ptr t :
  DFractional (λ d, own_tree ptr t d).
Proof.
  split.
  - intros ??. iSplit.
    + iInduction t as [] forall (ptr);
        iIntros "H"; iNamed "H"; try iNamed "H"; fold own_tree.
      * by iFrame "#".
      * iDestruct "Hnode" as "[? ?]".
        iFrame "∗#".
      * iDestruct "Hnode" as "[? ?]".
        iDestruct ("IHt1" with "Hown_child0") as "[? ?]".
        iDestruct ("IHt2" with "Hown_child1") as "[? ?]".
        iFrame "∗#".
      * iDestruct "Hnode" as "[? ?]".
        iFrame "∗#".
    + iInduction t as [] forall (ptr);
        iIntros "[H0 H1]";
        iNamedSuffix "H0" "0"; iNamedSuffix "H1" "1";
        try iNamedSuffix "H0" "0"; try iNamedSuffix "H1" "1";
        fold own_tree.
      * by iFrame "#".
      * iCombine "Hnode0 Hnode1" as "Hnode" gives %[_ ?].
        simplify_eq/=.
        iFrame "∗#".
      * iCombine "Hnode0 Hnode1" as "Hnode" gives %[_ ?].
        simplify_eq/=.
        iDestruct ("IHt1" with "[$Hown_child00 $Hown_child01]") as "?".
        iDestruct ("IHt2" with "[$Hown_child10 $Hown_child11]") as "?".
        iFrame "∗#".
      * iCombine "Hnode0 Hnode1" as "Hnode" gives %[_ ?].
        simplify_eq/=.
        iFrame "∗#".
  - revert ptr. induction t; apply _.
  - iIntros "* H".
    iInduction t as [] forall (ptr);
      iNamed "H"; try iNamed "H"; fold own_tree.
    + by iFrame "#".
    + iPersist "Hnode". by iFrame "#".
    + iPersist "Hnode".
      iMod ("IHt1" with "Hown_child0") as "?".
      iMod ("IHt2" with "Hown_child1") as "?".
      by iFrame "∗#".
    + iPersist "Hnode". by iFrame "#".
Qed.

#[global] Instance own_tree_as_dfrac ptr t d :
  AsDFractional (own_tree ptr t d) (λ d, own_tree ptr t d) d.
Proof. auto. Qed.

#[global] Instance own_tree_combine_sep_gives ptr t0 t1 d0 d1 :
  CombineSepGives (own_tree ptr t0 d0) (own_tree ptr t1 d1) ⌜t0 = t1⌝.
Proof.
  rewrite /CombineSepGives.
  iIntros "[H0 H1]".
  iInduction t0 as [] forall (ptr t1); destruct t1;
    iNamedSuffix "H0" "0"; iNamedSuffix "H1" "1";
    try iNamedSuffix "H0" "0"; try iNamedSuffix "H1" "1";
    fold own_tree; subst.
  - by iModIntro.
  - by iDestruct (typed_pointsto_not_null with "Hnode1") as %?.
  - by iDestruct (typed_pointsto_not_null with "Hnode1") as %?.
  - by iDestruct (typed_pointsto_not_null with "Hnode1") as %?.
  - by iDestruct (typed_pointsto_not_null with "Hnode0") as %?.
  - iCombine "Hnode0 Hnode1" gives %[_ ?].
    simplify_eq/=.
    iCombine "Hsl_label0 Hsl_label1" gives %->.
    iCombine "Hsl_val0 Hsl_val1" gives %->.
    by iModIntro.
  - iCombine "Hnode0 Hnode1" gives %[_ ?].
    simplify_eq/=.
  - iCombine "Hnode0 Hnode1" gives %[_ ?].
    simplify_eq/=.
  - by iDestruct (typed_pointsto_not_null with "Hnode0") as %?.
  - iCombine "Hnode0 Hnode1" gives %[_ ?].
    simplify_eq/=.
  - iCombine "Hnode0 Hnode1" gives %[_ ?].
    simplify_eq/=.
    iDestruct ("IHt0_1" with "Hown_child00 Hown_child01") as %->.
    iDestruct ("IHt0_2" with "Hown_child10 Hown_child11") as %->.
    by iModIntro.
  - iCombine "Hnode0 Hnode1" gives %[_ ?].
    simplify_eq/=.
  - by iDestruct (typed_pointsto_not_null with "Hnode0") as %?.
  - iCombine "Hnode0 Hnode1" gives %[_ ?].
    simplify_eq/=.
  - iCombine "Hnode0 Hnode1" gives %[_ ?].
    simplify_eq/=.
  - iCombine "Hnode0 Hnode1" gives %[_ ?].
    simplify_eq/=.
    iCombine "Hsl_hash0 Hsl_hash1" gives %->.
    iNamedSuffix "Htree_hash0" "0".
    iNamedSuffix "Htree_hash1" "1".
    simplify_eq/=.
    by iModIntro.
Qed.

#[global] Instance own_tree_combine_sep_as ptr t0 t1 d0 d1 :
  CombineSepAs (own_tree ptr t0 d0) (own_tree ptr t1 d1)
    (own_tree ptr t0 (d0 ⋅ d1)) | 60.
Proof.
  rewrite /CombineSepAs. iIntros "[H0 H1]".
  iCombine "H0 H1" gives %->.
  iCombine "H0 H1" as "$".
Qed.

(** tree / Verify program proofs. *)

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
  iDestruct (own_slice_len with "Hsl_label") as %[-> ?].
  iDestruct (own_slice_len with "Hsl_val") as %[-> ?].
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

Lemma wp_getBit sl_bs d0 bs (n : w64) :
  {{{
    is_pkg_init merkle ∗
    "Hsl_bs" ∷ sl_bs ↦*{d0} bs
  }}}
  @! merkle.getBit #sl_bs #n
  {{{
    bit, RET #bit;
    "Hsl_bs" ∷ sl_bs ↦*{d0} bs ∗
    "->" ∷ ⌜bit = get_bit bs (uint.nat n)⌝
  }}}.
Proof.
  wp_start as "@". wp_auto.
  iDestruct (own_slice_len with "Hsl_bs") as %?.

  (* deal with OOB case. *)
  rewrite list_lookup_total_alt.
  destruct (_ !! _) eqn:Hbs.
  2:{ apply lookup_ge_None in Hbs.
    rewrite length_bytes_to_bits in Hbs.
    wp_if_destruct; [word|].
    iApply "HΦ". by iFrame. }

  (* in pure, extract bit. *)
  opose proof (lookup_lt_Some _ _ _ Hbs) as Hlt_n.
  rewrite length_bytes_to_bits in Hlt_n.
  rewrite /bytes_to_bits in Hbs.
  eapply join_same_len_lookup_join in Hbs as (?&Hb&Ho).
  3: { apply Forall_fmap, Forall_true. naive_solver. }
  2: lia.
  apply list_lookup_fmap_Some in Hb as (byt&->&Hb).

  (* in golang, extract byte. *)
  wp_if_destruct; [|word].
  wp_pure; [ word | ].
  wp_apply (wp_load_slice_elem with "[$Hsl_bs]") as "Hsl_bs".
  { word. }
  { replace (sint.nat (word.divu _ _)) with (uint.nat n `div` 8)%nat; eauto.
    rewrite -> sint_eq_uint by word.
    rewrite -> word.unsigned_divu_nowrap by word.
    change (uint.Z (W64 8)) with 8.
    rewrite Z2Nat.inj_div; [done|word..]. (* TODO: word limitation *) }

  (* show equal. *)
  iApply "HΦ". iFrame. iPureIntro.
  rewrite lookup_byte_to_bits in Ho.
  2: { by apply Nat.mod_upper_bound. }
  replace (Z.of_nat (uint.nat n `mod` 8)%nat) with (uint.Z n `mod` 8) in Ho.
  2: { rewrite Nat2Z.inj_mod. word. }
  simplify_eq/=. clear.
  rewrite -bool_decide_not.
  assert (∀ x y, x = y → bool_decide (x ≠ W8 0) = bool_decide (y ≠ W8 0))
    as Ht by naive_solver.
  apply Ht. repeat f_equal. word.
Qed.

Lemma wp_node_getChild n d0 nodeTy sl_hash ptr_child0 ptr_child1 l v sl_label d1 label (depth : w64) :
  {{{
    is_pkg_init merkle ∗
    "Hnode" ∷ n ↦{d0}
      (merkle.node.mk nodeTy sl_hash ptr_child0 ptr_child1 l v) ∗
    "Hsl_label" ∷ sl_label ↦*{d1} label
  }}}
  n @ (ptrT.id merkle.node.id) @ "getChild" #sl_label #depth
  {{{
    ptr_cb ptr_cnb, RET (#ptr_cb, #ptr_cnb);
    sl_label ↦*{d1} label ∗

    "Hcb" ∷ ptr_cb ↦{d0}
      (if get_bit label (uint.nat depth) then ptr_child1 else ptr_child0) ∗
    "Hcnb" ∷ ptr_cnb ↦{d0}
      (if get_bit label (uint.nat depth) then ptr_child0 else ptr_child1) ∗
    "Hclose" ∷ (∀ ab anb,
      "Hab" ∷ ptr_cb ↦{d0} ab -∗
      "Hanb" ∷ ptr_cnb ↦{d0} anb -∗
      "Hnode" ∷ n ↦{d0} (merkle.node.mk nodeTy sl_hash
        (if get_bit label (uint.nat depth) then anb else ab)
        (if get_bit label (uint.nat depth) then ab else anb)
        l v))
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

Lemma wp_node_getHash t n d :
  {{{
    is_pkg_init merkle ∗
    "Hown_tree" ∷ own_tree n t d
  }}}
  n @ (ptrT.id merkle.node.id) @ "getHash" #()
  {{{
    sl_hash hash, RET #sl_hash;
    "Hown_tree" ∷ own_tree n t d ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash ∗
    "#His_hash" ∷ is_cut_tree t hash
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_if_destruct.
  { iDestruct (own_empty_tree with "Hown_tree") as %->.
    iDestruct (is_pkg_init_access with "[$]") as "/= #Hinit".
    rewrite /is_initialized. iNamed "Hinit".
    wp_apply wp_globals_get.
    iApply "HΦ". iFrame "∗#". }
  destruct t; iNamed "Hown_tree"; try done; iNamed "Hown_tree";
    wp_auto; iApply "HΦ"; iFrame "∗#".
Qed.

Notation pref_ext p l := (p ++ [get_bit l (length p)]) (only parsing).

Lemma wp_getProofCap (depth : nat) :
  {{{
    is_pkg_init merkle ∗
    "%Heq_depth" ∷ ⌜depth ≤ max_depth⌝
  }}}
  @! merkle.getProofCap #(W64 depth)
  {{{
    (cap : w64), RET #cap;
    "%Heq_cap" ∷ ⌜8 ≤ sint.Z cap⌝
  }}}.
Proof. wp_start as "@". wp_auto. iApply "HΦ". word. Qed.

Lemma wp_put n0 n t sl_label sl_val label val :
  (* for max depth. *)
  is_limit t →
  Z.of_nat (length label) = cryptoffi.hash_len →
  is_const_label_len t →
  is_sorted t →
  {{{
    is_pkg_init merkle ∗
    "Hn0_in" ∷ n0 ↦ n ∗
    "Hown_tree" ∷ own_tree n t 1 ∗
    "#Hsl_label_in" ∷ sl_label ↦*□ label ∗
    "#Hsl_val_in" ∷ sl_val ↦*□ val
  }}}
  @! merkle.put #n0 #(W64 0) #sl_label #sl_val
  {{{
    n' err, RET #err;
    "Hn0" ∷ n0 ↦ n' ∗
    "Hgenie" ∷
      match err with
      | true => ¬ ⌜is_cutless_path t label⌝
      | false =>
        ∃ t',
        "%Hcode" ∷ ⌜pure_put t label val = Some t'⌝ ∗
        "Hown_tree" ∷ own_tree n' t' 1
      end
  }}}.
Proof.
  autounfold with merkle.
  assert (∃ x, x = max_depth) as [limit Heq]; [by eexists|].
  rewrite -[in is_limit' _ _]Heq.
  rewrite -[in pure_put' _ _ _ _ _]Heq.
  remember [] as pref.
  assert (prefix_total pref (bytes_to_bits label)).
  { subst. apply prefix_total_nil. }
  replace 0%nat with (length pref) by (by subst).
  replace (W64 0) with (W64 $ length pref).
  2: { subst. simpl. word. }
  assert (length pref + limit = max_depth)%nat.
  { subst. simpl. lia. }
  clear Heq Heqpref.
  intros.
  generalize dependent pref.
  generalize dependent t.

  iInduction limit as [? IH] using lt_wf_ind forall (n0 n Φ).
  iIntros (t ?? pref).
  iIntros "* (#?&@) HΦ".
  wp_func_call. wp_call. wp_auto.
  wp_apply wp_Assert.
  { iPureIntro. case_bool_decide; [done|]. word. }
  iDestruct (own_slice_len with "Hsl_label_in") as %?.
  iDestruct (own_slice_len with "Hsl_val_in") as %?.
  iEval (rewrite pure_put_unfold) in "HΦ".

  wp_if_destruct.
  (* empty. *)
  { iDestruct (own_empty_tree with "Hown_tree") as %->.
    iClear "IH".
    wp_apply wp_alloc as "* Hnode".
    iApply wp_fupd.
    wp_apply wp_compLeafHash as "* @".
    { iFrame "#". }
    iPersist "Hsl_hash". iModIntro.
    iApply "HΦ".
    iFrame. iExists _. iSplit; [done|].
    iFrame "∗#".
    iPureIntro. split; word. }

  destruct t; simpl in *; iNamed "Hown_tree"; try done;
    iNamedSuffix "Hown_tree" "_old".
  (* leaf. *)
  - wp_auto.
    wp_apply bytes.wp_Equal as "_".
    { iFrame "#". }
    wp_if_destruct.
    (* same label. *)
    { case_decide; [|done].
      iClear "IH".
      iApply wp_fupd.
      wp_apply wp_compLeafHash as "* @".
      { iFrame "#". }
      iPersist "Hsl_hash". iModIntro.
      iApply "HΦ".
      iFrame. iExists _. iSplit; [done|].
      iFrame "∗#".
      iPureIntro. split; word. }
    case_decide; [done|].
    destruct limit.
    (* limit=0. show labels actually equal. *)
    { exfalso.
      opose proof (prefix_total_full _ (bytes_to_bits label) _ _);
        [|done|]; [by len|].
      opose proof (prefix_total_full _ (bytes_to_bits label0) _ _);
        [|done|]; [by len|].
      simplify_eq/=. }

    (* diff label. *)
    wp_apply wp_alloc as "* Hnode".
    wp_apply (wp_node_getChild with "[$Hnode]") as "*".
    { iFrame "#". }
    iIntros "[_ H]". iNamed "H". wp_auto.
    replace (if get_bit _ _ then null else null) with (null).
    2: { by case_match. }
    iDestruct ("Hclose" with "Hcb Hcnb") as "@".
    wp_apply (wp_node_getChild with "[$Hnode]") as "*".
    { iFrame "#". }
    iIntros "[_ H]". iNamed "H". wp_auto.
    replace (uint.nat (W64 _)) with (length pref) by word.
    assert (∀ (b0 b1 : bool) T (x0 x1 : T),
      (if b0 then (if b1 then x0 else x1) else (if b1 then x1 else x0))
      = (if decide (b0 = b1) then x0 else x1)) as Ht.
    { intros. by repeat case_match. }
    rewrite !{}Ht.
    remember (decide _) as cond.
    replace (word.add _ _) with (W64 (length (pref_ext pref label))) by len.
    replace (S (length _)) with (length (pref_ext pref label)) by len.

    iSpecialize ("IH" $! limit with "[]"); [word|].
    iDestruct (condition_prop cond with "[Hnode_old] []")
      as "[Hown_n_left Hown_n_right]"; [iAccu..|].
    wp_apply ("IH" $! _ _ _ (if cond then (Leaf label0 val0) else Empty)
      with "[][][][][][Hcb Hown_n_left]") as "* @"; try iPureIntro.
    { by repeat case_match. }
    { by repeat case_match. }
    { by eapply prefix_total_snoc. }
    { len. }
    { repeat case_match; try done;
        by eapply prefix_total_snoc. }
    { iFrame "∗#".
      case_match.
      - iFrame "∗#".
      - iDestruct (is_pkg_init_access with "[$]") as "/= #Hinit".
        rewrite /is_initialized. iNamed "Hinit".
        by iFrame "#". }
    destruct err; iNamed "Hgenie".
    { iExFalso. iApply "Hgenie". iPureIntro. by case_match. }
    wp_apply std.wp_Assert; [done|].
    rewrite Hcode.
    iClear "IH".
    iDestruct ("Hclose" with "Hn0 Hcnb") as "@".
    wp_auto.

    (* TODO: can these two conditions be combined together? *)
    iDestruct (condition_bool (get_bit label (length pref))
      with "[Hown_n_right] []") as "[Hown_n_left Hown_n_right]"; [iAccu..|].
    iDestruct (condition_bool (get_bit label (length pref))
      with "[Hown_tree] []") as "[Hown_n'_left Hown_n'_right]"; [iAccu..|].
    wp_apply (wp_node_getHash
      (if get_bit label (length pref)
        then if cond then Empty else (Leaf label0 val0) else _)
      with "[Hown_n_left Hown_n'_right]").
    { iFrame "#".
      destruct (get_bit label _); [|by iFrame].
      case_match.
      - iDestruct (is_pkg_init_access with "[$]") as "/= #Hinit".
        rewrite /is_initialized. iNamed "Hinit".
        by iFrame "#".
      - iFrame "∗#". }
    iIntros "*". iNamedSuffix 1 "0". wp_auto.
    wp_apply (wp_node_getHash
      (if get_bit label (length pref)
        then _ else if cond then Empty else (Leaf label0 val0))
      with "[Hown_n_right Hown_n'_left]").
    { iFrame "#".
      destruct (get_bit label _); [by iFrame|].
      case_match.
      - iDestruct (is_pkg_init_access with "[$]") as "/= #Hinit".
        rewrite /is_initialized. iNamed "Hinit".
        by iFrame "#".
      - iFrame "∗#". }
    iIntros "*". iNamedSuffix 1 "1". wp_auto.
    iPersist "Hsl_hash0 Hsl_hash1".

    iApply wp_fupd.
    wp_apply (wp_compInnerHash with "[Hsl_hash0 Hsl_hash1]") as "* @".
    { iFrame "#". }
    iPersist "Hsl_hash".
    iModIntro. iApply "HΦ".
    iFrame "Hn0_in".
    iExists _. iSplit; [done|].
    simpl.
    iFrame "Hnode #".

    (* TODO: figure out how to get rid of these replaces.
    if we remove unfold cond, does it simplify this? *)
    replace (if get_bit label _ then if get_bit label0 _ then _ else _ else _)
      with (if get_bit label (length pref) then if cond then Empty else Leaf label0 val0 else t').
    2: { clear. by repeat case_match. }
    replace (if get_bit label _ then _ else if get_bit label0 _ then _ else _)
      with (if get_bit label (length pref) then t' else if cond then Empty else Leaf label0 val0).
    2: { clear. by repeat case_match. }
    iFrame "∗#".

  (* inner. *)
  - destruct limit; [done|].
    intuition.
    wp_auto.
    wp_apply (wp_node_getChild with "[$Hnode_old]") as "*".
    { iFrame "#". }
    iIntros "[_ H]". iNamed "H". wp_auto.
    replace (uint.nat (W64 _)) with (length pref) by word.
    replace (word.add _ _) with (W64 (length (pref_ext pref label))) by len.
    replace (S (length _)) with (length (pref_ext pref label)) in * by len.

    iSpecialize ("IH" $! limit with "[]"); [word|].
    iDestruct (condition_bool (get_bit label (length pref))
      with "[Hown_child1_old] [Hown_child0_old]")
      as "[Hown_child_left Hown_child_right]"; [iAccu..|].
    wp_apply ("IH" $! _ _ _ (if get_bit label (length pref) then t2 else t1)
      with "[][][][][][Hcb Hown_child_left]") as "* @"; try iPureIntro.
    { by repeat case_match. }
    { by repeat case_match. }
    { by eapply prefix_total_snoc. }
    { len. }
    { by repeat case_match. }
    { iFrame "∗#".
      case_match; iFrame. }
    destruct err; iNamed "Hgenie"; wp_auto.
    { iApply "HΦ".  by iFrame. }
    rewrite Hcode.
    iClear "IH".
    iDestruct ("Hclose" with "Hn0 Hcnb") as "@".
    wp_auto.

    (* TODO: combine these conditions? *)
    iDestruct (condition_bool (get_bit label (length pref))
      with "[Hown_tree] []") as "[Hown_n'_left Hown_n'_right]"; [iAccu..|].
    iDestruct (condition_bool (get_bit label (length pref))
      with "[Hown_child_right] []") as "[Hown_child_left Hown_child_right]"; [iAccu..|].
    (* TODO: why do these simplifications show up? *)
    assert (∀ (b : bool) T (x0 x1 x2 : T),
      (if b then if b then x0 else x1 else x2)
      = (if b then x0 else x2)) as Ht0.
    { intros. by repeat case_match. }
    assert (∀ (b : bool) T (x0 x1 x2 : T),
      (if b then x0 else if b then x1 else x2)
      = (if b then x0 else x2)) as Ht1.
    { intros. by repeat case_match. }
    rewrite !{}Ht0 !{}Ht1.

    wp_apply (wp_node_getHash
      (if get_bit label (length pref) then t1 else t')
      with "[Hown_child_left Hown_n'_right]").
    { iFrame "#". case_match; iFrame. }
    iIntros "*". iNamedSuffix 1 "0". wp_auto.
    wp_apply (wp_node_getHash
      (if get_bit label (length pref) then t' else t2)
      with "[Hown_child_right Hown_n'_left]").
    { iFrame "#". case_match; iFrame. }
    iIntros "*". iNamedSuffix 1 "1". wp_auto.
    iPersist "Hsl_hash0 Hsl_hash1".

    iApply wp_fupd.
    wp_apply (wp_compInnerHash with "[Hsl_hash0 Hsl_hash1]") as "* @".
    { iFrame "#". }
    iPersist "Hsl_hash".
    iModIntro. iApply "HΦ".
    iFrame "Hn0_in".
    iExists _. iSplit; [done|].
    simpl.
    iFrame "Hnode".
    iFrame "∗#".

  (* cut. *)
  - wp_auto.
    wp_apply std.wp_Assert; [done|].
    iApply "HΦ". by iFrame.
Qed.

Lemma wp_newShell sl_label label sl_sibs sibs_enc (depth depth_rem : nat) :
  {{{
    is_pkg_init merkle ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_sibs" ∷ sl_sibs ↦*□ sibs_enc ∗
    "%Hlen_sibs" ∷ ⌜length sibs_enc = (depth_rem * Z.to_nat cryptoffi.hash_len)%nat⌝ ∗
    "%Heq_depth" ∷ ⌜depth + depth_rem ≤ max_depth⌝
  }}}
  @! merkle.newShell #(W64 depth) #sl_label #sl_sibs
  {{{
    sibs n, RET #n;
    "%Henc_sibs" ∷ ⌜sibs_enc = mjoin (reverse sibs)⌝ ∗
    "%Hlen_sibs" ∷ ⌜Forall (λ x, length x = Z.to_nat $ cryptoffi.hash_len) sibs⌝ ∗
    "Hown_tree" ∷ own_tree n (pure_newShell' depth label sibs) 1
  }}}.
Proof.
  iLöb as "IH" forall (sl_sibs sibs_enc depth depth_rem).
  wp_start as "@". wp_auto.
  iDestruct (own_slice_len with "Hsl_sibs") as %[].

  wp_if_destruct.
  { iApply "HΦ".
    destruct sibs_enc. 2: { simpl in *. word. }
    instantiate (1:=[]).
    repeat iSplit; try done.
    iDestruct (is_pkg_init_access with "[$]") as "/= #Hinit".
    rewrite /is_initialized. iNamed "Hinit".
    by iFrame "#". }
  destruct depth_rem; [word|].

  replace (Z.to_nat 32) with (32%nat) in * by lia.
  iDestruct (own_slice_wf with "Hsl_sibs") as %?.
  wp_apply (wp_slice_slice with "[$Hsl_sibs]")
    as "{Hsl_sibs} (_&#Hsplit_l&#Hsplit_r)"; [word|].
  wp_pure; [word|].
  wp_auto.
  wp_apply wp_alloc as "* Hcut".
  wp_apply wp_alloc as "* Hinner".
  wp_apply (wp_node_getChild with "[$Hinner]").
  { iFrame "#". }
  iIntros "* [_ @]". wp_auto.

  replace (sint.nat (W64 0)) with 0%nat by word.
  rewrite subslice_from_start.
  replace (sint.nat (word.sub _ _)) with (depth_rem * 32)%nat.
  2: { simpl in *. word. }
  replace (word.add _ _) with (W64 (S depth)) by word.
  wp_apply "IH" as "* @".
  { iFrame "#".
    instantiate (1:=depth_rem).
    rewrite length_take.
    word. }
  replace (uint.nat (W64 _)) with depth by word.
  iDestruct ("Hclose" with "Hcb Hcnb") as "@".
  wp_auto.

  iDestruct (condition_bool (get_bit label depth)
    with "[Hcut] [Hown_tree]") as "[Htree_l Htree_r]"; [iAccu..|].
  wp_apply (wp_node_getHash
    (if get_bit label depth then Cut _ else _)
    with "[Htree_l]").
  { iFrame "#". case_match; [|iFrame].
    iFrame "∗#".
    iPureIntro. intuition.
    rewrite length_drop. word. }
  iIntros "*". iNamedSuffix 1 "0". wp_auto.
  wp_apply (wp_node_getHash
    (if get_bit label depth then _ else Cut _)
    with "[Htree_r]").
  { iFrame "#". case_match; [iFrame|].
    iFrame "∗#".
    iPureIntro. intuition.
    rewrite length_drop. word. }
  iIntros "*". iNamedSuffix 1 "1". wp_auto.

  wp_apply wp_compInnerHash. { iFrame "#". }
  iIntros "*". iNamedSuffix 1 "_inner".
  iPersist "Hsl_hash_inner". wp_auto.
  iApply "HΦ".
  instantiate (1:=drop (depth_rem * 32) sibs_enc :: sibs).
  repeat iSplit; try iPureIntro.
  - rewrite reverse_cons join_app join_singleton -Henc_sibs take_drop //.
  - apply Forall_cons; split; [|done]. rewrite length_drop. word.
  - iFrame "∗#".
Qed.

Definition wish_proofToTree label proof_enc t : iProp Σ :=
  ∃ sibs oleaf LeafLabel LeafVal tail,
  let IsOtherLeaf := match oleaf with None => false | _ => true end in
  let proof := Proof.mk' (mjoin (reverse sibs)) IsOtherLeaf LeafLabel LeafVal in

  "%Hlen_label" ∷ ⌜Z.of_nat $ length label = cryptoffi.hash_len⌝ ∗
  "Henc_proof" ∷ Proof.wish proof_enc proof tail ∗
  "%Hlen_sibs" ∷ ⌜Forall (λ x, length x = Z.to_nat $ cryptoffi.hash_len) sibs⌝ ∗
  "%Heq_depth" ∷ ⌜length sibs ≤ max_depth⌝ ∗
  "Holeaf" ∷ match oleaf with None => True | Some (l, v) =>
    "%Hlen_olabel" ∷ ⌜Z.of_nat $ length l = cryptoffi.hash_len⌝ ∗
    "%Heq_olabel" ∷ ⌜label ≠ l⌝ ∗
    "->" ∷ ⌜LeafLabel = l⌝ ∗
    "->" ∷ ⌜LeafVal = v⌝
    end ∗

  "%Hcode" ∷ ⌜pure_proofToTree label sibs oleaf = Some t⌝.

Lemma wish_proofToTree_det l p t0 t1 :
  wish_proofToTree l p t0 -∗
  wish_proofToTree l p t1 -∗
  ⌜t0 = t1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (Proof.wish_det with "Henc_proof0 Henc_proof1") as %[[=] ->].
  opose proof (join_same_len_inj _ (reverse _) (reverse _) _ _ _ _)
    as Heq_s; try done.
  2: { by apply Forall_reverse. }
  2: { by apply Forall_reverse. }
  { word. }
  apply (inj _) in Heq_s.
  destruct oleaf as [[]|].
  2: { destruct oleaf0; try done. by simplify_eq/=. }
  iNamedSuffix "Holeaf0" "0".
  destruct oleaf0 as [[]|]; try done.
  iNamedSuffix "Holeaf1" "1".
  by simplify_eq/=.
Qed.

(* invariants on proofToTree tree that allow subsequent puts.
some invs established with additional info in wish,
which is why we make it the precond. *)
Lemma proofToTree_post label proof_enc t :
  wish_proofToTree label proof_enc t -∗
  ("%Hlabel_None" ∷ ⌜is_entry t label None⌝ ∗
  "%Hcutless" ∷ ⌜is_cutless_path t label⌝ ∗
  "%Hlimit" ∷ ⌜is_limit t⌝ ∗
  "%Hsorted" ∷ ⌜is_sorted t⌝ ∗
  "%Hconst_label_len" ∷ ⌜is_const_label_len t⌝).
Proof.
  iIntros "@".
  opose proof (newShell_None label sibs).
  opose proof (cutless_on_newShell label sibs).
  opose proof (limit_on_newShell label sibs _); [word|].
  opose proof (sorted_on_newShell label sibs).
  opose proof (const_label_on_newShell label sibs).
  destruct oleaf as [[]|]; simplify_eq/=; [|done].
  iNamed "Holeaf".

  eapply old_entry_over_put in Hcode as ?; [|done..].
  eapply cutless_path_over_put in Hcode as ?; [|done].
  eapply is_limit_over_put in Hcode as ?; [|done].
  eapply is_sorted_over_put in Hcode as ?; [|done].
  eapply const_label_len_over_put in Hcode as ?; [|done|word].
  by opose proof (put_impl_cutless_pre _ _ _ _).
Qed.

Tactic Notation "intro_wish" := iIntros "(%&%&@)".

Lemma wp_proofToTree sl_label label sl_proof proof :
  {{{
    is_pkg_init merkle ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_proof" ∷ sl_proof ↦*□ proof
  }}}
  @! merkle.proofToTree #sl_label #sl_proof
  {{{
    tr err, RET (#tr, #err);
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ t, wish_proofToTree label proof t
      | false =>
        ∃ t,
        "Hwish" ∷ wish_proofToTree label proof t ∗
        "Hown_tree" ∷ own_tree tr t 1
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  iDestruct (own_slice_len with "Hsl_label") as %[].
  wp_if_destruct.
  2: { iApply "HΦ". intro_wish. word. }
  wp_apply (Proof.wp_dec with "[$Hsl_proof]") as "* Hpost".
  destruct err; wp_auto.
  { iApply "HΦ". intro_wish. iApply "Hpost". iFrame. }
  iNamedSuffix "Hpost" "_dec".
  iNamed "Hown_obj_dec".
  iDestruct (own_slice_len with "Hsl_Siblings") as %[Hlen_sl_sibs ?].
  wp_auto.
  wp_if_destruct.
  2: { iApply "HΦ". intro_wish.
    iDestruct (Proof.wish_det with "Hwish_dec Henc_proof") as %[-> ->].
    iClear "Hwish_dec". simpl in *.
    apply join_same_len_length in Hlen_sibs.
    rewrite -join_length_reverse in Hlen_sibs.
    word. }
  wp_if_destruct.
  { iApply "HΦ". intro_wish.
    iDestruct (Proof.wish_det with "Hwish_dec Henc_proof") as %[-> ->].
    iClear "Hwish_dec". simpl in *.
    apply join_same_len_length in Hlen_sibs.
    rewrite -join_length_reverse in Hlen_sibs.
    word. }

  replace (W64 0) with (W64 0%nat) by word.
  iDestruct "Hsl_Siblings" as "#Hsl_Siblings".
  wp_apply wp_newShell as "* @".
  { iFrame "#".
    (* [Require ZifyNat] for [Nat.div] reasoning. *)
    instantiate (1:=(length obj.(Proof.Siblings) `div` 32)%nat).
    word. }
  destruct obj. simplify_eq/=.
  rewrite join_length_reverse in Hlen_sl_sibs.
  apply join_same_len_length in Hlen_sibs as ?.
  replace (pure_newShell' _ _ _) with (pure_newShell label sibs) by done.

  destruct IsOtherLeaf; wp_auto.
  2: { iApply "HΦ". iFrame "Hown_tree".
    repeat iSplit; try done.
    iExists _, None. iFrame.
    iPureIntro; repeat split; try done; word. }

  iDestruct (own_slice_len with "Hsl_LeafLabel") as %[].
  wp_if_destruct.
  2: { iApply "HΦ". intro_wish.
    destruct oleaf as [[]|].
    2: { iDestruct (Proof.wish_det with "Hwish_dec Henc_proof") as %[[=] _]. }
    iDestruct (Proof.wish_det with "Hwish_dec Henc_proof") as %[[=] ->].
    iNamed "Holeaf". simplify_eq/=. word. }

  iPersist "Hsl_LeafLabel Hsl_LeafVal".
  wp_apply bytes.wp_Equal as "_".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". intro_wish.
    destruct oleaf as [[]|].
    2: { iDestruct (Proof.wish_det with "Hwish_dec Henc_proof") as %[[=] _]. }
    iDestruct (Proof.wish_det with "Hwish_dec Henc_proof") as %[[=] ->].
    by iNamed "Holeaf". }

  wp_apply (wp_put with "[$tr $Hown_tree]") as "* @".
  5: { iFrame "#". }
  { apply limit_on_newShell. word. }
  { word. }
  { apply const_label_on_newShell. }
  { apply sorted_on_newShell. }
  destruct err; iNamed "Hgenie"; wp_auto.
  { iApply "HΦ". intro_wish.
    destruct oleaf as [[]|].
    2: { iDestruct (Proof.wish_det with "Hwish_dec Henc_proof") as %[[=] _]. }
    iDestruct (Proof.wish_det with "Hwish_dec Henc_proof") as %[[=] ->].
    iNamed "Holeaf". simplify_eq/=.
    opose proof (join_same_len_inj _ (reverse _) (reverse _) _ _ _ _)
      as Heq_s; try done.
    2: { by apply Forall_reverse. }
    2: { by apply Forall_reverse. }
    { word. }
    apply (inj _) in Heq_s.
    simplify_eq/=. iApply "Hgenie". iPureIntro.
    by eapply put_impl_cutless_pre. }

  iApply "HΦ".
  iFrame "Hown_tree".
  iExists _, (Some (_, _)).
  iFrame. iPureIntro. repeat split; try done; word.
Qed.

(* make defn to prevent unfolding the nat. *)
Definition w64_len := 8%nat.
Hint Unfold w64_len : word.

Lemma wp_node_find n t d0 sl_label d1 label (getProof : bool) :
  (* limit needed to prevent depth overflow. *)
  is_limit t →
  is_cutless_path t label →
  {{{
    is_pkg_init merkle ∗
    "Hown_tree" ∷ own_tree n t d0 ∗
    "Hsl_label_in" ∷ sl_label ↦*{d1} label ∗
    (* [is_sorted] lets us know that put (found-label) on
    bigger shell (input-label) goes down recur tree, not Cut. *)
    "%Hsorted" ∷ ⌜is_sorted t⌝
  }}}
  n @ (ptrT.id merkle.node.id) @ "find" #(W64 0) #sl_label #getProof
  {{{
    (found : bool) sl_foundLabel foundLabel sl_foundVal foundVal sl_sibs sibs_enc oleaf,
    RET (#found, #sl_foundLabel, #sl_foundVal, #sl_sibs);
    "Hown_tree" ∷ own_tree n t d0 ∗
    "Hsl_label" ∷ sl_label ↦*{d1} label ∗

    "#Hsl_foundLabel" ∷ sl_foundLabel ↦*□ foundLabel ∗
    "#Hsl_foundVal" ∷ sl_foundVal ↦*□ foundVal ∗
    "Hsl_sibs" ∷ sl_sibs ↦* sibs_enc ∗
    "Hcap_sibs" ∷ own_slice_cap w8 sl_sibs 1 ∗

    "%Hfind" ∷ ⌜find t label = oleaf⌝ ∗
    "%Holeaf" ∷
      ⌜match oleaf with
      | None => found = false
      | Some (fl, fv) => found = true ∧ foundLabel = fl ∧ foundVal = fv
      end⌝ ∗
    "Hproof" ∷ (if negb getProof then True else
      ∃ sibs t' sibsLen hash,
      (* subset (find makes only partial proof) of [wish_proofToTree]. *)
      "%Hlen_sibs" ∷ ⌜Forall (λ x, length x = Z.to_nat cryptoffi.hash_len) sibs⌝ ∗
      "%Heq_depth" ∷ ⌜length sibs ≤ max_depth⌝ ∗
      "%Hcode" ∷ ⌜pure_proofToTree label sibs oleaf = Some t'⌝ ∗

      "%Henc_sibs" ∷ ⌜sibs_enc = sibsLen ++ mjoin (reverse sibs)⌝ ∗
      "%Hlen_sibsLen" ∷ ⌜length sibsLen = w64_len⌝ ∗
      "#His_hash_orig" ∷ is_cut_tree t hash ∗
      "#His_hash_tape" ∷ is_cut_tree t' hash)
  }}}.
Proof.
  autounfold with merkle.
  intros Hlimit Hcutless.
  remember max_depth as limit.
  remember [] as pref.
  replace (0%nat) with (length pref) in * |-* by (by subst).
  replace (W64 0) with (W64 (length pref)) by (by subst).
  assert ((length pref) + limit = max_depth) as Heq_depth.
  { subst. simpl. word. }
  clear Heqlimit Heqpref.
  iLöb as "IH" forall (t limit pref n Hcutless Hlimit Heq_depth).
  iIntros (Φ) "(#?&@) HΦ".
  wp_method_call. wp_call. wp_auto.
  wp_if_destruct.

  { iClear "IH".
    iDestruct (own_empty_tree with "Hown_tree") as %->.
    wp_if_destruct.
    + wp_apply wp_getProofCap as "* %"; [word|].
      wp_apply wp_slice_make3 as "* (Hsl_sibs&Hcap_sibs&_)"; [word|].
      iDestruct (own_tree_to_hash with "Hown_tree") as "[% #His_hash]".
      iApply "HΦ". iFrame.
      iDestruct own_slice_nil as "$".
      iSplit; [done|].
      case_match; try done. iSplit; [done|].
      iExists []. simpl.
      repeat (iSplit || iExists _); try done;
        [word|by list_simplifier|len].
    + iApply "HΦ". iFrame.
      iDestruct own_slice_nil as "$".
      iDestruct own_slice_nil as "$".
      by iDestruct own_slice_cap_nil as "$". }

  destruct t; simpl in *; iNamed "Hown_tree"; try done;
    iNamed "Hown_tree"; wp_auto.

  - iClear "IH".
    wp_if_destruct.
    + wp_apply wp_getProofCap as "* %"; [word|].
      wp_apply wp_slice_make3 as "* (Hsl_sibs&Hcap_sibs&_)"; [word|].
      iApply "HΦ". iFrame "∗#".
      iSplit; [done|].
      iSplit; [done|].
      iExists []. simpl. rewrite pure_put_unfold.
      repeat (iSplit || iExists _); try done;
        [word|by list_simplifier|len].
    + iApply "HΦ". iFrame "∗#".
      iDestruct own_slice_nil as "$".
      by iDestruct own_slice_cap_nil as "$".

  - destruct limit; [done|]. intuition.
    wp_apply (wp_node_getChild with "[$Hnode $Hsl_label_in]") as "*".
    iIntros "[Hsl_label_in H]". iNamed "H". wp_auto.
    remember (length pref) as depth.
    replace (uint.nat (W64 depth)) with depth by word.
    remember (get_bit label depth) as bit.
    iDestruct (condition_bool bit with "[Hown_child1] [Hown_child0]")
      as "[Hown_child_l Hown_child_r]"; [iAccu..|].
    replace (word.add _ _) with (W64 (S depth)) by word.
    replace (S _) with (length (pref ++ [bit])) in * |-* by len.

    wp_apply ("IH" with "[//][][][Hown_child_l Hsl_label_in]") as "* @".
    { by case_match. }
    { len. }
    { iFrame "∗#". repeat iSplit; try done.
      - case_match; iFrame.
      - by case_match. }
    iClear "IH".
    assert (∀ (b : bool) T (x0 x1 : T),
      (if b then if b then x0 else x1 else if b then x1 else x0) = x0) as Hif.
    { intros. by repeat case_match. }

    wp_if_destruct; simpl in *; iNamed "Hproof".
    + iDestruct ("Hclose" with "Hcb Hcnb") as "@".
      rewrite !Hif.
      wp_apply (wp_node_getHash (if bit then _ else _)
        with "[Hown_child_r]") as "* H".
      { iFrame "#". destruct bit; iFrame. }
      iNamedSuffix "H" "0".
      wp_apply (wp_slice_append with "[$Hsl_sibs $Hcap_sibs]")
        as "* (Hsl_sibs & Hcap_sibs & _)".
      { iFrame "#". }
      iApply "HΦ". iFrame "Htree_hash ∗#".
      iSplitL. { destruct bit; iFrame. }
      iSplit; [done|].
      iSplit; [done|].

      iExists (hash1 :: sibs).
      iExists (Inner (if bit then Cut hash1 else t') (if bit then t' else Cut hash1)).
      simpl.
      iNamed "Htree_hash".
      iAssert (⌜hash0 = (if bit then h1 else h0) ∧
        hash1 = (if bit then h0 else h1)⌝)%I as %[-> ->].
      { clear. case_match.
        - iDestruct (is_cut_tree_det with "Hchild0 His_hash0") as %->.
          by iDestruct (is_cut_tree_det with "Hchild1 His_hash_orig") as %->.
        - iDestruct (is_cut_tree_det with "Hchild0 His_hash_orig") as %->.
          by iDestruct (is_cut_tree_det with "Hchild1 His_hash0") as %->. }
      iDestruct (is_cut_tree_len with "Hchild0") as %?.
      iDestruct (is_cut_tree_len with "Hchild1") as %?.
      repeat (iSplit || iExists _); try done; try iPureIntro.
      * apply Forall_cons; split; [|done].
        destruct bit; word.
      * word.
      * replace (S _) with (length (pref ++ [get_bit label (length pref)])) by len.
        destruct (find' _ _ _) as [[]|] eqn:?; simplify_eq/=; [|done].
        opose proof (find_to_bit_eq t1 t2 pref _ _ _ _ _ _) as Ht.
        { simpl.
          by replace (S _) with (length (pref ++ [get_bit label (length pref)])) by len. }
        1-2: done.
        rewrite -{}Ht.
        rewrite Hif.
        rewrite Hcode.
        assert (∀ (b : bool) T (x0 x1 x2 : T),
          (if b then if b then x0 else x1 else x2) = if b then x0 else x2) as ->.
        { intros. by repeat case_match. }
        assert (∀ (b : bool) T (x0 x1 x2 : T),
          (if b then x0 else if b then x1 else x2) = if b then x0 else x2) as ->.
        { intros. by repeat case_match. }
        done.
      * list_simplifier. f_equal.
        rewrite reverse_cons join_app.
        by list_simplifier.
      * by destruct bit.
      * by destruct bit.
    + iDestruct ("Hclose" with "Hcb Hcnb") as "@".
      rewrite !{}Hif.
      iApply "HΦ". iFrame "∗#".
      iSplit; [|done].
      destruct bit; iFrame.
Qed.

Definition wish_NonMemb label proof hash : iProp Σ :=
  ∃ t,
  "Hwish_toTree" ∷ wish_proofToTree label proof t ∗
  "#His_hash" ∷ is_cut_tree t hash.

Lemma wish_NonMemb_det l p h0 h1 :
  wish_NonMemb l p h0 -∗
  wish_NonMemb l p h1 -∗
  ⌜h0 = h1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (wish_proofToTree_det with "Hwish_toTree0 Hwish_toTree1") as %[].
  simplify_eq/=.
  iDestruct (is_cut_tree_det with "His_hash0 His_hash1") as %->.
  done.
Qed.

Lemma wp_VerifyNonMemb sl_label label sl_proof proof :
  {{{
    is_pkg_init merkle ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_proof" ∷ sl_proof ↦*□ proof
  }}}
  @! merkle.VerifyNonMemb #sl_label #sl_proof
  {{{
    sl_hash hash err, RET (#sl_hash, #err);
    "#Hsl_hash" ∷ sl_hash ↦*□ hash ∗
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ hash, wish_NonMemb label proof hash
      | false =>
        ∃ m,
        "#His_proof" ∷ wish_NonMemb label proof hash ∗
        "#His_map" ∷ is_map m hash ∗
        "%Hlook" ∷ ⌜m !! label = None⌝
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_proofToTree as "* @".
  { iFrame "#". }
  destruct err; wp_auto.
  { iApply "HΦ".
    iDestruct own_slice_nil as "$".
    intro_wish. iApply "Hgenie". iFrame. }
  iNamed "Hgenie".
  iDestruct (proofToTree_post with "[$]") as "#@".
  wp_apply (wp_node_getHash with "[$Hown_tree]") as "* @".
  iApply "HΦ".
  iDestruct (is_cut_tree_len with "His_hash") as %?.
  iDestruct (is_map_invert hash) as "[% #His_map]"; [done|].
  iFrame "∗#%".

  iNamed "His_map".
  iDestruct (full_entry_txfer with "[$]") as %?; [done..|].
  subst. iPureIntro.
  by rewrite -entry_eq_lookup.
Qed.

Definition wish_Memb label val proof hash : iProp Σ :=
  ∃ t0 t1,
  "Hwish_toTree" ∷ wish_proofToTree label proof t0 ∗
  "%Hcode" ∷ ⌜pure_put t0 label val = Some t1⌝ ∗
  "#His_hash" ∷ is_cut_tree t1 hash.

Lemma wish_Memb_det l v p h0 h1 :
  wish_Memb l v p h0 -∗
  wish_Memb l v p h1 -∗
  ⌜h0 = h1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (wish_proofToTree_det with "Hwish_toTree0 Hwish_toTree1") as %->.
  simplify_eq/=.
  iDestruct (is_cut_tree_det with "His_hash0 His_hash1") as %->.
  done.
Qed.

Lemma wp_VerifyMemb sl_label label sl_val val sl_proof proof :
  {{{
    is_pkg_init merkle ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_val" ∷ sl_val ↦*□ val ∗
    "#Hsl_proof" ∷ sl_proof ↦*□ proof
  }}}
  @! merkle.VerifyMemb #sl_label #sl_val #sl_proof
  {{{
    sl_hash hash err, RET (#sl_hash, #err);
    "#Hsl_hash" ∷ sl_hash ↦*□ hash ∗
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ hash, wish_Memb label val proof hash
      | false =>
        ∃ m,
        "#His_proof" ∷ wish_Memb label val proof hash ∗
        "#His_map" ∷ is_map m hash ∗
        "%Hlook" ∷ ⌜m !! label = Some val⌝
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_proofToTree as "* @".
  { iFrame "#". }
  destruct err; wp_auto.
  { iApply "HΦ".
    iDestruct own_slice_nil as "$".
    intro_wish. iApply "Hgenie". iFrame. }
  iNamed "Hgenie".
  iDestruct (proofToTree_post with "[$]") as "#@".
  iNamed "Hwish".

  wp_apply (wp_put with "[$tr $Hown_tree]") as "* @"; try done.
  { iFrame "#". }
  destruct err; iNamed "Hgenie".
  { iExFalso. by iApply "Hgenie". }
  wp_apply wp_Assert; [done|].

  wp_apply (wp_node_getHash with "[$Hown_tree]") as "* @".
  iApply "HΦ".
  iDestruct (is_cut_tree_len with "His_hash") as %?.
  iDestruct (is_map_invert hash) as "[% #His_map]"; [done|].
  iFrame "∗#%".

  iNamed "His_map".
  iDestruct (full_entry_txfer with "[$]") as %?.
  { by eapply put_new_entry. }
  { by eapply cutless_new_put. }
  { by eapply is_limit_over_put. }
  subst. iPureIntro.
  by rewrite -entry_eq_lookup.
Qed.

Definition wish_Update label val proof hashOld hashNew : iProp Σ :=
  ∃ tOld tNew,
  "Hwish_toTree" ∷ wish_proofToTree label proof tOld ∗
  "%Hcode" ∷ ⌜pure_put tOld label val = Some tNew⌝ ∗
  "#His_hash_old" ∷ is_cut_tree tOld hashOld ∗
  "#His_hash_new" ∷ is_cut_tree tNew hashNew.

Lemma wish_Update_det l v p hO0 hO1 hN0 hN1 :
  wish_Update l v p hO0 hN0 -∗
  wish_Update l v p hO1 hN1 -∗
  ⌜hO0 = hO1 ∧ hN0 = hN1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (wish_proofToTree_det with "Hwish_toTree0 Hwish_toTree1") as %->.
  simplify_eq/=.
  iDestruct (is_cut_tree_det with "His_hash_old0 His_hash_old1") as %->.
  iDestruct (is_cut_tree_det with "His_hash_new0 His_hash_new1") as %->.
  done.
Qed.

Lemma wp_VerifyUpdate sl_label label sl_val val sl_proof proof :
  {{{
    is_pkg_init merkle ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_val" ∷ sl_val ↦*□ val ∗
    "#Hsl_proof" ∷ sl_proof ↦*□ proof
  }}}
  @! merkle.VerifyUpdate #sl_label #sl_val #sl_proof
  {{{
    sl_oldHash oldHash sl_newHash newHash err,
    RET (#sl_oldHash, #sl_newHash, #err);
    "#Hsl_oldHash" ∷ sl_oldHash ↦*□ oldHash ∗
    "#Hsl_newHash" ∷ sl_newHash ↦*□ newHash ∗
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ hO hN, wish_Update label val proof hO hN
      | false =>
        ∃ mOld mNew,
        "#His_proof" ∷ wish_Update label val proof oldHash newHash ∗
        "#His_map_old" ∷ is_map mOld oldHash ∗
        "#His_map_new" ∷ is_map mNew newHash ∗
        "->" ∷ ⌜mNew = <[label:=val]>mOld⌝ ∗
        "%Hlook" ∷ ⌜mOld !! label = None⌝
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_proofToTree as "* @".
  { iFrame "#". }
  destruct err; wp_auto.
  { iApply "HΦ".
    iDestruct own_slice_nil as "$".
    intro_wish. iApply "Hgenie". iFrame. }
  iNamed "Hgenie".
  iDestruct (proofToTree_post with "[$]") as "#@".
  iNamed "Hwish".

  wp_apply (wp_node_getHash with "[$Hown_tree]") as "*".
  iNamedSuffix 1 "_old". wp_auto.
  wp_apply (wp_put with "[$tr $Hown_tree_old]") as "* @"; try done.
  { iFrame "#". }
  destruct err; iNamed "Hgenie".
  { iExFalso. by iApply "Hgenie". }
  wp_apply wp_Assert; [done|].
  wp_apply (wp_node_getHash with "[$Hown_tree]") as "*".
  iNamedSuffix 1 "_new". wp_auto.

  iApply "HΦ".
  iDestruct (is_cut_tree_len with "His_hash_old") as %?.
  iDestruct (is_cut_tree_len with "His_hash_new") as %?.
  iDestruct (is_map_invert hash) as "[% #His_map_old]"; [done|].
  iDestruct (is_map_invert hash0) as "[% #His_map_new]"; [done|].
  iFrame "Hsl_hash_old Hsl_hash_new".
  iFrame "∗#%".

  iNamedSuffix "His_map_old" "_old".
  iNamedSuffix "His_map_new" "_new".
  simplify_eq/=. iSplit.
  - rewrite map_eq_iff. iIntros (label').
    destruct (decide (label = label')); subst; simpl_map.
    + rewrite -entry_eq_lookup.
      iApply full_entry_txfer; [..|by iFrame "#"].
      { by eapply put_new_entry. }
      { by eapply cutless_new_put. }
      { by eapply is_limit_over_put. }
    + remember (to_map t0 !! label') as e. symmetry in Heqe.
      rewrite -!entry_eq_lookup in Heqe |-*.
      iDestruct (cut_full_over_put _ t0 _ t1 with "[$][][//][]") as %?.
      { iFrame "#". }
      { iFrame "#". }
      iPureIntro.
      by eapply old_entry_over_put.
  - rewrite -entry_eq_lookup.
    by iApply full_entry_txfer; [..|by iFrame "#"].
Qed.

Lemma wp_node_prove n t d0 sl_label d1 label getProof :
  {{{
    is_pkg_init merkle ∗
    "Hown_tree" ∷ own_tree n t d0 ∗
    "Hsl_label" ∷ sl_label ↦*{d1} label ∗

    "%His_limit" ∷ ⌜is_limit t⌝ ∗
    "%His_cutless" ∷ ⌜is_cutless_path t label⌝ ∗
    "%Hsorted" ∷ ⌜is_sorted t⌝ ∗
    "%Hlen_label" ∷ ⌜Z.of_nat $ length label = cryptoffi.hash_len⌝ ∗
    "%Hconst_len" ∷ ⌜is_const_label_len t⌝
  }}}
  n @ (ptrT.id merkle.node.id) @ "prove" #sl_label #getProof
  {{{
    oval inTree sl_val val sl_proof proof, RET (#inTree, #sl_val, #sl_proof);
    "Hown_tree" ∷ own_tree n t d0 ∗
    "Hsl_label" ∷ sl_label ↦*{d1} label ∗

    "#Hsl_val" ∷ sl_val ↦*□ val ∗
    "Hsl_proof" ∷ sl_proof ↦* proof ∗

    "%His_entry" ∷ ⌜is_entry t label oval⌝ ∗
    "%Hoval" ∷
      ⌜match oval with
      | None => inTree = false
      | Some v => inTree = true ∧ val = v
      end⌝ ∗
    "Hproof" ∷ (if negb getProof then True else
      ∃ hash,
      "#His_proof" ∷
        match oval with
        | None => wish_NonMemb label proof hash
        | Some v => wish_Memb label v proof hash
        end ∗
      "#His_hash" ∷ is_cut_tree t hash)
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply (wp_node_find with "[$Hown_tree $Hsl_label]") as "* @"; try done.

  wp_bind (If _ _ _).
  wp_apply (wp_wand _ _ _
    (λ v,
    ∃ sibs_enc',
    "->" ∷ ⌜v = execute_val⌝ ∗
    "proof" ∷ proof_ptr ↦ sl_sibs ∗
    "Hsl_sibs" ∷ sl_sibs ↦* sibs_enc' ∗
    "Hproof" ∷ (if negb getProof then True else
      ∃ sibs t' hash,
      "%Hlen_sibs" ∷ ⌜Forall (λ x, length x = Z.to_nat cryptoffi.hash_len) sibs⌝ ∗
      "%Heq_depth" ∷ ⌜length sibs ≤ max_depth⌝ ∗
      "%Hcode" ∷ ⌜pure_proofToTree label sibs oleaf = Some t'⌝ ∗

      "%Henc_sibs" ∷ ⌜sibs_enc' = u64_le (length (mjoin (reverse sibs))) ++ mjoin (reverse sibs)⌝ ∗
      "#His_hash_orig" ∷ is_cut_tree t hash ∗
      "#His_hash_tape" ∷ is_cut_tree t' hash)
    )%I
    with "[proof Hsl_sibs Hproof]"
  ) as "* @".
  { wp_if_destruct.
    2: { by iFrame "∗#". }
    iNamed "Hproof".
    subst.
    iDestruct (own_slice_len with "Hsl_sibs") as %[Hlen_sibs_enc ?].
    rewrite app_length Hlen_sibsLen in Hlen_sibs_enc.
    wp_apply (primitive.wp_UInt64Put with "[$Hsl_sibs]") as "Hsl_sibs"; [word|].
    iFrame "∗#".
    iSplit; [done|]. iFrame "%".
    iPureIntro. repeat f_equal. word. }

  wp_if_destruct.
  2: {
    destruct oleaf as [[]|]; destruct_and?; simplify_eq/=.
    wp_if_destruct.
    2: { iApply ("HΦ" $! None). iFrame "∗#". iSplit; try done. by iExists _. }
    iNamed "Hproof".
    wp_apply (marshal.wp_WriteBool with "[$Hsl_sibs $Hcap_sibs]") as "* [Hsl Hcap]".
    wp_apply (marshal.wp_WriteInt with "[$Hsl $Hcap]") as "* [Hsl Hcap]".
    wp_apply (marshal.wp_WriteInt with "[$Hsl $Hcap]") as "* [Hsl Hcap]".
    iApply ("HΦ" $! None).
    iFrame "∗#".
    iSplit. { by iExists _. }
    iSplit; [done|].
    iExists sibs, None.
    iFrame "%".

    iExists [], [], [].
    rewrite /Proof.wish /Proof.encodes /=.
    iExists _. repeat iSplit; try done; [|by list_simplifier].
    erewrite join_same_len_length.
    2: { by apply Forall_reverse. }
    rewrite length_reverse.
    word. }
  destruct oleaf as [[]|]; destruct_and?; simplify_eq/=.

  wp_apply (bytes.wp_Equal with "[Hsl_label]") as "[_ Hsl_label]".
  { iFrame "∗#". }
  wp_if_destruct.
  2: {
    wp_if_destruct.
    2: { iApply ("HΦ" $! None). iFrame "∗#". iSplit; try done. by iExists _. }
    iNamed "Hproof".
    wp_apply (marshal.wp_WriteBool with "[$Hsl_sibs $Hcap_sibs]") as "* [Hsl Hcap]".
    wp_apply (marshal.wp_WriteInt with "[$Hsl $Hcap]") as "* [Hsl Hcap]".
    wp_apply (marshal.wp_WriteBytes with "[$Hsl $Hcap]") as "* (Hsl&Hcap&_)".
    { iFrame "#". }
    wp_apply (marshal.wp_WriteInt with "[$Hsl $Hcap]") as "* [Hsl Hcap]".
    wp_apply (marshal.wp_WriteBytes with "[$Hsl $Hcap]") as "* (Hsl&Hcap&_)".
    { iFrame "#". }
    iApply ("HΦ" $! None).
    iFrame "∗#".
    iSplit. { by iExists _. }
    iSplit; [done|].
    iExists sibs, (Some (_, _)).
    eapply find_on_const_label_len in Hconst_len as ?; [|done].
    iFrame (Hcode) "%".

    iExists _, _, []. repeat iSplit; [|done..].
    rewrite /Proof.wish /Proof.encodes /=.
    iDestruct (own_slice_len with "Hsl_foundLabel") as %[].
    iDestruct (own_slice_len with "Hsl_foundVal") as %[].
    iExists _. repeat iSplit; try done; [|word..|].
    2: { list_simplifier. iPureIntro. repeat f_equal; word. }
    erewrite join_same_len_length.
    2: { by apply Forall_reverse. }
    rewrite length_reverse.
    word. }

  wp_if_destruct.
  2: { iApply ("HΦ" $! (Some _)). iFrame "∗#". iSplit; try done. by iExists _. }
  iNamed "Hproof".
  wp_apply (marshal.wp_WriteBool with "[$Hsl_sibs $Hcap_sibs]") as "* [Hsl Hcap]".
  wp_apply (marshal.wp_WriteInt with "[$Hsl $Hcap]") as "* [Hsl Hcap]".
  wp_apply (marshal.wp_WriteInt with "[$Hsl $Hcap]") as "* [Hsl Hcap]".
  iApply ("HΦ" $! (Some _)).
  iFrame "∗#".
  iSplit. { by iExists _. }
  iSplit; [done|].
  iFrame (Hcode).
  iExists sibs, None.
  iFrame "%".

  iExists [], [], []. repeat iSplit; [|done..].
  rewrite /Proof.wish /Proof.encodes /=.
  iExists _. repeat iSplit; try done.
  2: { by list_simplifier. }
  erewrite join_same_len_length.
  2: { by apply Forall_reverse. }
  rewrite length_reverse.
  word.
Qed.

(** Map predicates. *)

(* [own_Map] with [hash] allows for same hash across Map ops: Hash, Prove, Put.
an alternate (stronger but more work) approach is define pred that
determ maps Map to tree (via adding tree constraints like minimality)
and determ maps tree to hash. *)
Definition own_Map ptr m hash d : iProp Σ :=
  ∃ ptr_root t,
  "Hstruct" ∷ ptr ↦{d} (merkle.Map.mk ptr_root) ∗
  "Hown_tree" ∷ own_tree ptr_root t d ∗
  "%Heq_map" ∷ ⌜m = to_map t⌝ ∗
  "#His_hash" ∷ is_cut_tree t hash ∗

  "%His_cutless" ∷ ⌜is_cutless t⌝ ∗
  "%His_limit" ∷ ⌜is_limit t⌝ ∗
  "%His_const_label" ∷ ⌜is_const_label_len t⌝ ∗
  "%His_sorted" ∷ ⌜is_sorted t⌝.

Lemma own_Map_to_is_map ptr m hash d :
  own_Map ptr m hash d -∗
  is_map m hash.
Proof.
  iNamed 1.
  iFrame (Heq_map).
  by iDestruct (cut_to_full with "His_hash") as "$".
Qed.

Lemma own_Map_init ptr d0 :
  ("#Hpkg" ∷ is_pkg_init merkle ∗
  "Hstruct" ∷ ptr ↦{d0} (merkle.Map.mk null)) -∗
  ∃ hash, "Hown_Map" ∷ own_Map ptr ∅ hash d0.
Proof.
  iIntros "@".
  iDestruct (is_pkg_init_access with "[$]") as "/= #Hinit".
  rewrite /is_initialized. iNamed "Hinit".
  iExists _, null, Empty.
  iFrame "∗#".
  by repeat iSplit.
Qed.

#[global] Instance own_Map_dfrac ptr m h :
  DFractional (λ dq, own_Map ptr m h dq).
Proof.
  split.
  - intros ??. iSplit.
    + iNamed 1.
      iDestruct "Hstruct" as "[? ?]".
      iDestruct "Hown_tree" as "[? ?]".
      by iFrame "∗#".
    + iIntros "[H0 H1]".
      iNamedSuffix "H0" "0". iNamedSuffix "H1" "1".
      iCombine "Hstruct0 Hstruct1" as "?" gives %[_ ?].
      simplify_eq/=.
      iCombine "Hown_tree0 Hown_tree1" as "?" gives %->.
      by iFrame "∗#".
  - apply _.
  - iIntros "* @".
    iPersist "Hstruct Hown_tree".
    by iFrame "#".
Qed.

#[global] Instance own_Map_as_dfrac ptr m h dq :
  AsDFractional (own_Map ptr m h dq) (λ dq, own_Map ptr m h dq) dq.
Proof. auto. Qed.

#[global] Instance own_Map_combine_sep_gives ptr m0 m1 h0 h1 d0 d1 :
  CombineSepGives (own_Map ptr m0 h0 d0) (own_Map ptr m1 h1 d1)
    ⌜m0 = m1 ∧ h0 = h1⌝.
Proof.
  rewrite /CombineSepGives. iIntros "[H0 H1]".
  iNamedSuffix "H0" "0". iNamedSuffix "H1" "1".
  iCombine "Hstruct0 Hstruct1" gives %[_ ?].
  simplify_eq/=.
  iCombine "Hown_tree0 Hown_tree1" gives %->.
  iDestruct (is_cut_tree_det with "His_hash0 His_hash1") as %->.
  by iModIntro.
Qed.

#[global] Instance own_Map_combine_sep_as ptr m0 m1 h0 h1 d0 d1 :
  CombineSepAs (own_Map ptr m0 h0 d0) (own_Map ptr m1 h1 d1)
    (own_Map ptr m0 h0 (d0 ⋅ d1)) | 60.
Proof.
  rewrite /CombineSepAs.
  iIntros "[H0 H1]".
  iCombine "H0 H1" gives %?.
  destruct_and?. simplify_eq/=.
  iCombine "H0 H1" as "$".
Qed.

(** Map program proofs. *)

Lemma wp_Map_Hash ptr m hash d0 :
  {{{
    is_pkg_init merkle ∗
    "Hown_Map" ∷ own_Map ptr m hash d0
  }}}
  ptr @ (ptrT.id merkle.Map.id) @ "Hash" #()
  {{{
    sl_hash, RET #sl_hash;
    "Hown_Map" ∷ own_Map ptr m hash d0 ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash
  }}}.
Proof.
  wp_start as "@". wp_auto.
  iNamed "Hown_Map".
  wp_auto.
  iRename "His_hash" into "His_hash'".
  wp_apply (wp_node_getHash with "[$Hown_tree]") as "* @".
  iDestruct (is_cut_tree_det with "His_hash His_hash'") as %->.
  iApply "HΦ".
  iFrame "∗#%".
Qed.

Lemma wp_Map_Prove ptr m hash d0 sl_label d1 label :
  {{{
    is_pkg_init merkle ∗
    "Hown_Map" ∷ own_Map ptr m hash d0 ∗
    "Hsl_label" ∷ sl_label ↦*{d1} label ∗
    "%Hlen_label" ∷ ⌜Z.of_nat $ length label = cryptoffi.hash_len⌝
  }}}
  ptr @ (ptrT.id merkle.Map.id) @ "Prove" #sl_label
  {{{
    inMap sl_val val sl_entryProof entryProof, RET (#inMap, #sl_val, #sl_entryProof);
    "Hown_Map" ∷ own_Map ptr m hash d0 ∗
    "Hsl_label" ∷ sl_label ↦*{d1} label ∗

    "#Hsl_val" ∷ sl_val ↦*□ val ∗
    "Hsl_entryProof" ∷ sl_entryProof ↦* entryProof ∗

    "%Hlook" ∷
      ⌜match m !! label with
      | None => inMap = false
      | Some v => inMap = true ∧ val = v
      end⌝ ∗
    "#Hproof" ∷
      match m !! label with
      | None => wish_NonMemb label entryProof hash
      | Some v => wish_Memb label v entryProof hash
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  iNamed "Hown_Map".
  iDestruct (own_slice_len with "Hsl_label") as %[? _].
  wp_apply std.wp_Assert.
  { case_bool_decide; try done. word. }
  wp_apply (wp_node_prove with "[$Hown_tree $Hsl_label]") as "* @".
  { iFrame "#%". iPureIntro. by eapply is_cutless_to_path. }
  iNamedSuffix "Hproof" "'".
  iDestruct (is_cut_tree_det with "His_hash His_hash'") as %<-.
  apply entry_eq_lookup in His_entry.
  subst.
  iApply "HΦ".
  by iFrame "∗#%".
Qed.

Lemma wp_Map_Put ptr m hash sl_label label sl_val val :
  {{{
    is_pkg_init merkle ∗
    "Hown_Map" ∷ own_Map ptr m hash 1 ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_val" ∷ sl_val ↦*□ val ∗
    "%Hmono" ∷ ⌜m !! label = None⌝ ∗
    "%Hlen_label" ∷ ⌜Z.of_nat $ length label = cryptoffi.hash_len⌝
  }}}
  ptr @ (ptrT.id merkle.Map.id) @ "Put" #sl_label #sl_val
  {{{
    sl_updProof updProof hash', RET #sl_updProof;
    "Hown_Map" ∷ own_Map ptr (<[label:=val]>m) hash' 1 ∗
    "Hsl_updProof" ∷ sl_updProof ↦* updProof ∗
    "#His_proof" ∷ wish_Update label val updProof hash hash'
  }}}.
Proof.
  wp_start as "@". wp_auto.
  iNamed "Hown_Map".
  iDestruct (own_slice_len with "Hsl_label") as %[? _].
  wp_apply std.wp_Assert.
  { case_bool_decide; try done. word. }
  iRename "Hsl_val" into "Hsl_val_in".
  wp_apply (wp_node_prove with "[$Hown_tree $Hsl_label]") as "{Hsl_label} * @".
  { iFrame "#%". iPureIntro. by eapply is_cutless_to_path. }
  iNamedSuffix "Hproof" "'".
  iDestruct (is_cut_tree_det with "His_hash His_hash'") as %<-.
  apply entry_eq_lookup in His_entry. subst.
  rewrite Hmono in Hoval |-*. subst.
  iNamedSuffix "His_proof'" "_wish".
  wp_apply std.wp_Assert; [done|].
  iDestruct (struct_fields_split with "Hstruct") as "H".
  iNamed "H". simpl.
  wp_apply (wp_put with "[$Hown_tree $Hsl_label $Hroot]") as "* @"; try done.
  destruct err.
  { iExFalso. iApply "Hgenie". iPureIntro. by eapply is_cutless_to_path. }
  wp_apply std.wp_Assert; [done|].
  iNamed "Hgenie".
  iDestruct (struct_fields_combine (v:=merkle.Map.mk _) with "[$Hn0]") as "Hstruct".
  iDestruct (own_tree_to_hash with "Hown_tree") as "[% #His_hash_new]".
  iApply "HΦ".

  instantiate (1:=hash0).
  instantiate (1:=proof).
  rewrite /wish_Update.
  iFrame. iSplit.
  - iFrame "#". iPureIntro. repeat split.
    + symmetry. by eapply to_map_over_put.
    + by eapply cutless_over_put.
    + by eapply is_limit_over_put.
    + eapply const_label_len_over_put; try done. word.
    + by eapply is_sorted_over_put.
  - iFrame "Hwish_toTree_wish".
    iDestruct (proofToTree_post with "[$]") as "#@".
    opose proof (put_Some _ _ val _ _ _ _ _) as [? ?]; try done.
    iDestruct (cut_cut_hash_over_put t t0 with "[$][//][//][$]") as "#?".
    iFrame "#%".
Qed.

(* NOTE: i don't know why these instances are so brittle.
even re-ordering VerifyNonMemb before VerifyMemb causes TC search to spin.
i prove these instances at the end to remove internal brittleness.
i export the defs as Opaque to remove external brittleness. *)
#[global] Instance wish_Memb_pers l v p h :
  Persistent (wish_Memb l v p h).
Proof. apply _. Qed.

#[global] Instance wish_Update_pers l v p hO hN :
  Persistent (wish_Update l v p hO hN).
Proof. apply _. Qed.

#[global] Instance wish_NonMemb_pers l p h :
  Persistent (wish_NonMemb l p h).
Proof. apply _. Qed.

End proof.
End merkle.
