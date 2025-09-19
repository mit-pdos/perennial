From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import merkle.
From Perennial.Helpers Require Import bytes NamedProps.
From Stdlib.micromega Require Import ZifyNat.

From New.proof Require Import bytes.
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
  "%His_limit" ∷ ⌜ is_limit t ⌝.

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
  by iDestruct (cut_to_full with "His_tree") as "$".
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
Admitted. (*
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
*)

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

Lemma bool_decide_ite_not (P : Prop) {dec : Decision P} :
  (if bool_decide P then false else true) = bool_decide (¬P).
Proof. by rewrite bool_decide_not. Qed.

Lemma wp_getBit sl_bs d0 bs (n : w64) :
  {{{
    is_pkg_init merkle ∗
    "Hsl_bs" ∷ sl_bs ↦*{d0} bs
  }}}
  @! merkle.getBit #sl_bs #n
  {{{
    bit, RET #bit;
    "Hsl_bs" ∷ sl_bs ↦*{d0} bs ∗
    "->" ∷ ⌜ bit = get_bit bs (uint.nat n) ⌝
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
  wp_auto.
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
  rewrite bool_decide_ite_not.
  replace (Z.of_nat (uint.nat n `mod` 8)%nat) with (uint.Z n `mod` 8) in Ho.
  2: { rewrite Nat2Z.inj_mod. word. }
  simplify_eq/=. clear.
  assert (∀ x y, x = y → bool_decide (x ≠ W8 0) = bool_decide (y ≠ W8 0))
    as Ht by naive_solver.
  f_equal. apply Ht. repeat f_equal. word.
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
    "#Hinit" ∷ is_initialized ∗
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
    rewrite /is_initialized. iNamed "Hinit".
    wp_apply wp_globals_get.
    iApply "HΦ". iFrame "∗#". }
  destruct t; iNamed "Hown_tree"; try done; iNamed "Hown_tree";
    wp_auto; iApply "HΦ"; iFrame "∗#".
Qed.

Notation pref_ext p l := (p ++ [get_bit l (length p)]) (only parsing).

(* condition [P] and [Q] on [φ]. [P] and [Q] should be filled in by [iAccu]. *)
Lemma condition_prop {P Q : iProp Σ} {φ : Prop} (dec : Decision φ) :
  P -∗
  Q -∗
  (if dec then P else Q) ∗ (if dec then Q else P).
Proof. iIntros "**". case_match; iFrame. Qed.

Lemma condition_bool {P Q : iProp Σ} (b : bool) :
  P -∗
  Q -∗
  (if b then P else Q) ∗ (if b then Q else P).
Proof. iIntros "**". case_match; iFrame. Qed.

Lemma wp_getProofCap (depth : nat) :
  {{{
    is_pkg_init merkle ∗
    "%Heq_depth" ∷ ⌜depth≤max_depth⌝
  }}}
  @! merkle.getProofCap #(W64 depth)
  {{{
    (cap : w64), RET #cap;
    "%Heq_cap" ∷ ⌜8 ≤ sint.Z cap⌝
  }}}.
Proof. rewrite /max_depth. wp_start as "@". wp_auto. iApply "HΦ". word. Qed.

Lemma wp_put n0 n t sl_label sl_val label val :
  (* for max depth. *)
  is_limit t →
  Z.of_nat (length label) = cryptoffi.hash_len →
  is_const_label_len t →
  is_sorted t →
  {{{
    is_pkg_init merkle ∗
    "#Hinit" ∷ is_initialized ∗
    "Hn0_in" ∷ n0 ↦ n ∗
    "Hown_tree" ∷ own_tree n t 1 ∗
    "#Hsl_label_in" ∷ sl_label ↦*□ label ∗
    "#Hsl_val_in" ∷ sl_val ↦*□ val
  }}}
  @! merkle.put #n0 #(W64 0) #sl_label #sl_val
  {{{
    n' err, RET #err;
    "Hn0" ∷ n0 ↦ n' ∗
    "Herr" ∷ match err with
      | true =>
        "%Hvalid" ∷ ¬ ⌜is_cutless_path t label⌝
      | false =>
        ∃ t',
        "%HSome_tree" ∷ ⌜ pure_put t label val = Some t' ⌝ ∗
        "Hown_tree" ∷ own_tree n' t' 1
      end
  }}}.
Proof.
Admitted. (*
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
    wp_auto.
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
      iClear "IH". wp_auto.
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
    wp_auto. wp_apply wp_alloc as "* Hnode".
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
      - rewrite /is_initialized. iNamed "Hinit".
        by iFrame "#". }
    destruct err; iNamed "Herr".
    { exfalso. apply Hvalid. by case_match. }
    wp_apply std.wp_Assert; [done|].
    rewrite HSome_tree.
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
      - rewrite /is_initialized. iNamed "Hinit".
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
      - rewrite /is_initialized. iNamed "Hinit".
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
    destruct err; iNamed "Herr"; wp_auto.
    { iApply "HΦ".  by iFrame. }
    rewrite HSome_tree.
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
*)

Lemma wp_newShell sl_label label sl_sibs sibs_enc (depth depth_rem : nat) :
  {{{
    is_pkg_init merkle ∗
    "#Hinit" ∷ is_initialized ∗
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
Admitted. (*
  iLöb as "IH" forall (sl_sibs sibs_enc depth depth_rem).
  wp_start as "@". wp_auto.
  iDestruct (own_slice_len with "Hsl_sibs") as %[].

  wp_if_destruct; wp_auto.
  { iApply "HΦ".
    destruct sibs_enc. 2: { simpl in *. word. }
    instantiate (1:=[]).
    repeat iSplit; try done.
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
    rewrite length_drop. lia. }
  iIntros "*". iNamedSuffix 1 "0". wp_auto.
  wp_apply (wp_node_getHash
    (if get_bit label depth then _ else Cut _)
    with "[Htree_r]").
  { iFrame "#". case_match; [iFrame|].
    iFrame "∗#".
    iPureIntro. intuition.
    rewrite length_drop. lia. }
  iIntros "*". iNamedSuffix 1 "1". wp_auto.

  wp_apply wp_compInnerHash. { iFrame "#". }
  iIntros "*". iNamedSuffix 1 "_inner".
  iPersist "Hsl_hash_inner". wp_auto.
  iApply "HΦ".
  instantiate (1:=drop (depth_rem * 32) sibs_enc :: sibs).
  repeat iSplit; try iPureIntro.
  - rewrite reverse_cons join_app join_singleton -Henc_sibs take_drop //.
  - apply Forall_cons; [|done]. rewrite length_drop. lia.
  - iFrame "∗#".
Qed.
*)

Definition wish_proofToTree label proof_enc sibs oleaf : iProp Σ :=
  ∃ LeafLabel LeafVal tail,
  let IsOtherLeaf := match oleaf with None => false | _ => true end in
  let proof := MerkleProof.mk' (mjoin (reverse sibs)) IsOtherLeaf LeafLabel LeafVal in
  "%Hlen_label" ∷ ⌜length label = Z.to_nat (cryptoffi.hash_len)⌝ ∗
  "Henc_proof" ∷ MerkleProof.wish proof_enc proof tail ∗
  "%Hlen_sibs" ∷ ⌜Forall (λ x, length x = Z.to_nat $ cryptoffi.hash_len) sibs⌝ ∗
  "%Heq_depth" ∷ ⌜length sibs ≤ max_depth⌝ ∗
  "Holeaf" ∷ match oleaf with None => True | Some (l, v) =>
    "%Hlen_olabel" ∷ ⌜length l = Z.to_nat $ cryptoffi.hash_len⌝ ∗
    "%Heq_olabel" ∷ ⌜label ≠ l⌝ ∗
    "%Hcutless" ∷ ⌜is_cutless_path (pure_newShell label sibs) l⌝ ∗
    "->" ∷ ⌜LeafLabel = l⌝ ∗
    "->" ∷ ⌜LeafVal = v⌝
    end.

Lemma wish_proofToTree_det l p s0 s1 o0 o1 :
  wish_proofToTree l p s0 o0 -∗
  wish_proofToTree l p s1 o1 -∗
  ⌜s0 = s1 ∧ o0 = o1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (MerkleProof.wish_det with "Henc_proof0 Henc_proof1") as %[[=] ->].
  opose proof (join_same_len_inj _ (reverse _) (reverse _) _ _ _ _)
    as Heq_s; try done.
  2: { by apply Forall_reverse. }
  2: { by apply Forall_reverse. }
  { lia. }
  apply (inj _) in Heq_s.
  destruct o0 as [[]|]; [|by case_match].
  iNamedSuffix "Holeaf0" "0".
  destruct o1 as [[]|]; [|done].
  iNamedSuffix "Holeaf1" "1".
  by subst.
Qed.

Tactic Notation "intro_wish" := iIntros "(%&%&@)".

Lemma wp_proofToTree sl_label label sl_proof proof :
  {{{
    is_pkg_init merkle ∗
    "#Hinit" ∷ is_initialized ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_proof" ∷ sl_proof ↦*□ proof
  }}}
  @! merkle.proofToTree #sl_label #sl_proof
  {{{
    tr err, RET (#tr, #err);
    "Hgenie" ∷ match err with
      | true => ¬ ∃ sibs oleaf, wish_proofToTree label proof sibs oleaf
      | false =>
        ∃ sibs oleaf t,
        "Hwish" ∷ wish_proofToTree label proof sibs oleaf ∗
        "%HSome_tree" ∷ ⌜pure_proofToTree label sibs oleaf = Some t⌝ ∗
        "%Hlabel_None" ∷ ⌜is_entry t label None⌝ ∗
        "Hown_tree" ∷ own_tree tr t 1
      end
  }}}.
Proof.
Admitted. (*
  wp_start as "@". wp_auto.
  iDestruct (own_slice_len with "Hsl_label") as %[].
  wp_if_destruct; wp_auto.
  2: { iApply "HΦ". intro_wish. word. }
  wp_apply (MerkleProof.wp_dec with "[$Hsl_proof]") as "* Hpost".
  destruct err; wp_auto.
  { iApply "HΦ". intro_wish. iApply "Hpost". iFrame. }
  iNamedSuffix "Hpost" "_dec".
  iNamed "Hown_obj_dec".
  iDestruct (own_slice_len with "Hsl_Siblings") as %[Hlen_sl_sibs ?].
  wp_auto.
  wp_if_destruct; wp_auto.
  2: { iApply "HΦ". intro_wish.
    iDestruct (MerkleProof.wish_det with "Hwish_dec Henc_proof") as %[-> ->].
    iClear "Hwish_dec". simpl in *.
    apply join_same_len_length in Hlen_sibs.
    rewrite -join_length_reverse in Hlen_sibs.
    word. }
  wp_if_destruct; wp_auto.
  { iApply "HΦ". intro_wish.
    iDestruct (MerkleProof.wish_det with "Hwish_dec Henc_proof") as %[-> ->].
    iClear "Hwish_dec". simpl in *.
    apply join_same_len_length in Hlen_sibs.
    rewrite -join_length_reverse in Hlen_sibs.
    word. }

  replace (W64 0) with (W64 0%nat) by word.
  iDestruct "Hsl_Siblings" as "#Hsl_Siblings".
  wp_apply wp_newShell as "* @".
  { iFrame "#".
    instantiate (1:=(length obj.(MerkleProof.Siblings) `div` 32)%nat).
    (* [Require ZifyNat] for [Nat.div] reasoning. *)
    word. }
  destruct obj. simplify_eq/=.
  rewrite join_length_reverse in Hlen_sl_sibs.
  apply join_same_len_length in Hlen_sibs as ?.
  destruct IsOtherLeaf; wp_auto.
  2: { iApply "HΦ".
    iExists _, None. iFrame.
    iPureIntro; repeat split; try done; word. }
  replace (pure_newShell' _ _ _) with (pure_newShell label sibs) by done.

  iDestruct (own_slice_len with "Hsl_LeafLabel") as %[].
  wp_if_destruct; wp_auto.
  2: { iApply "HΦ". intro_wish.
    destruct oleaf as [[]|].
    2: { iDestruct (MerkleProof.wish_det with "Hwish_dec Henc_proof") as %[[=] _]. }
    iDestruct (MerkleProof.wish_det with "Hwish_dec Henc_proof") as %[[=] ->].
    iNamed "Holeaf". simplify_eq/=. word. }

  iPersist "Hsl_LeafLabel Hsl_LeafVal".
  wp_apply bytes.wp_Equal as "_".
  { iFrame "#". }
  wp_if_destruct; wp_auto.
  { iApply "HΦ". intro_wish.
    destruct oleaf as [[]|].
    2: { iDestruct (MerkleProof.wish_det with "Hwish_dec Henc_proof") as %[[=] _]. }
    iDestruct (MerkleProof.wish_det with "Hwish_dec Henc_proof") as %[[=] ->].
    by iNamed "Holeaf". }

  wp_apply (wp_put with "[$tr $Hown_tree]") as "* @".
  5: { iFrame "#". }
  { apply limit_on_newShell. word. }
  { word. }
  { apply const_label_on_newShell. }
  { apply sorted_on_newShell. }
  destruct err; iNamed "Herr"; wp_auto.
  { iApply "HΦ". intro_wish.
    destruct oleaf as [[]|].
    2: { iDestruct (MerkleProof.wish_det with "Hwish_dec Henc_proof") as %[[=] _]. }
    iDestruct (MerkleProof.wish_det with "Hwish_dec Henc_proof") as %[[=] ->].
    iNamed "Holeaf". simplify_eq/=.
    opose proof (join_same_len_inj _ (reverse _) (reverse _) _ _ _ _)
      as Heq_s; try done.
    2: { by apply Forall_reverse. }
    2: { by apply Forall_reverse. }
    { lia. }
    apply (inj _) in Heq_s.
    by subst. }

  iApply "HΦ".
  iExists _, (Some (_, _)).
  iFrame.
  iPureIntro. repeat split; try done; [word..|].
  by eapply cutless_on_put.
Qed.
*)

(* make def to prevent unfolding the nat. *)
Definition w64_len := 8%nat.
Hint Unfold w64_len : len.

Lemma wp_node_find n t d0 sl_label d1 label (getProof : bool) :
  (* limit needed to prevent depth overflow. *)
  is_limit t →
  is_cutless_path t label →
  {{{
    is_pkg_init merkle ∗
    "#Hinit" ∷ is_initialized ∗
    "Hown_tree" ∷ own_tree n t d0 ∗
    "Hsl_label_in" ∷ sl_label ↦*{d1} label
  }}}
  n @ (ptrT.id merkle.node.id) @ "find" #(W64 0) #sl_label #getProof
  {{{
    (found : bool) sl_foundLabel foundLabel sl_foundVal foundVal sl_sibs sibs_enc,
    RET (#found, #sl_foundLabel, #sl_foundVal, #sl_sibs);
    "Hown_tree" ∷ own_tree n t d0 ∗
    "Hsl_label" ∷ sl_label ↦*{d1} label ∗

    "#Hsl_foundLabel" ∷ sl_foundLabel ↦*□ foundLabel ∗
    "#Hsl_foundVal" ∷ sl_foundVal ↦*□ foundVal ∗
    "Hsl_sibs" ∷ sl_sibs ↦* sibs_enc ∗
    "Hcap_sibs" ∷ own_slice_cap w8 sl_sibs 1 ∗

    "%Heq_found" ∷ ⌜ find t label = if found then Some (foundLabel, foundVal) else None ⌝ ∗
    "Hproof" ∷ (if negb getProof then True else
      ∃ sibsLen sibs,
      "#His_sibs" ∷ is_sibs t label sibs ∗
      "%Henc_sibs" ∷ ⌜sibs_enc = sibsLen ++ mjoin (reverse sibs)⌝ ∗
      "%Hlen_sibsLen" ∷ ⌜length sibsLen = w64_len⌝)
  }}}.
Proof.
Admitted. (*
  autounfold with merkle.
  intros Hlimit Hcutless.
  remember max_depth as limit.
  remember 0%nat as depth.
  replace (W64 0) with (W64 depth) by word.
  assert (depth + limit = max_depth) as Heq_depth; [word|].
  clear Heqlimit Heqdepth.
  iLöb as "IH" forall (t limit depth n Hcutless Hlimit Heq_depth).
  iIntros (Φ) "(#?&@) HΦ".
  wp_method_call. wp_call. wp_auto.
  wp_if_destruct.

  { iClear "IH".
    iDestruct (own_empty_tree with "Hown_tree") as %->.
    wp_auto.
    (* TODO(goose): wp_if_destruct could destruct bool's. *)
    destruct getProof; wp_auto.
    + wp_apply wp_getProofCap as "* %"; [word|].
      wp_apply wp_slice_make3 as "* (Hsl_sibs&Hcap_sibs&_)"; [word|].
      iApply "HΦ". iFrame.
      iDestruct own_slice_nil as "$".
      repeat (iSplit || iExists _); try done;
        [by list_simplifier | len].
    + iApply "HΦ". iFrame.
      iDestruct own_slice_nil as "$".
      iDestruct own_slice_nil as "$".
      by iDestruct own_slice_cap_nil as "$". }

  destruct t; simpl in *; iNamed "Hown_tree"; try done;
    iNamed "Hown_tree"; wp_auto.

  - iClear "IH".
    destruct getProof; wp_auto.
    + wp_apply wp_getProofCap as "* %"; [word|].
      wp_apply wp_slice_make3 as "* (Hsl_sibs&Hcap_sibs&_)"; [word|].
      iApply "HΦ". iFrame "∗#".
      repeat (iSplit || iExists _); try done;
        [by list_simplifier | len].
    + iApply "HΦ". iFrame "∗#".
      iDestruct own_slice_nil as "$".
      by iDestruct own_slice_cap_nil as "$".

  - destruct limit; [done|]. intuition.
    wp_apply (wp_node_getChild with "[$Hnode $Hsl_label_in]") as "*".
    iIntros "[Hsl_label_in H]". iNamed "H". wp_auto.
    replace (uint.nat (W64 depth)) with depth by word.
    iDestruct (condition_bool (get_bit label depth)
      with "[Hown_child1] [Hown_child0]")
      as "[Hown_child_l Hown_child_r]"; [iAccu..|].
    replace (word.add _ _) with (W64 (S depth)) by word.
    wp_apply ("IH" with "[//] [] [] [Hown_child_l Hsl_label_in]") as "* @".
    { by case_match. }
    { word. }
    { iFrame "∗#". case_match; iFrame. }
    iClear "IH".
    assert (∀ (b : bool) T (x0 x1 : T),
      (if b then if b then x0 else x1 else if b then x1 else x0) = x0) as Hif.
    { intros. by repeat case_match. }

    destruct getProof; wp_auto; simpl in *; iNamed "Hproof".
    + iDestruct ("Hclose" with "Hcb Hcnb") as "@".
      rewrite !{}Hif.
      wp_apply (wp_node_getHash (if get_bit label depth then _ else _)
        with "[Hown_child_r]") as "* H".
      { iFrame "#". case_match; iFrame. }
      iNamedSuffix "H" "0".
      wp_apply (wp_slice_append with "[$Hsl_sibs $Hcap_sibs]")
        as "* (Hsl_sibs & Hcap_sibs & _)".
      { iFrame "#". }
      iApply "HΦ". iFrame "∗#".
      iSplitL. { case_match; iFrame. }
      repeat (iSplit || iExists _); try done.
      iPureIntro. list_simplifier. f_equal.
      rewrite reverse_cons join_app.
      by list_simplifier.
    + iDestruct ("Hclose" with "Hcb Hcnb") as "@".
      rewrite !{}Hif.
      iApply "HΦ". iFrame "∗#".
      iSplit; [|done].
      case_match; iFrame.
Qed.
*)

Definition valid_proof label proof hash m : iProp Σ :=
  ∃ sibs oleaf t,
  "Hvalid_toTree" ∷ wish_proofToTree label proof sibs oleaf ∗
  "%HSome_toTree" ∷ ⌜pure_proofToTree label sibs oleaf = Some t⌝ ∗
  "#His_hash" ∷ is_cut_tree t hash ∗
  "#His_map" ∷ is_map m hash.

Lemma valid_proof_det l p h0 h1 m0 m1 :
  valid_proof l p h0 m0 -∗ valid_proof l p h1 m1 -∗ ⌜h0 = h1 ∧ m0 = m1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (wish_proofToTree_det with "Hvalid_toTree0 Hvalid_toTree1") as %[].
  simplify_eq/=.
  iDestruct (is_cut_tree_det with "His_hash0 His_hash1") as %->.
  by iDestruct (is_map_inj with "His_map0 His_map1") as %->.
Qed.

Lemma wp_VerifyNonMemb sl_label label sl_proof proof :
  {{{
    is_pkg_init merkle ∗
    "#Hinit" ∷ is_initialized ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_proof" ∷ sl_proof ↦*□ proof
  }}}
  @! merkle.VerifyNonMemb #sl_label #sl_proof
  {{{
    sl_hash hash err, RET (#sl_hash, #err);
    "#Hsl_hash" ∷ sl_hash ↦*□ hash ∗
    "Hgenie" ∷ match err with
      | true => ¬ ∃ hash m, valid_proof label proof hash m
      | false =>
        ∃ m,
        "#His_proof" ∷ valid_proof label proof hash m ∗
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
  wp_apply (wp_node_getHash with "[$Hown_tree]") as "* @".
  { iFrame "#". }
  iApply "HΦ".
  iDestruct (is_cut_tree_len with "His_hash") as %?.
  iDestruct (is_map_invert hash) as "[% #His_map]"; [done|].
  iFrame "∗#%".

  iNamed "His_map".
  iDestruct (full_entry_txfer with "[$]") as %?; [done|..].
  (* TODO: shift these props to proofToTree WP.
  (1) they rely on valid rsrc and (2) are short that it's reasonable to do
  them in-line with WP. *)
  { opose proof (cutless_on_newShell label sibs).
    destruct oleaf as [[]|]; simpl in *.
    - by eapply cutless_over_put.
    - by simplify_eq/=. }
  { admit. }
  subst. iPureIntro.
  apply entry_eq_lookup.
Abort.

End proof.
