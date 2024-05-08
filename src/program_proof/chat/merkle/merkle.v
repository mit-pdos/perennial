From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat Require Import merkle.

From Perennial.program_proof.chat.merkle Require Import shim.
From Perennial.program_proof Require Import std_proof.

Section defs.
Context `{!heapGS Σ}.

Inductive tree : Type :=
  (* Cut only exists for proof checking trees. *)
  | Cut : list u8 → tree
  | Empty : tree
  | Leaf : list u8 → tree
  | Interior : list tree → tree.

Fixpoint containsNodeAtEnd (tr : tree) (id : list u8) (node : tree) : Prop :=
  match tr with
  | Cut _ => False
  | Empty => id = [] ∧ tr = node
  | Leaf val => id = [] ∧ tr = node
  | Interior children =>
    match id with
    | [] => False
    | pos :: rest =>
      ∃ child, children !! int.nat pos = Some child ∧ containsNodeAtEnd child rest node
    end
  end.

Fixpoint is_tree_hash (tr : tree) (hash : list u8) : iProp Σ :=
  match tr with
  | Cut hash' => ⌜hash = hash' ∧ length hash' = 32%nat⌝
  | Empty => is_hash [U8 0] hash
  | Leaf val => is_hash (val ++ [U8 1]) hash
  | Interior children =>
    ∃ (child_hashes : list (list u8)),
    let map_fn := (λ c h, is_tree_hash c h) in
    ([∗ list] child_fn;hash' ∈ (map_fn <$> children);child_hashes,
      child_fn hash') ∗
    is_hash (concat child_hashes ++ [U8 2]) hash
  end%I.

Lemma tree_hash_len tr hash :
  is_tree_hash tr hash -∗ ⌜length hash = 32%nat⌝.
Proof.
  iIntros "Htree".
  destruct tr.
  { iDestruct "Htree" as "[%Heq %Hlen]". naive_solver. }
  1-2: iDestruct (hash_len with "Htree") as "%Hlen"; naive_solver.
  {
    iDestruct "Htree" as (ch) "[_ Htree]".
    by iDestruct (hash_len with "Htree") as "%Hlen".
  }
Qed.

(* At a specific path down a tree rooted at digest, we will find this val. *)
Definition is_path_val id val digest : iProp Σ :=
  ∃ tr,
  is_tree_hash tr digest ∧
  ⌜containsNodeAtEnd tr id
    match val with
    | None => Empty
    | Some val' => Leaf val'
    end⌝.

Lemma concat_eq_dim1_eq {A : Type} sz (l1 l2 : list (list A)) :
  concat l1 = concat l2 →
  (Forall (λ l, length l = sz) l1) →
  (Forall (λ l, length l = sz) l2) →
  0 < sz →
  l1 = l2.
Proof.
  intros Heq_concat Hlen_l1 Hlen_l2 Hsz.
  apply (f_equal length) in Heq_concat as Heq_concat_len.
  do 2 rewrite concat_length in Heq_concat_len.
  generalize dependent l2.
  induction l1 as [|a1]; destruct l2 as [|a2]; simpl;
    intros Heq_concat Hlen_l2 Heq_concat_len;
    decompose_Forall; eauto with lia.
  apply (f_equal (take (length a1))) in Heq_concat as Htake_concat.
  apply (f_equal (drop (length a1))) in Heq_concat as Hdrop_concat.
  rewrite <-H in Htake_concat at 2.
  rewrite <-H in Hdrop_concat at 2.
  do 2 rewrite take_app_length in Htake_concat.
  do 2 rewrite drop_app_length in Hdrop_concat.
  rewrite Htake_concat.
  apply (app_inv_head_iff [a2]).
  apply IHl1; eauto with lia.
Qed.

Lemma sep_tree_hash_impl_forall_len ct ch :
  ([∗ list] t;h ∈ ct;ch, is_tree_hash t h) -∗
  ⌜Forall (λ l, length l = 32%nat) ch⌝.
Proof.
  iIntros "Htree".
  iDestruct (big_sepL2_impl _ (λ _ _ h, ⌜length h = 32%nat⌝%I) with "Htree []") as "Hlen_sepL2".
  {
    iIntros "!>" (???) "_ _ Hhash".
    by iDestruct (tree_hash_len with "Hhash") as "Hlen".
  }
  iDestruct (big_sepL2_const_sepL_r with "Hlen_sepL2") as "[_ %Hlen_sepL1]".
  iPureIntro.
  by apply Forall_lookup.
Qed.

Lemma is_path_val_inj' pos rest val1 val2 digest :
  is_path_val (pos :: rest) val1 digest -∗
  is_path_val (pos :: rest) val2 digest -∗
  ∃ digest',
  is_path_val rest val1 digest' ∗
  is_path_val rest val2 digest'.
Proof.
  iIntros "Hval1 Hval2".
  rewrite /is_path_val.
  iDestruct "Hval1" as (tr1) "[Htree1 %Hcont1]".
  iDestruct "Hval2" as (tr2) "[Htree2 %Hcont2]".
  destruct tr1 as [| | |ct1], tr2 as [| | |ct2]; try naive_solver.

  (* Get contains pred and is_tree_hash for children. *)
  destruct Hcont1 as [child1 [Hlist1 Hcont1]].
  destruct Hcont2 as [child2 [Hlist2 Hcont2]].
  iDestruct "Htree1" as (ch1) "[Htree1 Hdig1]".
  iDestruct "Htree2" as (ch2) "[Htree2 Hdig2]".
  iDestruct (big_sepL2_fmap_l (λ c h, is_tree_hash c h) with "Htree1") as "Htree1".
  iDestruct (big_sepL2_fmap_l (λ c h, is_tree_hash c h) with "Htree2") as "Htree2".

  (* Use is_hash ch1/ch2 digest to prove that child hashes are same. *)
  iDestruct (sep_tree_hash_impl_forall_len with "Htree1") as "%Hlen_ch1".
  iDestruct (sep_tree_hash_impl_forall_len with "Htree2") as "%Hlen_ch2".

  iDestruct (hash_inj with "Hdig1 Hdig2") as "%Heq".
  apply app_inv_tail in Heq.
  assert (ch1 = ch2) as Hch.
  { apply (concat_eq_dim1_eq 32); eauto with lia. }
  subst ch1.

  (* Finish up. *)
  iDestruct (big_sepL2_lookup_1_some with "Htree1") as (h1) "%Hlook1"; [done|].
  iDestruct (big_sepL2_lookup_1_some with "Htree2") as (h2) "%Hlook2"; [done|].
  iDestruct (big_sepL2_lookup with "Htree1") as "Hhash1"; [done..|].
  iDestruct (big_sepL2_lookup with "Htree2") as "Hhash2"; [done..|].
  clear Hlook1 Hlook2.

  iFrame "%∗".
Qed.

Lemma empty_leaf_hash_disjoint digest v :
  is_tree_hash Empty digest -∗
  is_tree_hash (Leaf v) digest -∗
  False.
Proof.
  iIntros "Hempty Hleaf".
  iDestruct (hash_inj with "Hempty Hleaf") as "%Heq".
  iPureIntro.
  destruct v as [|a]; [naive_solver|].
  (* TODO: why doesn't list_simplifier or solve_length take care of this? *)
  apply (f_equal length) in Heq.
  rewrite app_length in Heq.
  simpl in *.
  lia.
Qed.

Lemma is_path_val_inj id val1 val2 digest :
  is_path_val id val1 digest -∗
  is_path_val id val2 digest -∗
  ⌜val1 = val2⌝.
Proof.
  iInduction (id) as [|a] "IH" forall (digest);
    iIntros "Hpath1 Hpath2".
  {
    rewrite /is_path_val.
    iDestruct "Hpath1" as (tr1) "[Htree1 %Hcont1]".
    iDestruct "Hpath2" as (tr2) "[Htree2 %Hcont2]".
    destruct tr1 as [| | |ct1], tr2 as [| | |ct2], val1, val2; try naive_solver.
    { iExFalso. iApply (empty_leaf_hash_disjoint with "[$] [$]"). }
    { iExFalso. iApply (empty_leaf_hash_disjoint with "[$] [$]"). }
    destruct Hcont1 as [_ Hleaf1].
    destruct Hcont2 as [_ Hleaf2].
    inversion Hleaf1; subst l; clear Hleaf1.
    inversion Hleaf2; subst l0; clear Hleaf2.
    iDestruct (hash_inj with "[$Htree1] [$Htree2]") as "%Heq".
    by list_simplifier.
  }
  {
    iDestruct (is_path_val_inj' with "[$Hpath1] [$Hpath2]") as (digest') "[Hval1 Hval2]".
    by iSpecialize ("IH" $! digest' with "[$Hval1] [$Hval2]").
  }
Qed.

Definition own_Node' (recur : loc -d> tree -d> iPropO Σ) : loc -d> tree -d> iPropO Σ :=
  (λ ptr_tr tr,
    match tr with
    (* We should never have cuts in in-memory trees. *)
    | Cut _ => False
    | Empty =>
      ∃ hash,
      "#His_hash" ∷ is_tree_hash tr hash ∗
      "%Hnil" ∷ ⌜ptr_tr = null⌝
    | Leaf val =>
      ∃ sl_val hash sl_hash,
      "Hval" ∷ own_slice_small sl_val byteT 1 val ∗
      "Hptr_val" ∷ ptr_tr ↦[Node :: "Val"] (slice_val sl_val) ∗
      "#His_hash" ∷ is_tree_hash tr hash ∗
      "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
      "Hsl_hash" ∷ ptr_tr ↦[Node :: "hash"] (slice_val sl_hash)
    | Interior children =>
      ∃ hash sl_hash sl_children ptr_children,
      "#His_hash" ∷ is_tree_hash tr hash ∗
      "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
      "Hsl_children" ∷ own_slice_small sl_children ptrT 1 ptr_children ∗
      "Hptr_children" ∷ ptr_tr ↦[Node :: "Children"] (slice_val sl_children) ∗
      "Hchildren" ∷
        ([∗ list] child;ptr_child ∈ children;ptr_children,
          ▷ recur ptr_child child)
    end)%I.

Local Instance own_Node'_contractive : Contractive own_Node'.
Proof. solve_contractive. Qed.

Definition own_Node : loc → tree → iProp Σ := fixpoint own_Node'.

Lemma own_Node_unfold ptr obj :
  own_Node ptr obj ⊣⊢ (own_Node' own_Node) ptr obj.
Proof.
  apply (fixpoint_unfold own_Node').
Qed.

Definition tree_to_map (tr : tree) : gmap (list u8) (list u8) :=
  let fix traverse (tr : tree) (acc : gmap (list u8) (list u8)) (id : list u8) :=
    match tr with
    | Cut _ => acc
    | Empty => acc
    | Leaf val => <[id:=val]>acc
    | Interior children =>
      (* Grab all entries from the children, storing the ongoing id. *)
      (foldr
        (λ child (pIdxAcc:(Z * gmap (list u8) (list u8))),
          let acc' := traverse child pIdxAcc.2 (id ++ [U8 pIdxAcc.1])
          in (pIdxAcc.1 + 1, acc'))
        (0, acc) children
      ).2
    end
  in traverse tr ∅ [].

Definition own_Tree ptr_tr entry_map : iProp Σ :=
  ∃ tr root,
  "Hnode" ∷ own_Node root tr ∗
  "%Htree_map" ∷ ⌜tree_to_map tr = entry_map⌝ ∗
  "Hptr_root" ∷ ptr_tr ↦[Tree :: "Root"] #root.

(* Note: make everything RO for easy big sep logic. *)
Definition is_Slice2D (sl_dim0 : Slice.t) (obj_dim0 : list (list u8)) : iProp Σ :=
  ∃ list_dim0,
  "#Hro_sl_dim0" ∷ readonly (own_slice_small sl_dim0 (slice.T byteT) 1 list_dim0) ∗
  "#Hsep_dim0" ∷ ([∗ list] sl_dim1;obj_dim1 ∈ list_dim0;obj_dim0,
    "#Hro_sl_dim1" ∷ readonly (own_slice_small sl_dim1 byteT 1 obj_dim1)).

Definition is_Slice3D (sl_dim0 : Slice.t) (obj_dim0 : list (list (list u8))) : iProp Σ :=
  ∃ list_dim0,
  "#Hro_sl_dim0" ∷ readonly (own_slice_small sl_dim0 (slice.T (slice.T byteT)) 1 list_dim0) ∗
  "#Hsep_dim0" ∷ ([∗ list] sl_dim1;obj_dim1 ∈ list_dim0;obj_dim0,
    ∃ list_dim1,
    "#Hro_sl_dim1" ∷ readonly (own_slice_small sl_dim1 (slice.T byteT) 1 list_dim1) ∗
    "#Hsep_dim1" ∷ ([∗ list] sl_dim2;obj_dim2 ∈ list_dim1;obj_dim1,
      "#Hro_sl_dim2" ∷ readonly (own_slice_small sl_dim2 byteT 1 obj_dim2))).

End defs.

Module PathProof.
Record t :=
  mk {
    Id: list u8;
    NodeHash: list u8;
    Digest: list u8;
    ChildHashes: list (list (list u8));
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_Id sl_NodeHash sl_Digest sl_ChildHashes,
  "HId" ∷ own_slice_small sl_Id byteT 1 obj.(Id) ∗
  "Hptr_Id" ∷ ptr ↦[PathProof :: "Id"] (slice_val sl_Id) ∗
  "HNodeHash" ∷ own_slice_small sl_NodeHash byteT 1 obj.(NodeHash) ∗
  "Hptr_NodeHash" ∷ ptr ↦[PathProof :: "NodeHash"] (slice_val sl_NodeHash) ∗
  "HDigest" ∷ own_slice_small sl_Digest byteT 1 obj.(Digest) ∗
  "Hptr_Digest" ∷ ptr ↦[PathProof :: "Digest"] (slice_val sl_Digest) ∗
  "#HChildHashes" ∷ is_Slice3D sl_ChildHashes obj.(ChildHashes) ∗
  "Hptr_ChildHashes" ∷ ptr ↦[PathProof :: "ChildHashes"] (slice_val sl_ChildHashes) ∗
  "%Hlen_id_depth" ∷ ⌜length obj.(Id) = length obj.(ChildHashes)⌝ ∗
  "%Hlen_id_ub" ∷ ⌜length obj.(Id) ≤ 32⌝.
End local_defs.
End PathProof.

Section proofs.
Context `{!heapGS Σ}.

Lemma wp_Put ptr_tr entry_map sl_id id sl_val val :
  {{{
    "Htree" ∷ own_Tree ptr_tr entry_map ∗
    "Hid" ∷ own_slice_small sl_id byteT 1 id ∗
    "Hval" ∷ own_slice_small sl_val byteT 1 val
  }}}
  Tree__Put #ptr_tr (slice_val sl_id) (slice_val sl_val)
  {{{
    sl_digest ptr_proof (err : u64),
    RET ((slice_val sl_digest), #ptr_proof, #err);
    if bool_decide (err = 0) then
      "Htree" ∷ own_Tree ptr_tr (<[id:=val]>entry_map)
    else True%I
  }}}.
Proof. Admitted.

Lemma wp_NodeHashNull :
  {{{ True }}}
  Node__Hash #null
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
    "#His_hash" ∷ is_tree_hash Empty hash
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /Node__Hash.
  wp_apply wp_SliceSingleton; [val_ty|];
    iIntros (sl_data) "Hdata".
  wp_apply (wp_Hash with "[Hdata]").
  {
    iDestruct (slice.own_slice_to_small with "Hdata") as "Hdata".
    rewrite /own_slice_small.
    instantiate (1:=[_]).
    iFrame.
  }
  iIntros (??) "H"; iNamed "H".
  iApply "HΦ".
  iFrame "#∗".
Qed.

Lemma wp_HasherWrite sl_hr hr ptr_hr sl_data (data : list u8) :
  {{{
    "Hhr" ∷ own_slice_small sl_hr byteT 1 hr ∗
    "Hptr_hr" ∷ ptr_hr ↦[slice.T byteT] (slice_val sl_hr) ∗
    "#Hdata" ∷ readonly (own_slice_small sl_data byteT 1 data)
  }}}
  HasherWrite #ptr_hr (slice_val sl_data)
  {{{
    sl_hr', RET #();
    "Hhr" ∷ own_slice_small sl_hr' byteT 1 (hr ++ data) ∗
    "Hptr_hr" ∷ ptr_hr ↦[slice.T byteT] (slice_val sl_hr')
  }}}.
Proof. Admitted.

Lemma wp_HasherWriteSl sl_hr hr ptr_hr sl_data data :
  {{{
    "Hhr" ∷ own_slice_small sl_hr byteT 1 hr ∗
    "Hptr_hr" ∷ ptr_hr ↦[slice.T byteT] (slice_val sl_hr) ∗
    "#Hdata" ∷ is_Slice2D sl_data data
  }}}
  HasherWriteSl #ptr_hr (slice_val sl_data)
  {{{
    sl_hr', RET #();
    "Hhr" ∷ own_slice_small sl_hr' byteT 1 (hr ++ concat data) ∗
    "Hptr_hr" ∷ ptr_hr ↦[slice.T byteT] (slice_val sl_hr')
  }}}.
Proof. Admitted.

Lemma wp_HasherSumNil sl_hr hr :
  {{{
    "Hhr" ∷ own_slice_small sl_hr byteT 1 hr
  }}}
  HasherSum (slice_val sl_hr) slice.nil
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "#Hhash" ∷ is_hash hr hash ∗
    "Hsl_hash" ∷ own_slice_small sl_hash byteT 1 hash
  }}}.
Proof. Admitted.

Lemma wp_IsValidHashSl sl_data data :
  {{{
    "#Hdata" ∷ is_Slice2D sl_data data
  }}}
  IsValidHashSl (slice_val sl_data)
  {{{
    (ok : bool), RET #ok;
    if bool_decide ok then
      "%Hlen" ∷ ([∗ list] l ∈ data, ⌜length l = 32%nat⌝)
    else True%I
  }}}.
Proof. Admitted.

Lemma wp_PathProofCheck ptr_proof proof val :
  {{{
    "Hproof" ∷ PathProof.own ptr_proof proof ∗
    let node := match val with
    | None => Empty
    | Some val' => Leaf val'
    end in
    "Hhash" ∷ is_tree_hash node proof.(PathProof.NodeHash)
  }}}
  PathProof__Check #ptr_proof
  {{{
    (err : u64), RET #err;
    if bool_decide (err = 0) then
      "Hpath" ∷ is_path_val proof.(PathProof.Id) val proof.(PathProof.Digest)
    else True%I
  }}}.
Proof.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hproof".
  rewrite /PathProof__Check.
  wp_apply wp_ref_to; [val_ty|];
    iIntros (ptr_err) "Hptr_err".
  wp_loadField.
  wp_apply wp_ref_to; [val_ty|]. iIntros (ptr_currHash) "HcurrHash".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_apply wp_ref_to; [val_ty|]; iIntros (ptr_loopIdx) "HloopIdx".
  iDestruct ("HChildHashes") as (?) "H"; iNamed "H".
  iMod (readonly_alloc_1 with "HNodeHash") as "#Hro_NodeHash".
  iDestruct (big_sepL2_length with "Hsep_dim0") as "%Hlen_ChildHashes".
  iMod (readonly_load with "Hro_sl_dim0") as (q) "H";
    iDestruct (own_slice_small_sz with "H") as "%Hlen_list_dim0";
    iClear (q) "H".

  (* Entering the main loop. *)
  set for_inv :=
    (λ loopIdx, ∃ sl_currHash currHash (err : u64),
      "HId" ∷ own_slice_small sl_Id byteT 1 proof.(PathProof.Id) ∗
      "Hptr_Id" ∷ ptr_proof ↦[PathProof :: "Id"] sl_Id ∗
      "Hptr_ChildHashes" ∷ ptr_proof ↦[PathProof :: "ChildHashes"] sl_ChildHashes ∗
      "#Hro_sl_currHash" ∷ readonly (own_slice_small sl_currHash byteT 1 currHash) ∗
      "Hptr_currHash" ∷ ptr_currHash ↦[slice.T byteT] sl_currHash ∗
      "Hptr_err" ∷ ptr_err ↦[uint64T] #err ∗
      "Herr_pred" ∷ if bool_decide (err = 0) then
        "Hpath_val" ∷ is_path_val
          (drop (length proof.(PathProof.Id) - int.nat loopIdx)
          proof.(PathProof.Id)) val currHash
      else True)%I : u64 → iProp Σ.
  wp_apply (wp_forUpto for_inv with "[] [$HId $Hptr_Id $Hptr_ChildHashes $HloopIdx $HcurrHash $Hro_NodeHash $Hptr_err Hhash]"); [word|..].
  2: {
    assert ((length proof.(PathProof.Id) - int.nat 0)%nat = length proof.(PathProof.Id)) as H by word;
      iEval (rewrite H); clear H.
    iEval (rewrite drop_all).
    iFrame.
    destruct val; done.
  }
  {
    iEval (rewrite /for_inv); clear for_inv.
    iIntros (loopIdx Φ2) "!> (Hinv & HloopIdx & %HloopBound) HΦ2";
      iNamed "Hinv".
    wp_load.
    wp_apply (wp_loadField with "[$Hptr_ChildHashes]");
      iIntros "Hptr_ChildHashes".

    (* Note: move all the sep fetches into one block, like this. *)
    iMod (readonly_load with "Hro_sl_dim0") as (?) "Hsl_dim0".
    assert (∃ (sl_dim1' : Slice.t),
      list_dim0 !! int.nat (length list_dim0 - 1 - int.nat loopIdx) =
      Some sl_dim1') as [sl_dim1' Hlook_sl_dim1'].
    { apply lookup_lt_is_Some. word. }
    iDestruct (big_sepL2_lookup_1_some with "Hsep_dim0") as %[obj_dim1' Hlook_obj_dim1']; [done|].
    iDestruct (big_sepL2_lookup with "Hsep_dim0") as (list_dim1') "H";
      [done..|]; iNamed "H".
    iMod (readonly_load with "Hro_sl_dim1") as (?) "Hsl_dim1".
    iDestruct (own_slice_small_sz with "Hsl_dim1") as "%Hlen_list_dim1'".
    iDestruct (big_sepL2_length with "Hsep_dim1") as "%Hlen_obj_dim1'".
    iDestruct (own_slice_small_sz with "HId") as "%Hlen_Id".

    (* Rewrite this early since it appears in multiple sub-terms. *)
    replace (word.sub (word.sub sl_ChildHashes.(Slice.sz) 1) loopIdx) with
      (U64 (length list_dim0 - 1 - int.nat loopIdx)) by word.

    wp_apply (wp_SliceGet with "[$Hsl_dim0]"); [done|];
      iIntros "Hsl_dim0".
    wp_apply wp_slice_len.

    wp_if_destruct.
    { wp_store. iApply "HΦ2". by iFrame "#∗". }
    replace (word.sub 256 1) with (U64 255) in Heqb;
      [|word]; rename Heqb into Hsz_sl_dim1'.
    wp_apply (wp_IsValidHashSl with "[$Hro_sl_dim1 $Hsep_dim1]").
      iIntros (ok) "H".
    wp_if_destruct.
    { wp_store. iApply "HΦ2". by iFrame "#∗". }
    iSimpl in "H"; iNamed "H"; rename Hlen into Hhash_len_obj_dim1'.

    wp_apply (wp_loadField with "[$Hptr_Id]");
      iIntros "Hptr_Id".
    assert (∃ (pos : u8),
      proof.(PathProof.Id) !! int.nat (length list_dim0 - 1 - int.nat loopIdx) =
      Some pos) as [pos Hlook_pos].
    { apply lookup_lt_is_Some. word. }
    wp_apply (wp_SliceGet with "[$HId]"); [done|];
      iIntros "HId".

    (* TODO: word should know this. *)
    assert (length list_dim1' = 255%nat) as H255_list_dim1'.
    { rewrite Hlen_list_dim1'. rewrite Hsz_sl_dim1'. word. }
    (* Note: this slows down word for some reason. *)
    pose proof (word.unsigned_range pos) as Hpos_bound.

    (* The complicated slice splitting logic. *)
    iDestruct (own_slice_small_wf with "Hsl_dim1") as "%Hwf_sl_dim1".
    iDestruct (slice_small_split _ (u8_to_u64 pos) with "Hsl_dim1") as "[Hsl_before Hsl_after]".
    (* TODO: word should know this. *)
    { rewrite u8_to_u64_Z. lia. }
    wp_apply wp_SliceTake.
    { rewrite u8_to_u64_Z. lia. }
    wp_apply wp_SliceSkip.
    { rewrite u8_to_u64_Z. lia. }
    iEval (rewrite u8_to_u64_Z) in "Hsl_before".
    iEval (rewrite u8_to_u64_Z) in "Hsl_after".
    (* TODO: we really shouldn't need to type in the entire P here. *)
    iMod (readonly_alloc (own_slice_small (slice_take sl_dim1' (u8_to_u64 pos)) (slice.T byteT) 1 (take (int.nat pos) list_dim1')) with "[$Hsl_before]") as "#Hro_sl_before".
    iMod (readonly_alloc (own_slice_small (slice_skip sl_dim1' (slice.T byteT) (u8_to_u64 pos)) (slice.T byteT) 1 (drop (int.nat pos) list_dim1')) with "[$Hsl_after]") as "#Hro_sl_after".

    wp_apply wp_ref_of_zero; [done|];
      iIntros (ptr_hr) "Hptr_hr".
    iEval (rewrite zero_slice_val) in "Hptr_hr".
    iDestruct (own_slice_small_nil byteT 1 (Slice.nil)) as "Hnil"; [done|].
    wp_apply (wp_HasherWriteSl with "[$Hptr_hr $Hnil $Hro_sl_before]").
    {
      iApply big_sepL2_prefix.
      4: iFrame "#".
      1: apply prefix_take.
      1: apply (prefix_take _ (int.nat pos)).
      { do 2 rewrite take_length. lia. }
    }
    iIntros (sl_hr) "H"; iNamed "H".
    wp_load.
    wp_apply (wp_HasherWrite with "[$Hptr_hr $Hhr $Hro_sl_currHash]");
      clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_apply (wp_HasherWriteSl with "[$Hptr_hr $Hhr $Hro_sl_after]").
    {
      iApply big_sepL2_suffix.
      4: iFrame "#".
      1: apply suffix_drop.
      1: apply (suffix_drop _ (int.nat pos)) .
      { do 2 rewrite drop_length. lia. }
    }
    clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_apply wp_SliceSingleton; [val_ty|];
      iIntros (sl_tag) "H";
      iDestruct (slice.own_slice_to_small with "H") as "Hsl_tag".
    iAssert (own_slice_small _ _ _ [U8 2]) with "Hsl_tag" as "Hsl_tag".
    iMod (readonly_alloc_1 with "Hsl_tag") as "#Hro_sl_tag".
    wp_apply (wp_HasherWrite with "[$Hptr_hr $Hhr $Hro_sl_tag]").
    clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_load.
    wp_apply (wp_HasherSumNil with "Hhr");
      iIntros (sl_hash hash) "H"; iNamed "H".
    wp_store.
    iMod (readonly_alloc_1 with "Hsl_hash") as "#Hro_sl_hash".
    iClear (sl_tag) "Hro_NodeHash Hro_sl_before Hro_sl_after Hnil Hro_sl_tag".

    (* Done with code, now re-establish loop inv. *)
    case_bool_decide; rename H into Herr; iNamed "Herr_pred".
    2: { iApply "HΦ2". iFrame "#∗". by case_bool_decide. }
    iApply "HΦ2".
    iFrame "#∗".
    case_bool_decide; [|done].
    clear Herr H.

    rewrite /is_path_val.
    iDestruct "Hpath_val" as (tr) "[Htr_hash %Htr_contains]".
    iExists (Interior (
      ((λ h, Cut h) <$> (take (int.nat pos) obj_dim1')) ++
      [tr] ++
      ((λ h, Cut h) <$> (drop (int.nat pos) obj_dim1')))).
    iIntros "!>".
    iSplit.
    {
      iExists (
        (take (int.nat pos) obj_dim1') ++
        [currHash] ++
        (drop (int.nat pos) obj_dim1')).
      iSplit.
      {
        iEval (rewrite fmap_app).
        iApply big_sepL2_app.
        {
          iEval (rewrite <-list_fmap_compose).
          iApply big_sepL2_fmap_l.
          iApply big_sepL_sepL2_diag.
          iApply big_sepL_take.
          iPureIntro.
          naive_solver.
        }
        iEval (rewrite fmap_cons).
        iApply big_sepL2_cons.
        iFrame.
        {
          iEval (rewrite <-list_fmap_compose).
          iApply big_sepL2_fmap_l.
          iApply big_sepL_sepL2_diag.
          iApply (big_sepL_drop (λ _ _, _)).
          iPureIntro.
          naive_solver.
        }
      }
      iEval (do 2 rewrite concat_app).
      by list_simplifier.
    }
    iPureIntro.
    clear Hpos_bound.
    rewrite (drop_S _ pos _ _).
    2: { rewrite <-Hlook_pos. f_equal. word. }
    (* TODO: is there a good way of extracting this goal automatically? *)
    replace (S (length proof.(PathProof.Id) - int.nat (word.add loopIdx 1))) with
      ((length proof.(PathProof.Id) - int.nat loopIdx)%nat) by word.
    exists tr.
    split; [|done].
    rewrite (lookup_app_r _ _ _ _).
    2: {
      rewrite fmap_length.
      rewrite (take_length_le _ _ _); [done|].
      pose proof (word.unsigned_range pos) as Hpos_bound.
      lia.
    }
    rewrite fmap_length.
    rewrite (take_length_le _ _ _).
    2: { pose proof (word.unsigned_range pos) as Hpos_bound. lia. }
    replace ((int.nat pos - int.nat pos)%nat) with (0%nat) by lia.
    naive_solver.
  }

  (* Last chunk of code after for loop. *)
  iEval (rewrite /for_inv); clear for_inv.
  iIntros "[H _]"; iNamed "H".
  wp_load.
  wp_if_destruct; [by iApply "HΦ"|].
  iSimpl in "Herr_pred"; iNamed "Herr_pred".
  wp_apply (wp_loadField with "Hptr_Digest");
    iIntros "Hptr_Digest".
  wp_load.
  iMod (readonly_load with "Hro_sl_currHash") as (?) "Hsl_currHash".
  wp_apply (wp_BytesEqual with "[$Hsl_currHash $HDigest]");
    iIntros "[Hsl_currHash HDigest]".
  wp_if_destruct; [by iApply "HΦ"|].
  iEval (replace ((length proof.(PathProof.Id) - int.nat sl_ChildHashes.(Slice.sz))%nat)
    with (0%nat) by word) in "Hpath_val".
  iEval (rewrite drop_0 Heqb) in "Hpath_val".
  by iApply "HΦ".
Qed.

Lemma wp_MembProofCheck sl_proof proof sl_id sl_val sl_digest (id val digest : list u8) :
  {{{
    "#Hproof" ∷ is_Slice3D sl_proof proof ∗
    "Hid" ∷ own_slice_small sl_id byteT 1 id ∗
    "Hval" ∷ own_slice_small sl_val byteT 1 val ∗
    "Hdigest" ∷ own_slice_small sl_digest byteT 1 digest
  }}}
  MembProofCheck (slice_val sl_proof) (slice_val sl_id) (slice_val sl_val) (slice_val sl_digest)
  {{{
    (err:u64), RET #err;
    if bool_decide (err = 0) then
      "#Hpath" ∷ is_path_val id (Some val) digest
    else True%I
  }}}.
Proof.
  iIntros (Φ) "H HΦ"; iNamed "H".
  rewrite /MembProofCheck.
  admit.
Admitted.

Lemma wp_NonmembCheck sl_proof proof sl_id sl_digest (id digest : list u8) :
  {{{
    "#Hproof" ∷ is_Slice3D sl_proof proof ∗
    "Hid" ∷ own_slice_small sl_id byteT 1 id ∗
    "Hdigest" ∷ own_slice_small sl_digest byteT 1 digest
  }}}
  NonmembProofCheck (slice_val sl_proof) (slice_val sl_id) (slice_val sl_digest)
  {{{
    (err:u64), RET #err;
    if bool_decide (err = 0) then
      "#Hpath" ∷ is_path_val id None digest
    else True%I
  }}}.
Proof. Admitted.

End proofs.
