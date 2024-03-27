From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat.merkle Require Import merkle_shim.
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

Definition is_nil_hash hash : iProp Σ :=
  is_hash [] hash.

Definition is_tree_hash' (recur : tree -d> list u8 -d> iPropO Σ) : tree -d> list u8 -d> iPropO Σ :=
  (λ tr hash,
  match tr with
  | Cut hash' => ⌜hash = hash' ∧ length hash' = 32%nat⌝
  | Empty => is_hash [U8 0] hash
  | Leaf val => is_hash (val ++ [U8 1]) hash
  | Interior children =>
      ∃ (child_hashes : list (list u8)),
      ([∗ list] child;hash' ∈ children;child_hashes,
        ▷ recur child hash') ∗
      is_hash (concat child_hashes ++ [U8 2]) hash
  end)%I.

Local Instance is_tree_hash'_contractive : Contractive is_tree_hash'.
Proof. solve_contractive. Qed.

Definition is_tree_hash : tree → list u8 → iProp Σ := fixpoint is_tree_hash'.

#[global]
Instance is_tree_hash_persistent tr hash : Persistent (is_tree_hash tr hash).
Proof. Admitted.

Lemma is_tree_hash_unfold tr hash :
  is_tree_hash tr hash ⊣⊢ (is_tree_hash' is_tree_hash) tr hash.
Proof.
  apply (fixpoint_unfold is_tree_hash').
Qed.

Lemma tree_hash_len tr hash :
  is_tree_hash tr hash -∗ ⌜length hash = 32%nat⌝.
Proof.
  iIntros "Htree".
  destruct tr.
  {
    iDestruct (is_tree_hash_unfold with "Htree") as "Htree".
    simpl.
    iDestruct "Htree" as "[%Heq %Hlen]".
    naive_solver.
  }
  {
    iDestruct (is_tree_hash_unfold with "Htree") as "Htree".
    simpl.
    iDestruct (hash_len with "Htree") as "%Hlen".
    naive_solver.
  }
  {
    iDestruct (is_tree_hash_unfold with "Htree") as "Htree".
    simpl.
    iDestruct (hash_len with "Htree") as "%Hlen".
    naive_solver.
  }
  {
    iDestruct (is_tree_hash_unfold with "Htree") as "Htree".
    simpl.
    iDestruct "Htree" as (ch) "[_ Htree]".
    iDestruct (hash_len with "Htree") as "%Hlen".
    naive_solver.
  }
Qed.

Definition is_path_node id node digest : iProp Σ :=
  ∃ tr,
  is_tree_hash tr digest ∧
  ⌜containsNodeAtEnd tr id node⌝.

Definition is_path_val id val digest : iProp Σ :=
  ∃ tr,
  is_tree_hash tr digest ∧
  ⌜containsNodeAtEnd tr id
    match val with
    | None => Empty
    | Some val' => Leaf val'
    end⌝.

Lemma concat_eq_dim1_eq {A : Type} (l1 l2 : list (list A)) sz :
  concat l1 = concat l2 →
  (Forall (λ l, length l = sz) l1) →
  (Forall (λ l, length l = sz) l2) →
  0 < sz →
  l1 = l2.
Proof.
  intros Heq_concat Hlen_l1 Hlen_l2 Hsz.
  assert (length (concat l1) = length (concat l2))
    as Heq_concat_len by eauto with f_equal.
  do 2 rewrite concat_length in Heq_concat_len.
  generalize dependent l2.
  induction l1 as [|a1]; destruct l2 as [|a2]; simpl;
    intros Heq_concat Hlen_l2 Heq_concat_len.
  { reflexivity. }
  { apply Forall_inv in Hlen_l2. lia. }
  { apply Forall_inv in Hlen_l1. lia. }
  apply Forall_cons_iff in Hlen_l1 as [Hlen_a1 Hlen_l1].
  apply Forall_cons_iff in Hlen_l2 as [Hlen_a2 Hlen_l2].
  assert (take (length a1) (a1 ++ concat l1) = take (length a2) (a2 ++ concat l2)) as Htake_concat.
  { rewrite Hlen_a1. rewrite Hlen_a2. rewrite Heq_concat. reflexivity. }
  assert (drop (length a1) (a1 ++ concat l1) = drop (length a2) (a2 ++ concat l2)) as Hdrop_concat.
  { rewrite Hlen_a1. rewrite Hlen_a2. rewrite Heq_concat. reflexivity. }
  do 2 rewrite take_app_length in Htake_concat.
  do 2 rewrite drop_app_length in Hdrop_concat.
  (* TODO: this is really simple, how to automate? *)
  assert (a1 = a2 → l1 = l2 → a1 :: l1 = a2 :: l2) as H by naive_solver;
    apply H; clear H; [done|].
  apply IHl1; try eauto with lia.
Qed.

Lemma helper pos rest val1 val2 digest :
  is_path_val (pos :: rest) val1 digest -∗
  is_path_val (pos :: rest) val2 digest -∗
  ∃ digest',
  is_path_val rest val1 digest' ∗
  is_path_val rest val2 digest'.
Proof.
  iIntros "Hval1 Hval2".
  rewrite /is_path_val.
  iDestruct "Hval1" as (tr1) "[#Htree1 %Hcont1]".
  iDestruct "Hval2" as (tr2) "[#Htree2 %Hcont2]".
  destruct tr1, tr2; try naive_solver.
  simpl in Hcont1, Hcont2.
  destruct Hcont1 as [child1 [Hlist1 Hcont1]].
  destruct Hcont2 as [child2 [Hlist2 Hcont2]].
  iRename "Htree1" into "H";
    iDestruct (is_tree_hash_unfold with "H") as "Htree1";
    iClear "H".
  iRename "Htree2" into "H";
    iDestruct (is_tree_hash_unfold with "H") as "Htree2";
    iClear "H".
  simpl.
  iDestruct "Htree1" as (ch1) "[Htree1 Hdig1]".
  iDestruct "Htree2" as (ch2) "[Htree2 Hdig2]".

  iDestruct (big_sepL2_lookup_1_some with "Htree1") as (h1) "%Helem1"; [done|].
  iDestruct (big_sepL2_lookup_1_some with "Htree2") as (h2) "%Helem2"; [done|].
  iDestruct (big_sepL2_lookup with "Htree1") as "Helem1"; [done..|].
  iDestruct (big_sepL2_lookup with "Htree2") as "Helem2"; [done..|].

  iDestruct (hash_inj with "Hdig1 Hdig2") as "%Heq".
  apply app_inv_tail in Heq.
  (*
     have big_sepL2 with child;hash' and is_tree_hash child hash'.
     from each tree_hash, get hash len eq.
     Then prove the concat lemma.
     Also need tree_hash 
     
     Want oneL equiv to twoL if twoL func doesn't talk about 1L.
   *)
  iAssert ([∗ list] hash' ∈ ch1, ⌜length ch1 
  Search big_sepL2 big_opL.
  About big_sepL2_impl.
  iDestruct (big_sepL2_impl _ (λ _ _ h, ⌜length h = 32%nat⌝%I) with "Htree1") as "H".

Lemma is_path_val_inj id val1 val2 digest :
  is_path_val id val1 digest -∗
  is_path_val id val2 digest -∗
  ⌜val1 = val2⌝.
Proof.
  iLöb as "IH" forall (id val1 val2 digest) "".
`iLöb as "IH" forall (x1 ... xn) "selpat"` 


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
  let fix traverse (tr : tree) (acc : gmap (list u8) (list u8)) (path : list u8) :=
    match tr with
    | Cut _ => acc
    | Empty => acc
    | Leaf val => <[path:=val]>acc
    | Interior children =>
      (* Grab all entries from the children, storing the ongoing path. *)
      (foldr
        (λ child (pIdxAcc:(Z * gmap (list u8) (list u8))),
          let acc' := traverse child pIdxAcc.2 (path ++ [U8 pIdxAcc.1])
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

Definition is_Slice3D (sl : Slice.t) (obj0 : list (list (list u8))) : iProp Σ :=
  ∃ list_sl0,
  readonly (own_slice_small sl (slice.T (slice.T byteT)) 1 list_sl0) ∗
  ([∗ list] obj1;sl_1 ∈ obj0;list_sl0,
    ∃ list_sl1,
    readonly (own_slice_small sl_1 (slice.T byteT) 1 list_sl1) ∗
    ([∗ list] obj2;sl_2 ∈ obj1;list_sl1,
      readonly (own_slice_small sl_2 byteT 1 obj2))).


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
  "Hptr_ChildHashes" ∷ ptr ↦[PathProof :: "ChildHashes"] (slice_val sl_ChildHashes).
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
    sl_digest ptr_proof (err:u64),
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
  (* SliceSingleton gives untyped slice. Need typed slice. *)
  wp_apply (wp_Hash with "[Hdata]").
  {
    iDestruct (slice.own_slice_to_small with "Hdata") as "Hdata".
    rewrite /own_slice_small.
    instantiate (1:=[_]).
    iFrame.
  }
  iIntros (??) "H"; iNamed "H".
  iApply "HΦ".
  iFrame.
  iApply is_tree_hash_unfold.
  rewrite /is_tree_hash'.
  iFrame "#".
Qed.

Lemma wp_PathProofCheck ptr_proof proof node :
  {{{
    "Hproof" ∷ PathProof.own ptr_proof proof ∗
    "#Hvalid_NodeHash" ∷ is_tree_hash node proof.(PathProof.NodeHash) ∗
    "%Hproof_len_eq" ∷ ⌜length proof.(PathProof.Id) = length proof.(PathProof.ChildHashes)⌝ ∗
    "%Hproof_len_ub" ∷ ⌜length proof.(PathProof.Id) ≤ 32⌝
  }}}
  PathProof__Check #ptr_proof
  {{{
    (err:u64), RET #err;
    if bool_decide (err = 0) then
      "#Hpath" ∷ is_path_node proof.(PathProof.Id) node proof.(PathProof.Digest)
    else True%I
  }}}.
Proof.
  iIntros (Φ) "H HΦ"; iNamed "H".
  rewrite /PathProof__Check.
  iNamed "Hproof".
  wp_loadField.
  wp_apply wp_slice_len.
  iDestruct (own_slice_small_sz with "HId") as "%Hid_sz".
  wp_if_destruct.
  {
    (* Case: empty tree. *)
    wp_apply wp_ref_of_zero; [done|].
    iIntros (ptr_empty) "Hempty".
    wp_loadField.
    wp_loadField.
    wp_apply (wp_BytesEqual with "[$HNodeHash $HDigest]");
      iIntros "[HNodeHash HDigest]".
    wp_if_destruct; [|by iApply "HΦ"].
    wp_load.
    wp_apply (wp_NodeHashNull); iIntros (??) "H"; iNamed "H".
    wp_loadField.
    wp_apply (wp_BytesEqual with "[$HNodeHash $Hhash]");
      iIntros "[HNodeHash Hhash]".
    wp_if_destruct; [|by iApply "HΦ"].
    iApply "HΦ".
    iIntros "!>".
    rewrite /is_path_node.
    iExists Empty.
    subst hash.
    rewrite Heqb0.
    iSplit; [iFrame "#"|].
    rewrite Heqb in Hid_sz.
    apply length_zero_iff_nil in Hid_sz.
    rewrite Hid_sz.
    iDestruct (is_tree_hash_inj with "Hvalid_NodeHash His_hash") as %Hnode.
    rewrite Hnode.
    naive_solver.
  }

  (* By the end of this next block, we should have is_tree_hash holding
     on the bottom-most node of the tree. *)
  wp_loadField.
  admit.
Admitted.

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
