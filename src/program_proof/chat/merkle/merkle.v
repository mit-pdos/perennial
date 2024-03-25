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

Definition containsValAtEnd (tr : tree) (id : list u8) (val : option (list u8)) : Prop :=
  match val with
  | None => containsNodeAtEnd tr id Empty
  | Some val' => containsNodeAtEnd tr id (Leaf val')
  end.

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

Definition is_nil_hash hash : iProp Σ :=
  is_hash [] hash.

Definition is_tree_hash' (recur : tree -d> list u8 -d> iPropO Σ) : tree -d> list u8 -d> iPropO Σ :=
  (λ tr hash,
  match tr with
  | Cut hash' => ⌜hash = hash'⌝
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

Lemma is_tree_hash_unfold tree hash :
  is_tree_hash tree hash ⊣⊢ (is_tree_hash' is_tree_hash) tree hash.
Proof.
  apply (fixpoint_unfold is_tree_hash').
Qed.

Lemma is_tree_hash_inj tree1 tree2 hash :
  is_tree_hash tree1 hash -∗
  is_tree_hash tree2 hash -∗
  ⌜tree1 = tree2⌝.
Proof. Admitted.

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

Definition is_path_node id node digest : iProp Σ :=
  ∃ tree,
  is_tree_hash tree digest ∧
  ⌜containsNodeAtEnd tree id node⌝.

Definition is_path_val id val digest : iProp Σ :=
  ∃ tree,
  is_tree_hash tree digest ∧
  ⌜containsValAtEnd tree id val⌝.

Lemma is_path_val_inj id val1 val2 digest :
  is_path_val id val1 digest -∗
  is_path_val id val2 digest -∗
  ⌜val1 = val2⌝.
Proof. Admitted.

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

Lemma wp_Put ptr_tree entry_map sl_id id sl_val val :
  {{{
    "Htree" ∷ own_Tree ptr_tree entry_map ∗
    "Hid" ∷ own_slice_small sl_id byteT 1 id ∗
    "Hval" ∷ own_slice_small sl_val byteT 1 val
  }}}
  Tree__Put #ptr_tree (slice_val sl_id) (slice_val sl_val)
  {{{
    sl_digest ptr_proof (err:u64),
    RET ((slice_val sl_digest), #ptr_proof, #err);
    if bool_decide (err = 0) then
      "Htree" ∷ own_Tree ptr_tree (<[id:=val]>entry_map)
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
