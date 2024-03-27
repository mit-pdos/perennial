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

Lemma is_tree_hash_unfold tree hash :
  is_tree_hash tree hash ⊣⊢ (is_tree_hash' is_tree_hash) tree hash.
Proof.
  apply (fixpoint_unfold is_tree_hash').
Qed.

(* XXX: is there a more concise proof? *)
#[global]
Instance is_tree_hash_persistent tr hash : Persistent (is_tree_hash tr hash).
Proof.
  rewrite /Persistent.
  iStartProof.
  iLöb as "IH" forall (tr hash).
  iIntros "H".
  rewrite is_tree_hash_unfold /is_tree_hash'.
  destruct tr.
  1-3: iDestruct "H" as "#H"; eauto.
  iDestruct "H" as (?) "[H #?]".
  iExists _. iFrame "#".
  iApply big_sepL2_persistently.
  iApply (big_sepL2_impl with "H").
  iIntros "!> * % % H".
  iApply later_persistently_1.
  iNext. iDestruct ("IH" with "H") as "#H2".
  eauto.
Qed.

(* Not sure how to prove this. Should be true because tr is well founded, and
   is_tree_hash' only has timeless stuff. *)
#[global]
Instance is_tree_hash_timeless tr hash : Timeless (is_tree_hash tr hash).
Proof.
  rewrite /Timeless.
  iStartProof.
  iLöb as "IH" forall (tr hash).
  (* iInduction tr as [| | |] "IH". forall (tr hash). *)
  iIntros "H".
  rewrite is_tree_hash_unfold /is_tree_hash'.
  destruct tr.
  1-3: by iMod "H".
  iDestruct "H" as (?) "[H >?]".
  iExists _. iFrame.
  iAssert (
    ∀ (tr : tree) (hash0 : list u8), (▷ ▷ is_tree_hash tr hash0) -∗ (▷ ◇ is_tree_hash tr hash0)
    )%I with "[IH]" as "#IH2".
  {
    iIntros. iSpecialize ("IH" $! _ _).
    iNext. iApply "IH". iFrame "#".
  }
  iDestruct (big_sepL2_later_1 with "H") as ">H".
  iApply big_sepL2_later_1. iApply big_sepL2_later_2.
  iApply (big_sepL2_impl with "H").
  iIntros "!> * % % H".
  iDestruct ("IH2" with "H") as "H".
  iNext.
  admit.
Admitted.

Lemma tree_hash_len tr hash :
  is_tree_hash tr hash -∗ ⌜length hash = 32%nat⌝.
Proof.
  iIntros "Htree".
  destruct tr;
    iDestruct (is_tree_hash_unfold with "Htree") as "Htree";
    simpl.
  { iDestruct "Htree" as "[%Heq %Hlen]". naive_solver. }
  { iDestruct (hash_len with "Htree") as "%Hlen". naive_solver. }
  { iDestruct (hash_len with "Htree") as "%Hlen". naive_solver. }
  {
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

Lemma concat_eq_dim1_eq {A : Type} sz (l1 l2 : list (list A)) :
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
  { f_equal; naive_solver. }
  assert (drop (length a1) (a1 ++ concat l1) = drop (length a2) (a2 ++ concat l2)) as Hdrop_concat.
  { f_equal; naive_solver. }
  do 2 rewrite take_app_length in Htake_concat.
  do 2 rewrite drop_app_length in Hdrop_concat.
  rewrite Htake_concat.
  apply (app_inv_head_iff [a2]).
  apply IHl1; try eauto with lia.
Qed.

Lemma is_path_val_inj' pos rest val1 val2 digest :
  is_path_val (pos :: rest) val1 digest -∗
  (* Need fupd so we can remove ▷ in is_tree_hash. *)
  is_path_val (pos :: rest) val2 digest ={⊤}=∗
  ∃ digest',
  is_path_val rest val1 digest' ∗
  is_path_val rest val2 digest'.
Proof.
  iIntros "Hval1 Hval2".
  rewrite /is_path_val.
  iDestruct "Hval1" as (tr1) "[#Htree1 %Hcont1]".
  iDestruct "Hval2" as (tr2) "[#Htree2 %Hcont2]".
  destruct tr1 as [| | |ct1], tr2 as [| | |ct2]; try naive_solver.

  (* Get contains pred. *)
  simpl in *.
  destruct Hcont1 as [child1 [Hlist1 Hcont1]].
  destruct Hcont2 as [child2 [Hlist2 Hcont2]].

  (* Get is_tree_hash for children. *)
  iRename "Htree1" into "H";
    iDestruct (is_tree_hash_unfold with "H") as "Htree1";
    iClear "H".
  iRename "Htree2" into "H";
    iDestruct (is_tree_hash_unfold with "H") as "Htree2";
    iClear "H".
  simpl.
  iDestruct "Htree1" as (ch1) "[Htree1 Hdig1]".
  iDestruct "Htree2" as (ch2) "[Htree2 Hdig2]".

  iRename "Htree1" into "H";
    iDestruct (big_sepL2_later_2 with "H") as "Htree1";
    iClear "H".
  iRename "Htree2" into "H";
    iDestruct (big_sepL2_later_2 with "H") as "Htree2";
    iClear "H".
  iMod "Htree1".
  iMod "Htree2".

  (* Use is_hash ch1/ch2 digest to prove that child hashes are same. *)
  iAssert (⌜Forall (λ l, length l = 32%nat) ch1⌝%I) as %Hlen_ch1.
  {
    iDestruct (big_sepL2_impl _ (λ _ _ h, ⌜length h = 32%nat⌝%I) with "Htree1 []") as "Hlen_sepL2".
    {
      iIntros "!>" (???) "_ _ Hhash".
      iDestruct (tree_hash_len with "Hhash") as "Hlen".
      naive_solver.
    }
    iDestruct (big_sepL2_const_sepL_r with "Hlen_sepL2") as "[_ %Hlen_sepL1]".
    iPureIntro.
    by apply Forall_lookup.
  }
  iAssert (⌜Forall (λ l, length l = 32%nat) ch2⌝%I) as %Hlen_ch2.
  {
    iDestruct (big_sepL2_impl _ (λ _ _ h, ⌜length h = 32%nat⌝%I) with "Htree2 []") as "Hlen_sepL2".
    {
      iIntros "!>" (???) "_ _ Hhash".
      iDestruct (tree_hash_len with "Hhash") as "Hlen".
      naive_solver.
    }
    iDestruct (big_sepL2_const_sepL_r with "Hlen_sepL2") as "[_ %Hlen_sepL1]".
    iPureIntro.
    by apply Forall_lookup.
  }

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

  iIntros "!>".
  iExists h2.
  iSplit.
  { iExists child1. iFrame "%#". }
  { iExists child2. iFrame "%#". }
Qed.

Lemma is_path_val_inj id val1 val2 digest :
  is_path_val id val1 digest -∗
  is_path_val id val2 digest -∗
  ⌜val1 = val2⌝.
Proof.
  iLöb as "IH" forall (id val1 val2 digest) "".
  admit.
Admitted.

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
