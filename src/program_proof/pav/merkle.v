From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import merkle.

From Perennial.program_proof.pav Require Import classes misc cryptoffi cryptoutil.
From Perennial.program_proof Require Import std_proof.

Section internal.
Context `{!heapGS Σ}.

Inductive tree : Type :=
  (* Cut only exists for proof checking trees. *)
  | Cut : list w8 → tree
  | Leaf : list w8 → tree
  | Interior : list (option tree) → tree.

(* The core invariant that defines the recursive hashing structure of merkle trees. *)
Fixpoint is_node_hash (tr : tree) (hash : list w8) : iProp Σ :=
  match tr with
  | Cut hash' => ⌜hash = hash' ∧ length hash' = 32%nat⌝
  | Leaf val => is_hash (val ++ [W8 1]) hash
  | Interior children =>
    ∃ (child_hashes : list (list w8)),
    let map_fn := (λ c h,
                     match c with
                     | None => is_hash [W8 0] h
                     | Some c => is_node_hash c h
                     end
                  ) in
    ([∗ list] child_fn;hash' ∈ (map_fn <$> children);child_hashes,
      child_fn hash') ∗
    is_hash (concat child_hashes ++ [W8 2]) hash
  end%I.

#[global]
Instance is_node_hash_timeless tr hash : Timeless (is_node_hash tr hash).
Proof. Admitted.

#[global]
Instance is_node_hash_persistent tr hash : Persistent (is_node_hash tr hash).
Proof. Admitted.

Lemma node_hash_len tr hash :
  is_node_hash tr hash -∗ ⌜length hash = 32%nat⌝.
Proof.
  iIntros "Htree".
  destruct tr.
  { iDestruct "Htree" as "[%Heq %Hlen]". naive_solver. }
  { iDestruct (is_hash_len with "Htree") as "%Hlen"; naive_solver. }
  {
    iDestruct "Htree" as (ch) "[_ Htree]".
    by iDestruct (is_hash_len with "Htree") as "%Hlen".
  }
Qed.

Lemma concat_len_eq {A : Type} sz (l1 l2 : list (list A)) :
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

(* Ownership of a merkle tree node, where the hashes on all nodes down path
   [path] may be invalid. *)
Definition own_node_except' (recur : option (list w8) -d> loc -d> tree -d> iPropO Σ) : option (list w8) -d> loc -d> tree -d> iPropO Σ :=
  (λ path ptr_tr tr,
     ∃ (hash val : list w8) sl_hash sl_children ptr_children sl_val,
       "Hptr_hash" ∷ ptr_tr ↦[node :: "hash"] (slice_val sl_hash) ∗
       "Hptr_val" ∷ ptr_tr ↦[node :: "val"] (slice_val sl_val) ∗
       "Hptr_children" ∷ ptr_tr ↦[node :: "children"] (slice_val sl_children) ∗

       "Hhash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
       "Hsl_children" ∷ own_slice_small sl_children ptrT (DfracOwn 1) ptr_children ∗
       "Hval" ∷ own_slice_small sl_val byteT (DfracOwn 1) val ∗

       "#His_hash" ∷ match path with
         | None => is_node_hash tr hash
         | _ => True
         end ∗
       "%Hchildren_len" ∷ ⌜ length ptr_children = uint.nat (W64 256) ⌝ ∗
       "Hchildren" ∷ match tr with
       (* We should never have cuts in in-memory trees. *)
       | Cut _ => False
       | Leaf _ => True
       | Interior children =>
           ([∗ list] idx ↦ child;ptr_child ∈ children;ptr_children,
              match child with
              | None => True
              | Some child =>
                  match path with
                  | Some (a :: path) => if decide (uint.nat a = idx) then ▷ recur (Some path) ptr_child child
                                      else ▷ recur None ptr_child child
                  | None => ▷ recur None ptr_child child
                  | Some [] => ▷ recur None ptr_child child
                  end
              end
           )
         end)%I.

Local Instance own_node_except'_contractive : Contractive own_node_except'.
Proof. Admitted.

Definition own_node_except : option (list w8) → loc → tree → iProp Σ := fixpoint own_node_except'.

Lemma own_node_except_unfold path ptr obj :
  own_node_except path ptr obj ⊣⊢ (own_node_except' own_node_except) path ptr obj.
Proof.
  apply (fixpoint_unfold own_node_except').
Qed.

Fixpoint is_tree_lookup (tr : tree) (k : list w8) (v : option (list w8)) : Prop :=
  match tr with
  | Cut _ => False
  | Leaf v' => match k with
             | [] => v = Some v'
             | _ => v = None
             end
  | Interior children =>
      match k with
      | [] => v = None
      | pos :: k => match (children !! (uint.nat pos)) with
                  | Some (Some child) => is_tree_lookup child k v
                  | Some None => v = None
                  | None => False
                  end
      end
  end.

Definition eq_tree_map (tr : tree) (m : gmap (list w8) (list w8)) : Prop :=
  ∀ k, is_tree_lookup tr k (m !! k).

Lemma own_node_except_mono path2 path1 root tr :
  match path1, path2 with
  | Some a, Some b => prefix a b
  | None, _ => True
  | _, _ => False
  end →
  own_node_except path1 root tr -∗
  own_node_except path2 root tr.
Proof.
Admitted.

End internal.

Section external.
Context `{!heapGS Σ}.

Definition full_height := (W64 32).

Definition has_tree_height tr (height : nat) : Prop :=
  (fix go tr height {struct height} :=
     match height with
     | O => match tr with Interior _ => False | _ => True end
     | S height => match tr with
                  | Leaf _ => False
                  | Cut _ => True
                  | Interior children =>
                      Forall (λ ochild,
                                match ochild with
                                | None => True
                                | Some child => go child height
                                end
                        ) children
                  end
     end) tr height.

(* own_merkle denotes ownership of a merkle tree containing some entries. *)
Definition own_merkle ptr_tr entries : iProp Σ :=
  ∃ tr (root : loc),
  "Hroot" ∷ ptr_tr ↦[Tree :: "root"] #root ∗
  "Hnode" ∷ (if decide (root = null) then ⌜ entries = ∅ ⌝
             else own_node_except None root tr) ∗
  "%Htree" ∷ ⌜ eq_tree_map tr entries ⌝ ∗
  "%Hheight" ∷ ⌜ has_tree_height tr (uint.nat full_height) ⌝
.

(* is_dig says that the tree with these entries has this digest. *)
Definition is_dig entries dig : iProp Σ :=
  ∃ tr,
  "%Htree" ∷ ⌜ eq_tree_map tr entries ⌝ ∗
  "#Hdig" ∷ is_node_hash tr dig.

Global Instance is_dig_func : Func is_dig.
Proof. Admitted.
Global Instance is_dig_inj : InjRel is_dig.
Proof. Admitted.

(* is_merkle_entry says that (id, val) is contained in the tree with this digest.
we use (val : option string) instead of (val : tree) bc there are really
only two types of nodes we want to allow. *)
Definition is_merkle_entry id val digest : iProp Σ :=
  ∃ tr, is_node_hash tr digest ∧ ⌜ is_tree_lookup tr id val ⌝.

(* is_merkle_entry_with_map says that if you know an entry as well
as the underlying map, you can combine those to get a pure map fact. *)
Lemma is_merkle_entry_with_map id val dig m :
  is_merkle_entry id val dig -∗ is_dig m dig -∗ ⌜ m !! id = val ⌝.
Proof. Admitted.

Lemma is_merkle_entry_inj id val1 val2 digest :
  is_merkle_entry id val1 digest -∗
  is_merkle_entry id val2 digest -∗
  ⌜val1 = val2⌝.
Proof.
  iInduction (id) as [|a] "IH" forall (digest).
  {
    iIntros "Hval1 Hval2".
    rewrite /is_merkle_entry.
    iDestruct "Hval1" as (tr1) "[Htree1 %Hcont1]".
    iDestruct "Hval2" as (tr2) "[Htree2 %Hcont2]".
    simpl in *.
    destruct tr1, tr2; try done; subst.
    - iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
      iPureIntro. by list_simplifier.
    - simpl. iDestruct "Htree2" as (?) "[? Htree2]".
      iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
      exfalso. by list_simplifier.
    - simpl. iDestruct "Htree1" as (?) "[? Htree1]".
      iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
      exfalso. by list_simplifier.
    - done.
  }
  {
    iIntros "Hval1 Hval2".
    rewrite /is_merkle_entry.
    iDestruct "Hval1" as (tr1) "[Htree1 %Hcont1]".
    iDestruct "Hval2" as (tr2) "[Htree2 %Hcont2]".
    simpl in *.
    destruct tr1, tr2; subst; try done.
    - simpl. iDestruct "Htree2" as (?) "[? Htree2]".
      iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
      exfalso. by list_simplifier.
    - simpl. iDestruct "Htree1" as (?) "[? Htree1]".
      iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
      exfalso. by list_simplifier.
    - simpl.
      iDestruct "Htree1" as (?) "[Hchildren1 Htree1]".
      iDestruct "Htree2" as (?) "[Hchildren2 Htree2]".
      iDestruct (is_hash_inj with "[$] [$]") as "%Heq".
      list_simplifier.
      rename H into Heq.
      iClear "Htree1 Htree2".

      iAssert (⌜ child_hashes0 = child_hashes ⌝)%I with "[-]" as %->.
      {
        iApply pure_mono.
        { by pose proof (and_ind (and_ind (concat_len_eq (32%nat) _ _ Heq))). }
        iSplit.
        2:{ word. }
        iSplit.
        - rewrite Forall_forall.
          iIntros (hash Helem_of).
          clear a Hcont1 Hcont2.
          apply elem_of_list_lookup_1 in Helem_of as [a Hlookup].
          iClear "Hchildren1".
          iDestruct (big_sepL2_lookup_2_some _ _ _ a with "Hchildren2") as %[? Hlookup'].
          { done. }
          apply list_lookup_fmap_Some in Hlookup' as (? & Hlookup' & ->).
          iDestruct (big_sepL2_lookup _ _ _ a with "Hchildren2") as "H".
          { rewrite list_lookup_fmap Hlookup' //. }
          { done. }
          simpl.
          destruct x0.
          { by iApply node_hash_len. }
          { by iApply is_hash_len. }
        - rewrite Forall_forall.
          iIntros (hash Helem_of).
          clear a Hcont1 Hcont2.
          apply elem_of_list_lookup_1 in Helem_of as [a Hlookup].
          iClear "Hchildren2".
          iDestruct (big_sepL2_lookup_2_some _ _ _ a with "Hchildren1") as %[? Hlookup'].
          { done. }
          apply list_lookup_fmap_Some in Hlookup' as (? & Hlookup' & ->).
          iDestruct (big_sepL2_lookup _ _ _ a with "Hchildren1") as "H".
          { rewrite list_lookup_fmap Hlookup' //. }
          { done. }
          simpl.
          destruct x0.
          { by iApply node_hash_len. }
          { by iApply is_hash_len. }
      }
      destruct (l !! uint.nat a) eqn:Hlookup; [|done].
      destruct (l0 !! uint.nat a) eqn:Hlookup0; [|done].
      iDestruct (big_sepL2_lookup_1_some _ _ _ (uint.nat a) with "Hchildren1") as %[? Hlookup'].
      { rewrite list_lookup_fmap Hlookup //. }
      iDestruct (big_sepL2_lookup_1_some _ _ _ (uint.nat a) with "Hchildren2") as %[? Hlookup0'].
      { rewrite list_lookup_fmap Hlookup0 //. }


      iDestruct (big_sepL2_lookup _ _ _ (uint.nat a) with "Hchildren1") as "Hchild1".
      { rewrite list_lookup_fmap Hlookup //. }
      { done. }
      iDestruct (big_sepL2_lookup _ _ _ (uint.nat a) with "Hchildren2") as "Hchild2".
      { rewrite list_lookup_fmap Hlookup0 //. }
      { done. }
      simpl.
      destruct o, o0; subst.
      + iApply ("IH" with "[Hchild1] [Hchild2]").
        { by iFrame. }
        { by iFrame. }
      + destruct t.
        { simpl in *. destruct id; done. }
        { simpl. iDestruct (is_hash_inj with "[$] [$]") as "%Hbad".
          apply (f_equal last) in Hbad. rewrite last_snoc //= in Hbad. }
        { simpl. iDestruct "Hchild1" as (?) "[? ?]". iDestruct (is_hash_inj with "[$] [$]") as "%Hbad".
          apply (f_equal last) in Hbad. rewrite last_snoc //= in Hbad. }
      + destruct t.
        { simpl in *. destruct id; done. }
        { simpl. iDestruct (is_hash_inj with "[$] [$]") as "%Hbad".
          apply (f_equal last) in Hbad. rewrite last_snoc //= in Hbad. }
        { simpl. iDestruct "Hchild2" as (?) "[? ?]". iDestruct (is_hash_inj with "[$] [$]") as "%Hbad".
          apply (f_equal last) in Hbad. rewrite last_snoc //= in Hbad. }
      + done.
  }
Qed.

End external.

Module pathProof.
Record t :=
  mk {
    id: list w8;
    nodeHash: list w8;
    digest: list w8;
    childHashes: list (list (list w8));
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_id sl_nodeHash sl_digest sl_childHashes,
  "Hid" ∷ own_slice_small sl_id byteT (DfracOwn 1) obj.(id) ∗
  "Hptr_id" ∷ ptr ↦[pathProof :: "id"] (slice_val sl_id) ∗
  "HnodeHash" ∷ own_slice_small sl_nodeHash byteT (DfracOwn 1) obj.(nodeHash) ∗
  "Hptr_nodeHash" ∷ ptr ↦[pathProof :: "nodeHash"] (slice_val sl_nodeHash) ∗
  "Hdigest" ∷ own_slice_small sl_digest byteT (DfracOwn 1) obj.(digest) ∗
  "Hptr_digest" ∷ ptr ↦[pathProof :: "digest"] (slice_val sl_digest) ∗
  "#HchildHashes" ∷ is_Slice3D sl_childHashes obj.(childHashes) ∗
  "Hptr_childHashes" ∷ ptr ↦[pathProof :: "childHashes"] (slice_val sl_childHashes) ∗
  "%Hlen_id_depth" ∷ ⌜length obj.(id) = length obj.(childHashes)⌝ ∗
  "%Hlen_id_ub" ∷ ⌜length obj.(id) ≤ 32⌝.
End local_defs.
End pathProof.

Module GetReply.
Record t :=
  mk {
    Val: list w8;
    Digest: list w8;
    ProofTy: bool;
    Proof: list (list (list w8));
    Error: bool;
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_Val sl_Dig sl_Proof,
  "HVal" ∷ ptr ↦[GetReply :: "val"] (slice_val sl_Val) ∗
  "Hptr_Val" ∷ own_slice_small sl_Val byteT (DfracOwn 1) obj.(Val) ∗
  "HDig" ∷ ptr ↦[GetReply :: "Digest"] (slice_val sl_Dig) ∗
  "Hptr_Dig" ∷ own_slice_small sl_Dig byteT (DfracOwn 1) obj.(Digest) ∗
  "HProofTy" ∷ ptr ↦[GetReply :: "ProofTy"] #obj.(ProofTy) ∗
  "HProof" ∷ ptr ↦[GetReply :: "Proof"] (slice_val sl_Proof) ∗
  "Hsl_Proof" ∷ is_Slice3D sl_Proof obj.(Proof) ∗
  "HErr" ∷ ptr ↦[GetReply :: "Error"] #obj.(Error).
End local_defs.
End GetReply.

Section wps.
Context `{!heapGS Σ}.

Lemma wp_Tree_Digest ptr_tr entries :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries
  }}}
  Tree__Digest #ptr_tr
  {{{
    sl_dig dig, RET (slice_val sl_dig);
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "Hdig" ∷ own_slice_small sl_dig byteT (DfracOwn 1) dig ∗
    "#HisDig" ∷ is_dig entries dig
  }}}.
Proof. Admitted.


Lemma newNode_eq_empty :
  eq_tree_map (Interior (replicate (uint.nat 256) None)) ∅.
Proof.
  intros ?. destruct k.
  { done. }
  { simpl. rewrite lookup_replicate_2; [done|word]. }
Qed.

Lemma wp_Tree_Put ptr_tr entries sl_id id sl_val val d0 d1 :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val
  }}}
  Tree__Put #ptr_tr (slice_val sl_id) (slice_val sl_val)
  {{{
    sl_dig sl_proof (err : bool),
    RET ((slice_val sl_dig), (slice_val sl_proof), #err);
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "%Hvalid_id" ∷ ⌜ length id = hash_len → err = false ⌝ ∗
    "Herr" ∷
      if negb err then
        ∃ dig proof,
        "Htree" ∷ own_merkle ptr_tr (<[id:=val]>entries) ∗
        "Hdig" ∷ own_slice_small sl_dig byteT (DfracOwn 1) dig ∗
        "#HisDig" ∷ is_dig (<[id:=val]>entries) dig ∗
        "Hproof" ∷ is_Slice3D sl_proof proof
      else
        "Htree" ∷ own_merkle ptr_tr entries
  }}}.
Proof.
  iIntros (?) "H HΦ". iNamed "H".
  wp_rec.
  wp_pures.
  iDestruct (own_slice_small_sz with "Hid") as %Hsz_id.
  wp_apply wp_slice_len.
  wp_pures.
  wp_if_destruct.
  { (* return an error. *)
    wp_pures.
    replace (slice.nil) with (slice_val Slice.nil) by done.
    iApply "HΦ".
    iModIntro. iFrame. iPureIntro.
    word.
  }
  wp_rec.
  wp_pures.
  iNamed "Htree".
  wp_loadField.
  wp_pures.

  (* weaken to loop invariant. *)

  wp_bind (if: _ then _ else _)%E.
  wp_apply (wp_wand _ _ _ (λ _,
                             ∃ (root : loc) tr,
                               "Hroot" ∷ ptr_tr ↦[Tree::"root"] #root ∗
                               "Hnode" ∷ own_node_except (Some id) root tr ∗
                               "%Htree" ∷ ⌜ eq_tree_map tr entries ⌝ ∗
                               "%Hheight" ∷ ⌜ has_tree_height tr (uint.nat full_height) ⌝
              )%I
             with "[Hnode Hroot]").
  {
    wp_if_destruct.
    2:{
      iModIntro. iFrame "∗%".
      rewrite decide_False //.
      iDestruct (own_node_except_mono (Some id) with "[$]") as "$"; done.
    }
    wp_rec.
    wp_apply wp_NewSlice.
    iIntros (?) "Hsl".
    iDestruct (own_slice_to_small with "[$]") as "Hsl".
    wp_pures. wp_apply wp_allocStruct.
    { val_ty. }

    iDestruct "Hnode" as %->.
    iIntros (?) "Hnode".
    wp_storeField.
    iDestruct (struct_fields_split with "Hnode") as "H".
    iNamed "H".
    iExists _, (Interior (replicate (uint.nat (W64 256)) None)).
    iFrame.
    iSplitL.
    2:{
      (* XXX: could have lemmas for stuff like this *)
      iPureIntro. split.
      - (* tree still matches empty map *)
        apply newNode_eq_empty.
      - (* tree respects has_tree_height *)
        rewrite /has_tree_height /=.
        destruct (uint.nat full_height) eqn:H.
        { exfalso. done. }
        clear H.
        by apply Forall_replicate.
    }
    iApply own_node_except_unfold .
    rewrite zero_slice_val.
    iFrame.
    iExists [], [].
    iDestruct (own_slice_small_nil) as "$".
    { done. }
    iSplitR; first done.
    iSplitR; first done.
    iApply big_sepL2_replicate_r.
    { rewrite length_replicate //. }
    iApply big_sepL_impl.
    { by iApply big_sepL_emp. }
    iModIntro. iIntros.
    apply lookup_replicate in H as [-> ?]. done.
  }
  iIntros (?) "HifInv".
  wp_pures. clear v.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (nodePath_ptr) "HnodePath_ptr".
  wp_pures.
  clear tr root Htree Hheight.
  iNamed "HifInv".
  wp_loadField.
  wp_load.
  rewrite zero_slice_val.
  wp_apply (wp_SliceAppend (V:=loc) with "[]").
  { iApply own_slice_zero. }
  iIntros (?) "HnodePath".
  simpl.
  wp_store.
  wp_apply wp_ref_to.
  { val_ty. }
  iIntros (pathIdx_ptr) "HpathIdx".
  wp_pures.
  set (loopInv :=
         (λ (i : w64),
            ∃ (currNode_ptr : loc) sub_tree sub_map nodePath_sl (nodePath : list loc),
              "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
              "HnodePath_ptr" ∷ nodePath_ptr ↦[slice.T ptrT] (slice_val nodePath_sl) ∗
              "HnodePath" ∷ own_slice nodePath_sl ptrT (DfracOwn 1) nodePath ∗

              "%HnodePath_last" ∷ ⌜ last nodePath = Some currNode_ptr ⌝ ∗
              "Hnode" ∷ own_node_except (Some (drop (uint.nat i) id)) currNode_ptr sub_tree ∗
              "%HnodePath_length" ∷ ⌜ length nodePath = S (uint.nat i) ⌝ ∗
              "%Hsubmap" ∷ ⌜ eq_tree_map sub_tree sub_map ⌝ ∗
              "%Hheight" ∷ ⌜ has_tree_height sub_tree (uint.nat full_height - uint.nat i)%nat ⌝ ∗
              "Hrest" ∷ (∀ sub_tree' ,
                           ⌜ eq_tree_map sub_tree' (<[id := val]> sub_map) ⌝ -∗
                           ⌜ has_tree_height sub_tree (uint.nat full_height - uint.nat i)%nat ⌝ -∗
                           own_node_except (Some (drop (uint.nat i) id)) currNode_ptr sub_tree' -∗
                           ∃ tr', own_node_except (Some id) currNode_ptr tr' ∗
                                  ⌜ eq_tree_map tr' (<[id := val]> entries) ⌝ ∗
                                  ⌜ has_tree_height sub_tree (uint.nat full_height) ⌝)
         )%I).
  wp_apply (wp_forUpto' loopInv with "[$HpathIdx Hid Hnode HnodePath_ptr HnodePath]").
  {
    iSplitR; first word.
    iFrame. repeat iExists _. iSplitR; first done.
    iSplitR; first done. iSplitR; first done.
    iSplitR; first done.
    iIntros (?). iIntros.
    iExists _; iFrame. done.
  }
  { (* one loop iteration *)
    clear Φ Hheight Htree.
    iIntros "!# * (H & HpathIdx & %Hlt) HΦ'".
    iNamed "H".
    wp_pures. wp_load. wp_load.
    iDestruct (own_slice_split_1 with "HnodePath") as "[HnodePath HnodePath_cap]".
    wp_apply (wp_SliceGet with "[$HnodePath]").
    {
      iPureIntro.
      rewrite last_lookup in HnodePath_last.
      rewrite HnodePath_length /= in HnodePath_last.
      done.
    }
    iIntros "HnodePath".
    wp_pures.
    wp_load.
    opose proof (list_lookup_lt id (uint.nat i) ltac:(word)) as [pos H].
    wp_apply (wp_SliceGet with "[$Hid //]").
    iIntros "Hid".
    wp_pures.
    iDestruct (own_node_except_unfold with "Hnode") as "Hnode".
    iNamed "Hnode".
    wp_loadField.

    destruct (uint.nat full_height - uint.nat i)%nat eqn:Hdepth.
    { exfalso. unfold full_height in Hdepth. word. }
    destruct sub_tree as [| |children].
    { by iExFalso. }
    { simpl in Hheight. exfalso. subst. word. }
    opose proof (list_lookup_lt ptr_children (uint.nat pos) ltac:(word)) as [ptr_child Hptr_child].

    wp_apply (wp_SliceGet with "[$Hsl_children]").
    { iPureIntro. instantiate (1:=ptr_child). rewrite -Hptr_child. f_equal.
      word. }
    iIntros "Hsl_children".
    wp_pures.
    wp_if_destruct.
    { (* child was null *)
      wp_rec.
      wp_apply wp_NewSlice.
      iIntros (?) "Hsl".
      iDestruct (own_slice_to_small with "[$]") as "Hsl".
      wp_pures. wp_apply wp_allocStruct.
      { val_ty. }

      iIntros (?) "HchildNode".
      wp_loadField.
      wp_apply (wp_SliceSet with "[$Hsl_children]").
      { replace (uint.nat (W64 (uint.Z pos))) with (uint.nat pos) by word. done. }
      iIntros "Hsl_children".
      wp_pures.
      wp_loadField.
      wp_apply (wp_SliceGet with "[$Hsl_children]").
      { iPureIntro. rewrite list_lookup_insert; [done|word]. }
      iIntros "Hsl_children".
      wp_load.
      iDestruct (own_slice_split with "[$HnodePath $HnodePath_cap]") as "HnodePath".
      wp_apply (wp_SliceAppend (V:=loc) with "[$]").
      iIntros (newNodePath_sl) "HnodePath".
      wp_store.
      clear nodePath_sl.
      iApply "HΦ'".
      iFrame "HpathIdx".
      iModIntro.
      repeat iExists _.
      iFrame.
      iSplitR.
      { rewrite last_snoc //. }
      iSplitL "HchildNode Hsl".
      {
        iApply own_node_except_unfold.
        repeat iExists _.
        iDestruct (struct_fields_split with "HchildNode") as "H".
        iNamed "H".
        rewrite zero_slice_val.
        iFrame.
        iDestruct (own_slice_small_nil) as "$"; first done.
        iSplitR; first done.
        iSplitR; first done.
        instantiate (1:=Interior (replicate _ None)).
        simpl.
        iApply big_sepL2_replicate_r.
        { rewrite length_replicate //. }
        iApply big_sepL_impl.
        { by iApply big_sepL_emp. }
        iModIntro. iIntros.
        apply lookup_replicate in H0 as [-> ?]. done.
      }
      repeat (iSplitR; try iPureIntro).
      { rewrite length_app /=. word. }
      { rewrite Hchildren_len. apply newNode_eq_empty. }
      { (* FIXME: don't want to always make the new node an Interior; at the
           very end, it should be a leaf node. *)
        admit.
      }
      admit.
    }
Admitted.

Lemma wp_Tree_Get ptr_tr entries sl_id id d0 :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id
  }}}
  Tree__Get #ptr_tr (slice_val sl_id)
  {{{
    ptr_reply reply, RET #ptr_reply;
    "Hreply" ∷ GetReply.own ptr_reply reply ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "%Hvalid_id" ∷ ⌜ length id = hash_len → reply.(GetReply.Error) = false ⌝ ∗
    "Herr" ∷
      if negb reply.(GetReply.Error) then
        "Htree" ∷ own_merkle ptr_tr (<[id:=reply.(GetReply.Val)]>entries) ∗
        "#HisDig" ∷ is_dig (<[id:=reply.(GetReply.Val)]>entries) reply.(GetReply.Digest)
      else
        "Htree" ∷ own_merkle ptr_tr entries
  }}}.
Proof. Admitted.

Lemma wp_Tree_DeepCopy ptr_tr entries :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries
  }}}
  Tree__DeepCopy #ptr_tr
  {{{
    ptr_new, RET #ptr_new;
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "HnewTree" ∷ own_merkle ptr_new entries
  }}}.
Proof. Admitted.

Lemma wp_isValidHashSl sl_data data :
  {{{
    "#Hdata" ∷ is_Slice2D sl_data data
  }}}
  isValidHashSl (slice_val sl_data)
  {{{
    (ok : bool), RET #ok;
    if bool_decide ok then
      "%Hlen" ∷ ([∗ list] l ∈ data, ⌜length l = 32%nat⌝)
    else True%I
  }}}.
Proof. Admitted.

(*
Lemma wp_pathProof_check ptr_proof proof val :
  {{{
    "Hproof" ∷ pathProof.own ptr_proof proof ∗
    let node := match val with
    | None => Empty
    | Some val' => Leaf val'
    end in
    "Hhash" ∷ is_node_hash node proof.(pathProof.nodeHash)
  }}}
  pathProof__check #ptr_proof
  {{{
    (err : bool), RET #err;
    if negb err then
      "Hpath" ∷ is_merkle_entry proof.(pathProof.id) val proof.(pathProof.digest)
    else True%I
  }}}.
Proof.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hproof".
  rewrite /pathProof__check.
  wp_apply wp_ref_to; [val_ty|];
    iIntros (ptr_err) "Hptr_err".
  wp_loadField.
  wp_apply wp_ref_to; [val_ty|]. iIntros (ptr_currHash) "HcurrHash".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_apply wp_ref_to; [val_ty|]; iIntros (ptr_loopIdx) "HloopIdx".
  iDestruct ("HchildHashes") as (?) "H"; iNamed "H".
  iMod (own_slice_small_persist with "HnodeHash") as "#HnodeHash".
  iDestruct (big_sepL2_length with "Hsep_dim0") as "%Hlen_childHashes".
  iDestruct (own_slice_small_sz with "Hsl_dim0") as "%Hlen_list_dim0".

  (* Entering the main loop. *)
  set for_inv :=
    (λ loopIdx, ∃ sl_currHash currHash (err : bool),
      "Hid" ∷ own_slice_small sl_id byteT (DfracOwn 1) proof.(pathProof.id) ∗
      "Hptr_id" ∷ ptr_proof ↦[pathProof :: "id"] sl_id ∗
      "Hptr_childHashes" ∷ ptr_proof ↦[pathProof :: "childHashes"] sl_childHashes ∗
      "#Hsl_currHash" ∷ own_slice_small sl_currHash byteT DfracDiscarded currHash ∗
      "Hptr_currHash" ∷ ptr_currHash ↦[slice.T byteT] sl_currHash ∗
      "Hptr_err" ∷ ptr_err ↦[boolT] #err ∗
      "Herr_pred" ∷ if negb err then
        "Hpath_val" ∷ is_merkle_entry
          (drop (length proof.(pathProof.id) - (Z.to_nat (word.unsigned loopIdx)))
          proof.(pathProof.id)) val currHash
      else True)%I : w64 → iProp Σ.
  wp_apply (wp_forUpto for_inv with "[] [$Hid $Hptr_id $Hptr_childHashes $HloopIdx $HcurrHash $HnodeHash $Hptr_err Hhash]"); [word|..].
  2: {
    assert ((length proof.(pathProof.id) - 0%nat)%nat = length proof.(pathProof.id)) as H by word;
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
    wp_apply (wp_loadField with "[$Hptr_childHashes]");
      iIntros "Hptr_childHashes".

    (* Note: move all the sep fetches into one block, like this. *)
    (* TODO: change all uint out of backwords compat thing *)
    assert (∃ (sl_dim1' : Slice.t),
      list_dim0 !! uint.nat (length list_dim0 - 1 - uint.nat loopIdx) =
      Some sl_dim1') as [sl_dim1' Hlook_sl_dim1'].
    { apply lookup_lt_is_Some. word. }
    iDestruct (big_sepL2_lookup_1_some with "Hsep_dim0") as %[obj_dim1' Hlook_obj_dim1']; [done|].
    iDestruct (big_sepL2_lookup with "Hsep_dim0") as (list_dim1') "H";
      [done..|]; iNamed "H".
    iDestruct (own_slice_small_sz with "Hsl_dim1") as "%Hlen_list_dim1'".
    iDestruct (big_sepL2_length with "Hsep_dim1") as "%Hlen_obj_dim1'".
    iDestruct (own_slice_small_sz with "Hid") as "%Hlen_id".

    (* Rewrite this early since it appears in multiple sub-terms. *)
    replace (word.sub (word.sub sl_childHashes.(Slice.sz) 1) loopIdx) with
      (W64 (length list_dim0 - 1 - uint.nat loopIdx)) by word.

    wp_apply (wp_SliceGet with "[$Hsl_dim0]"); [done|]; iIntros "_".
    wp_apply wp_slice_len.

    wp_if_destruct.
    { wp_store. iApply "HΦ2". by iFrame "#∗". }
    replace (word.sub 256 1) with (W64 255) in Heqb;
      [|word]; rename Heqb into Hsz_sl_dim1'.
    wp_apply (wp_isValidHashSl with "[$Hsl_dim1 $Hsep_dim1]").
      iIntros (ok) "H".
    wp_if_destruct.
    { wp_store. iApply "HΦ2". by iFrame "#∗". }
    iSimpl in "H"; iNamed "H"; rename Hlen into Hhash_len_obj_dim1'.

    wp_apply (wp_loadField with "[$Hptr_id]");
      iIntros "Hptr_id".
    assert (∃ (pos : w8),
      proof.(pathProof.id) !! uint.nat (length list_dim0 - 1 - uint.nat loopIdx) =
      Some pos) as [pos Hlook_pos].
    { apply lookup_lt_is_Some. word. }
    wp_apply (wp_SliceGet with "[$Hid]"); [done|];
      iIntros "Hid".

    (* TODO: word should know this. *)
    assert (length list_dim1' = 255%nat) as H255_list_dim1'.
    { rewrite Hlen_list_dim1'. rewrite Hsz_sl_dim1'. word. }
    (* Note: this slows down word for some reason. *)
    pose proof (word.unsigned_range pos) as Hpos_bound.

    (* The complicated slice splitting logic. *)
    iDestruct (own_slice_small_wf with "Hsl_dim1") as "%Hwf_sl_dim1".
    iDestruct (slice_small_split _ (W64 (word.unsigned pos)) with "Hsl_dim1") as "[Hsl_before Hsl_after]".
    (* TODO: word should know this. *)
    { rewrite u8_to_u64_Z. lia. }
    wp_apply wp_SliceTake.
    { rewrite u8_to_u64_Z. lia. }
    wp_apply wp_SliceSkip.
    { rewrite u8_to_u64_Z. lia. }
    iEval (rewrite u8_to_u64_Z) in "Hsl_before".
    iEval (rewrite u8_to_u64_Z) in "Hsl_after".

    wp_apply wp_ref_of_zero; [done|];
      iIntros (ptr_hr) "Hptr_hr".
    iEval (rewrite zero_slice_val) in "Hptr_hr".
    iDestruct (own_slice_small_nil byteT (DfracOwn 1) (Slice.nil)) as "Hnil"; [done|].
    wp_apply (wp_HasherWriteSl with "[$Hptr_hr $Hnil $Hsl_before]").
    {
      iApply big_sepL2_prefix.
      4: iFrame "#".
      1: apply prefix_take.
      1: apply (prefix_take _ (uint.nat pos)).
      { do 2 rewrite length_take. lia. }
    }
    iIntros (sl_hr) "H"; iNamed "H".
    wp_load.
    wp_apply (wp_HasherWrite with "[$Hptr_hr $Hhr $Hsl_currHash]");
      clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_apply (wp_HasherWriteSl with "[$Hptr_hr $Hhr $Hsl_after]").
    {
      iApply big_sepL2_suffix.
      4: iFrame "#".
      1: apply suffix_drop.
      1: apply (suffix_drop _ (uint.nat pos)) .
      { do 2 rewrite length_drop. lia. }
    }
    clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_apply wp_SliceSingleton; [val_ty|];
      iIntros (sl_tag) "H";
      iDestruct (slice.own_slice_to_small with "H") as "Hsl_tag".
    iAssert (own_slice_small _ _ _ [W8 2]) with "Hsl_tag" as "Hsl_tag".
    iMod (own_slice_small_persist with "Hsl_tag") as "#Hsl_tag".
    wp_apply (wp_HasherWrite with "[$Hptr_hr $Hhr $Hsl_tag]").
    clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_load.
    wp_apply (wp_HasherSumNil with "Hhr");
      iIntros (sl_hash hash) "H"; iNamed "H".
    wp_store.
    iMod (own_slice_small_persist with "Hsl_hash") as "#Hsl_hash".
    iClear (sl_tag) "HnodeHash Hsl_before Hsl_after Hnil Hsl_tag".

    (* Done with code, now re-establish loop inv. *)

    destruct err; iNamed "Herr_pred"; iApply "HΦ2"; iFrame "#∗"; [done|].
    rewrite /is_merkle_entry.
    iDestruct "Herr_pred" as "[Htr_hash %Htr_contains]".
    iExists (Interior (
      ((λ h, Cut h) <$> (take (uint.nat pos) obj_dim1')) ++
      [tr] ++
      ((λ h, Cut h) <$> (drop (uint.nat pos) obj_dim1')))).
    iIntros "!>".
    iSplit.
    {
      iExists (
        (take (uint.nat pos) obj_dim1') ++
        [currHash] ++
        (drop (uint.nat pos) obj_dim1')).
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
    replace (S (length proof.(pathProof.id) - uint.nat (word.add loopIdx 1))) with
      ((length proof.(pathProof.id) - uint.nat loopIdx)%nat) by word.
    exists tr.
    split; [|done].
    rewrite (lookup_app_r _ _ _ _).
    2: {
      rewrite length_fmap.
      rewrite (length_take_le _ _ _); [done|].
      pose proof (word.unsigned_range pos) as Hpos_bound.
      lia.
    }
    rewrite length_fmap.
    rewrite (length_take_le _ _ _).
    2: { pose proof (word.unsigned_range pos) as Hpos_bound. lia. }
    replace ((uint.nat pos - uint.nat pos)%nat) with (0%nat) by lia.
    naive_solver.
  }

  (* Last chunk of code after for loop. *)
  iEval (rewrite /for_inv); clear for_inv.
  iIntros "[H _]"; iNamed "H".
  wp_load.
  wp_if_destruct; [by iApply "HΦ"|]; clear err Heqb.
  iSimpl in "Herr_pred"; iNamed "Herr_pred".
  wp_apply (wp_loadField with "Hptr_digest");
    iIntros "Hptr_digest".
  wp_load.
  (* TODO: framing doesn't work here. $Hsl_currHash frames this persis thing twice. *)
  wp_apply (wp_BytesEqual with "[Hdigest]"); [iFrame "#∗"|];
    iIntros "[_ Hdigest]".
  wp_if_destruct; [by iApply "HΦ"|]; rename Heqb into Heq_currHash.
  iEval (replace ((length proof.(pathProof.id) - uint.nat sl_childHashes.(Slice.sz))%nat)
    with (0%nat) by word) in "Hpath_val".
  iEval (rewrite drop_0 Heq_currHash) in "Hpath_val".
  by iApply "HΦ".
Qed. *)

(* is_merkle_proof says that the merkle proof gives rise to a cut tree
that has digest dig. and is_merkle_entry id val dig.
the cut tree is the existential tree in is_merkle_entry. *)
Definition is_merkle_proof (proof : list (list (list w8))) (id : list w8)
    (val : option (list w8)) (dig : list w8) : iProp Σ.
Proof. Admitted.

Global Instance is_merkle_proof_persis proof id val dig :
  Persistent (is_merkle_proof proof id val dig).
Proof. Admitted.

Lemma is_merkle_proof_to_entry proof id val dig :
  is_merkle_proof proof id val dig -∗ is_merkle_entry id val dig.
Proof. Admitted.

Definition wp_CheckProof sl_id sl_val sl_dig (proofTy : bool) sl_proof proof (id val dig : list w8) d0 d1 d2 :
  {{{
    "#Hsl_proof" ∷ is_Slice3D sl_proof proof ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val ∗
    "Hdig" ∷ own_slice_small sl_dig byteT d2 dig
  }}}
  CheckProof #proofTy (slice_val sl_proof) (slice_val sl_id) (slice_val sl_val) (slice_val sl_dig)
  {{{
    (err : bool), RET #err;
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val ∗
    "Hdig" ∷ own_slice_small sl_dig byteT d2 dig ∗
    let expected_val := (if proofTy then Some val else None) in
    "Hgenie" ∷ (is_merkle_proof proof id expected_val dig ∗-∗ ⌜ err = false ⌝)
  }}}.
Proof. Admitted.

End wps.
