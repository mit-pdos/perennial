From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import merkle.

From Perennial.program_proof.pav Require Import misc cryptoffi cryptoutil.
From Perennial.program_proof Require Import std_proof.

Section internal.
Context `{!heapGS Σ}.

Inductive tree : Type :=
  (* Cut only exists for proof checking trees. *)
  | Cut : list w8 → tree
  | Empty : tree
  | Leaf : list w8 → tree
  | Interior : list tree → tree.

Fixpoint has_entry (tr : tree) (id : list w8) (node : tree) : Prop :=
  match tr with
  | Cut _ => False
  | Empty => id = [] ∧ tr = node
  | Leaf val => id = [] ∧ tr = node
  | Interior children =>
    match id with
    | [] => False
    | pos :: rest =>
      ∃ child, children !! Z.to_nat (word.unsigned pos) = Some child ∧ has_entry child rest node
    end
  end.

(* The core invariant that defines the recursive hashing structure of merkle trees. *)
Fixpoint is_node_hash (tr : tree) (hash : list w8) : iProp Σ :=
  match tr with
  | Cut hash' => ⌜hash = hash' ∧ length hash' = 32%nat⌝
  | Empty => is_hash [W8 0] hash
  | Leaf val => is_hash (val ++ [W8 1]) hash
  | Interior children =>
    ∃ (child_hashes : list (list w8)),
    let map_fn := (λ c h, is_node_hash c h) in
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
  1-2: iDestruct (is_hash_len with "Htree") as "%Hlen"; naive_solver.
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

(* TODO: is this necessary? can we just apply node_hash_len when necessary? *)
Lemma sep_node_hash_len ct ch :
  ([∗ list] t;h ∈ ct;ch, is_node_hash t h) -∗
  ⌜Forall (λ l, length l = 32%nat) ch⌝.
Proof.
  iIntros "Htree".
  iDestruct (big_sepL2_impl _ (λ _ _ h, ⌜length h = 32%nat⌝%I) with "Htree []") as "Hlen_sepL2".
  {
    iIntros "!>" (???) "_ _ Hhash".
    by iDestruct (node_hash_len with "Hhash") as "Hlen".
  }
  iDestruct (big_sepL2_const_sepL_r with "Hlen_sepL2") as "[_ %Hlen_sepL1]".
  iPureIntro.
  by apply Forall_lookup.
Qed.

Lemma disj_empty_leaf digest v :
  is_node_hash Empty digest -∗
  is_node_hash (Leaf v) digest -∗
  False.
Proof.
  iIntros "Hempty Hleaf".
  iDestruct (is_hash_inj with "Hempty Hleaf") as "%Heq".
  iPureIntro.
  destruct v as [|a]; [naive_solver|].
  (* TODO: why doesn't list_simplifier or solve_length take care of this? *)
  apply (f_equal length) in Heq.
  rewrite length_app in Heq.
  simpl in *.
  lia.
Qed.

(* Ownership of a logical merkle tree. *)
Definition own_node' (recur : loc -d> tree -d> iPropO Σ) : loc -d> tree -d> iPropO Σ :=
  (λ ptr_tr tr,
    match tr with
    (* We should never have cuts in in-memory trees. *)
    | Cut _ => False
    | Empty =>
      ∃ hash,
      "#His_hash" ∷ is_node_hash tr hash ∗
      "%Hnil" ∷ ⌜ptr_tr = null⌝
    | Leaf val =>
      ∃ sl_val hash sl_hash,
      "Hval" ∷ own_slice_small sl_val byteT (DfracOwn 1) val ∗
      "Hptr_val" ∷ ptr_tr ↦[node :: "Val"] (slice_val sl_val) ∗
      "#His_hash" ∷ is_node_hash tr hash ∗
      "Hhash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
      "Hsl_hash" ∷ ptr_tr ↦[node :: "hash"] (slice_val sl_hash)
    | Interior children =>
      ∃ hash sl_hash sl_children ptr_children,
      "#His_hash" ∷ is_node_hash tr hash ∗
      "Hhash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
      "Hsl_children" ∷ own_slice_small sl_children ptrT (DfracOwn 1) ptr_children ∗
      "Hptr_children" ∷ ptr_tr ↦[node :: "Children"] (slice_val sl_children) ∗
      "Hchildren" ∷
        ([∗ list] child;ptr_child ∈ children;ptr_children,
          ▷ recur ptr_child child)
    end)%I.

Local Instance own_node'_contractive : Contractive own_node'.
Proof. solve_contractive. Qed.

Definition own_node : loc → tree → iProp Σ := fixpoint own_node'.

Lemma own_node_unfold ptr obj :
  own_node ptr obj ⊣⊢ (own_node' own_node) ptr obj.
Proof.
  apply (fixpoint_unfold own_node').
Qed.

Definition tree_to_map (tr : tree) : gmap (list w8) (list w8) :=
  let fix traverse (tr : tree) (acc : gmap (list w8) (list w8)) (id : list w8) :=
    match tr with
    | Cut _ => acc
    | Empty => acc
    | Leaf val => <[id:=val]>acc
    | Interior children =>
      (* Grab all entries from the children, storing the ongoing id. *)
      (foldr
        (λ child (pIdxAcc:(Z * gmap (list w8) (list w8))),
          let acc' := traverse child pIdxAcc.2 (id ++ [W8 pIdxAcc.1])
          in (pIdxAcc.1 + 1, acc'))
        (0, acc) children
      ).2
    end
  in traverse tr ∅ [].

End internal.
