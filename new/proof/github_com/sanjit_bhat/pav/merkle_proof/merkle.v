From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import merkle.
From Perennial.Helpers Require Import bytes NamedProps.

From New.proof.github_com.goose_lang Require Import primitive std.
From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi cryptoutil safemarshal.
From New.proof.github_com.tchajed Require Import marshal.

From New.proof.github_com.sanjit_bhat.pav.merkle_proof Require Import base serde theory.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.
Context `{!merkle.GlobalAddrs}.

(** ownership preds. *)

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

Fixpoint own_tree ptr t d : iProp Σ :=
  ∃ hash,
  "#Htree_hash" ∷ is_cut_tree t hash ∗
  match t with
  | Empty =>
    "%Heq_ptr" ∷ ⌜ ptr = null ⌝
  | Leaf label val =>
    ∃ sl_hash sl_label sl_val,
    "Hstruct" ∷ ptr ↦{d}
      (merkle.node.mk leafNodeTy sl_hash null null sl_label sl_val) ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_val" ∷ sl_val ↦*□ val
  | Cut _ =>
    ∃ sl_hash,
    "Hstruct" ∷ ptr ↦{d}
      (merkle.node.mk cutNodeTy sl_hash null null slice.nil slice.nil) ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash
  | Inner child0 child1 =>
    ∃ sl_hash ptr_child0 ptr_child1,
    "Hstruct" ∷ ptr ↦{d}
      (merkle.node.mk innerNodeTy sl_hash ptr_child0 ptr_child1 slice.nil slice.nil) ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash ∗
    "Hown_child0" ∷ own_tree ptr_child0 child0 d ∗
    "Hown_child1" ∷ own_tree ptr_child1 child1 d ∗
    "%Heq_children" ∷ ⌜ ptr_child0 ≠ null ∨ ptr_child1 ≠ null ⌝
  end.

Global Instance own_tree_dfractional ptr t :
  DFractional (λ d, own_tree ptr t d).
Proof. Admitted.

Global Instance own_tree_as_dfractional ptr t d :
  AsDFractional (own_tree ptr t d) (λ d, own_tree ptr t d) d.
Proof. Admitted.

Definition own_map_aux ptr m depth d : iProp Σ :=
  ∃ t,
  "%Heq_tree_map" ∷ ⌜ m = tree_to_map t ⌝ ∗
  "%Hsorted" ∷ ⌜ sorted_tree t depth ⌝ ∗
  "%Hminimal" ∷ ⌜ minimal_tree t ⌝ ∗
  "%Hcutless" ∷ ⌜ cutless_tree t ⌝ ∗
  "Hown_tree" ∷ own_tree ptr t d.

Definition own_map ptr m d : iProp Σ :=
  own_map_aux ptr m (W64 0) d.

Lemma own_map_to_is_map ptr m d:
  own_map ptr m d -∗
  ∃ h,
  is_map m h.
Proof.
  iNamed 1. destruct t;
    iNamed "Hown_tree"; [..|done]; iFrame "%#".
Qed.

Lemma own_empty_tree t d :
  own_tree null t d -∗
  ⌜ t = Empty ⌝.
Proof.
  iIntros "H". destruct t; [done|..];
    iNamed "H"; iNamed "H".
  all:
    iDestruct (typed_pointsto_not_null with "Hstruct") as %?; [|done];
    by rewrite go_type_size_unseal.
Qed.

Lemma own_map_not_nil ptr elems depth d :
  elems ≠ ∅ →
  own_map_aux ptr elems depth d -∗
  ⌜ ptr ≠ null ⌝.
Proof.
  intros ?. iNamed 1.
  destruct t; [done|..]; iNamed "Hown_tree"; iNamed "Hown_tree".
  all:
    iDestruct (typed_pointsto_not_null with "Hstruct") as %?; [|done];
    by rewrite go_type_size_unseal.
Qed.

Lemma own_tree_to_hash ptr t d :
  own_tree ptr t d -∗
  ∃ dig, is_cut_tree t dig.
Proof. destruct t; iNamed 1; iFrame "#". Qed.

Definition own_Tree ptr elems d : iProp Σ :=
  ∃ ptr_root,
  "Hstruct" ∷ ptr ↦{d} (merkle.Tree.mk ptr_root) ∗
  "Hown_map" ∷ own_map ptr_root elems d.

(** relation bw [is_full_tree] and [is_cut_tree]. *)

Fixpoint get_depth t : nat :=
  match t with
  | Inner c0 c1 => S (get_depth c0 `max` get_depth c1)
  | _ => 0%nat
  end.

Lemma cut_path_is_full_path t0 t1 h label found :
  is_cut_tree (Σ:=Σ) t0 h -∗
  ⌜ tree_path t0 label (W64 0) found ⌝ -∗
  is_full_tree t1 h (get_depth t0) -∗
  ⌜ tree_path t1 label (W64 0) found ⌝.
Proof. Admitted.

(** program proofs. *)

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

End proof.
