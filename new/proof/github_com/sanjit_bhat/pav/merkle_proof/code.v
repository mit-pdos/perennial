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
    "Hstruct" ∷ ptr ↦{d}
      (merkle.node.mk leafNodeTy sl_hash null null sl_label sl_val) ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash ∗
    "#Hsl_label" ∷ sl_label ↦*□ label ∗
    "#Hsl_val" ∷ sl_val ↦*□ val
  | Inner child0 child1 =>
    ∃ sl_hash ptr_child0 ptr_child1,
    "Hstruct" ∷ ptr ↦{d}
      (merkle.node.mk innerNodeTy sl_hash ptr_child0 ptr_child1 slice.nil slice.nil) ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash ∗
    "Hown_child0" ∷ own_tree ptr_child0 child0 d ∗
    "Hown_child1" ∷ own_tree ptr_child1 child1 d ∗
    "%Heq_children" ∷ ⌜ ptr_child0 ≠ null ∨ ptr_child1 ≠ null ⌝
  | Cut _ =>
    ∃ sl_hash,
    "Hstruct" ∷ ptr ↦{d}
      (merkle.node.mk cutNodeTy sl_hash null null slice.nil slice.nil) ∗
    "#Hsl_hash" ∷ sl_hash ↦*□ hash
  end.

Definition own ptr m d : iProp Σ :=
  ∃ ptr_root t,
  "Hstruct" ∷ ptr ↦{d} (merkle.Map.mk ptr_root) ∗
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
    (iDestruct (typed_pointsto_not_null with "Hstruct") as %?; [|done]);
    by rewrite go_type_size_unseal.
Qed.

(** program proofs. *)

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
