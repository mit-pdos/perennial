From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat.merkle Require Import merkle_shim.
From Goose.github_com.mit_pdos.secure_chat Require Import merkle.

From Perennial.program_proof.chat.merkle Require Import shim.

Module Id.
Record t :=
  mk {
    B: list u8;
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr arg : iProp Σ :=
  ∃ sl_B,
  "HB" ∷ own_slice_small sl_B byteT 1 arg.(B) ∗
  "Hptr_B" ∷ ptr ↦[Id :: "B"] (slice_val sl_B).
End local_defs.
End Id.

Module Val.
Record t :=
  mk {
    B: list u8;
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr arg : iProp Σ :=
  ∃ sl_B,
  "HB" ∷ own_slice_small sl_B byteT 1 arg.(B) ∗
  "Hptr_B" ∷ ptr ↦[Id :: "B"] (slice_val sl_B).
End local_defs.

Definition encodesF (arg:t) : list u8 :=
  arg.(B).
End Val.

Section tree.
Context `{!heapGS Σ}.

(* TODO: will need to carry some invariant that the # of children == 256. *)
Inductive tree : Type :=
  | Leaf : list u8 → tree
  | Interior : list (option tree) → tree.

Definition tree_to_map (t : tree) : gmap (list u8) (list u8) :=
  let fix traverse (t : tree) (acc : gmap (list u8) (list u8)) (path : list u8) :=
    match t with
    | Leaf val => <[path:=val]>acc
    | Interior children =>
      (* Grab all entries from the children, storing the ongoing path. *)
      (foldr
        (λ child (p:(Z * gmap (list u8) (list u8))),
          let acc' := match child with
                      | None => acc
                      | Some t' => traverse t' p.2 (path ++ [U8 p.1])
                      end
          in (p.1 + 1, acc'))
        (0, acc) children
      ).2
    end
  in traverse t ∅ [].

Definition is_nil_hash h : iProp Σ :=
  is_hash [] h.

Definition is_tree_hash' (recur : tree -d> list u8 -d> iPropO Σ) : tree -d> list u8 -d> iPropO Σ :=
  (λ t h,
  match t with
  | Leaf val => is_hash val h
  | Interior children =>
      ∃ (child_hashes : list (list u8)),
      ([∗ list] child;hash ∈ children;child_hashes,
        match child with
        | None => is_nil_hash hash
        | Some t' => ▷ recur t' hash
        end) ∗
      is_hash (concat child_hashes) h
  end)%I.

Local Instance is_tree_hash'_contractive : Contractive is_tree_hash'.
Proof. solve_contractive. Qed.

Definition is_tree_hash : tree → list u8 → iProp Σ := fixpoint is_tree_hash'.

Definition own_tree' (recur : loc -d> tree -d> iPropO Σ) : loc -d> tree -d> iPropO Σ :=
  (λ ptr arg,
    match arg with
    | Leaf val =>
      ∃ ptr_v v hash sl_hash sl_children,
      "Hval" ∷ Val.own ptr_v v ∗
      "Hptr_val" ∷ ptr ↦[Node :: "Val"] #ptr_v ∗
      "#His_hash" ∷ is_tree_hash arg hash ∗
      "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
      "Hsl_hash" ∷ ptr ↦[Node :: "hash"] (slice_val sl_hash) ∗
      "Hchildren" ∷ own_slice_small sl_children ptrT 1 (replicate 256 null) ∗
      "Hsl_children" ∷ ptr ↦[Node :: "Children"] (slice_val sl_children)
    | Interior children =>
      ∃ hash sl_hash sl_children ptr_children,
      "Hptr_val" ∷ ptr ↦[Node :: "Val"] #null ∗
      "#His_hash" ∷ is_tree_hash arg hash ∗
      "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
      "Hsl_children" ∷ own_slice_small sl_children ptrT 1 ptr_children ∗
      "Hptr_children" ∷ ptr ↦[Node :: "Children"] (slice_val sl_children) ∗
      "Hchildren" ∷
        ([∗ list] child;ptr_child ∈ children;ptr_children,
          match child with
          | None => ⌜ptr_child = null⌝
          | Some t' => ▷ recur ptr_child t'
          end)
    end)%I.

Local Instance own_tree'_contractive : Contractive own_tree'.
Proof. solve_contractive. Qed.

Definition own_tree : loc → tree → iProp Σ := fixpoint own_tree'.

Lemma own_tree_unfold ptr arg :
  own_tree ptr arg ⊣⊢
  match arg with
  | Leaf val =>
    ∃ ptr_v v hash sl_hash sl_children,
    "Hval" ∷ Val.own ptr_v v ∗
    "Hptr_val" ∷ ptr ↦[Node :: "Val"] #ptr_v ∗
    "#His_hash" ∷ is_tree_hash arg hash ∗
    "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
    "Hsl_hash" ∷ ptr ↦[Node :: "hash"] (slice_val sl_hash) ∗
    "Hchildren" ∷ own_slice_small sl_children ptrT 1 (replicate 256 null) ∗
    "Hsl_children" ∷ ptr ↦[Node :: "Children"] (slice_val sl_children)
  | Interior children =>
    ∃ hash sl_hash sl_children ptr_children,
    "Hptr_val" ∷ ptr ↦[Node :: "Val"] #null ∗
    "#His_hash" ∷ is_tree_hash arg hash ∗
    "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
    "Hsl_children" ∷ own_slice_small sl_children ptrT 1 ptr_children ∗
    "Hptr_children" ∷ ptr ↦[Node :: "Children"] (slice_val sl_children) ∗
    "Hchildren" ∷
      ([∗ list] child;ptr_child ∈ children;ptr_children,
        match child with
        | None => ⌜ptr_child = null⌝
        | Some t' => ▷ own_tree ptr_child t'
        end)
  end.
Proof. apply (fixpoint_unfold own_tree'). Qed.
End tree.

Module RootedTree.
Record t :=
  mk {
    Root: tree;
    PtrRoot: loc;
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr arg : iProp Σ :=
  "Hroot" ∷ own_tree arg.(PtrRoot) arg.(Root) ∗
  "Hptr_root" ∷ ptr ↦[Tree :: "Root"] #arg.(PtrRoot).
End local_defs.
End RootedTree.

Section proof.
Context `{!heapGS Σ}.

Lemma wp_InteriorHash children ptr_tree old_hash sl_children ptr_children :
  {{{
    "Hptr_val" ∷ ptr_tree ↦[Node :: "Val"] #null ∗
    "Hhash" ∷ ptr_tree ↦[Node :: "hash"] old_hash ∗
    "Hsl_children" ∷ own_slice_small sl_children ptrT 1 ptr_children ∗
    "Hstruct_children" ∷ ptr_tree ↦[Node :: "Children"] sl_children ∗
    "Hchildren" ∷
      ([∗ list] child;ptr_child ∈ children;ptr_children,
        match child with
        | None => ⌜ptr_child = null⌝
        | Some t' => ▷ own_tree ptr_child t'
        end)
  }}}
  Node__UpdateInteriorHash #ptr_tree
  {{{
    RET #();
    own_tree ptr_tree (Interior children)
  }}}.
Proof. Admitted.

Lemma sep_nil_children :
 ⊢
 ([∗ list] child;ptr_child ∈ replicate 256 None;replicate (int.nat 256) null,
   match child with
   | Some t' => ▷ own_tree ptr_child t'
   | None => ⌜ptr_child = null⌝
   end).
Proof.
  replace (int.nat 256) with (256%nat); [|word].
  naive_solver.
Qed.

Lemma wp_NewTree :
  {{{ True }}}
  NewTree #()
  {{{
    ptr_tree ptr_root, RET #ptr_tree;
    RootedTree.own ptr_tree (RootedTree.mk (Interior (replicate 256 None)) ptr_root)
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /NewTree.
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (ptr_node) "H".
  iDestruct (struct_fields_split with "H") as "H"; iNamed "H".
  wp_apply wp_NewSlice.
  iIntros (sl_children) "H".
  iDestruct (own_slice_to_small with "H") as "Hsl_children".
  wp_apply (wp_storeField with "[$]"); [val_ty|].
  iIntros "Hchildren".
  wp_apply (wp_InteriorHash with "[$Val $hash $Hsl_children $Hchildren]").
  {
    instantiate (1:=(replicate 256 None)).
    iApply sep_nil_children.
  }
  iIntros "Htree".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (ptr_tree) "H".
  iDestruct (struct_fields_split with "H") as "H"; iNamed "H".
  iApply "HΦ".
  iFrame.
Qed.

End proof.
