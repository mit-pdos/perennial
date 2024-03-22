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
(* TODO: change this with golang change. *)
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

Section node.
Context `{!heapGS Σ}.

(* TODO: will need to carry some invariant that the # of children == 256. *)
Inductive tree : Type :=
  (* Cut only exists for proof checking trees. *)
  | Cut : list u8 → tree
  | Empty : tree
  | Leaf : list u8 → tree
  | Interior : list tree → tree.

Fixpoint contains (t : tree) (id : list u8) (val : option (list u8)) : Prop :=
  match t with
  | Cut _ => False
  | Empty => id = [] ∧ val = None
  | Leaf val' => id = [] ∧ val = (Some val')
  | Interior children =>
    match id with
    | [] => False
    | pos :: rest =>
      ∃ child, children !! int.nat pos = Some child ∧ contains child rest val
    end
  end.

Definition tree_to_map (t : tree) : gmap (list u8) (list u8) :=
  let fix traverse (t : tree) (acc : gmap (list u8) (list u8)) (path : list u8) :=
    match t with
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
  in traverse t ∅ [].

Definition is_nil_hash h : iProp Σ :=
  is_hash [] h.

Definition is_tree_hash' (recur : tree -d> list u8 -d> iPropO Σ) : tree -d> list u8 -d> iPropO Σ :=
  (λ t h,
  match t with
  | Cut h' => ⌜h = h'⌝
  | Empty => is_hash [U8 0] h
  | Leaf val => is_hash (val ++ [U8 1]) h
  | Interior children =>
      ∃ (child_hashes : list (list u8)),
      ([∗ list] child;h2 ∈ children;child_hashes,
        ▷ recur child h2) ∗
      is_hash (concat child_hashes ++ [U8 2]) h
  end)%I.

Local Instance is_tree_hash'_contractive : Contractive is_tree_hash'.
Proof. solve_contractive. Qed.

Definition is_tree_hash : tree → list u8 → iProp Σ := fixpoint is_tree_hash'.

Definition own_Node' (recur : loc -d> tree -d> iPropO Σ) : loc -d> tree -d> iPropO Σ :=
  (λ ptr arg,
    match arg with
    (* We should never have cuts in in-memory trees. *)
    | Cut _ => False
    | Empty =>
      ∃ hash,
      "#His_hash" ∷ is_tree_hash arg hash ∗
      "%Hnil" ∷ ⌜ptr = null⌝
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
          ▷ recur ptr_child child)
    end)%I.

Local Instance own_Node'_contractive : Contractive own_Node'.
Proof. solve_contractive. Qed.

Definition own_Node : loc → tree → iProp Σ := fixpoint own_Node'.

Lemma own_Node_unfold ptr arg :
  own_Node ptr arg ⊣⊢ (own_Node' own_Node) ptr arg.
Proof.
  apply (fixpoint_unfold own_Node').
Qed.

End node.

Module Tree.
Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr arg : iProp Σ :=
  ∃ tree root,
  "Htree" ∷ own_Node root tree ∗
  "%Htree_map" ∷ ⌜tree_to_map tree = arg⌝ ∗
  "Hptr_root" ∷ ptr ↦[Tree :: "Root"] #root.
End local_defs.
End Tree.

Section TreeProofs.
Context `{!heapGS Σ}.

(*
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
        | Some t' => ▷ own_Node ptr_child t'
        end)
  }}}
  Node__UpdateInteriorHash #ptr_tree
  {{{
    RET #();
    own_Node ptr_tree (Interior children)
  }}}.
Proof. Admitted.

Lemma sep_nil_children :
 ⊢
 ([∗ list] child;ptr_child ∈ replicate 256 None;replicate (int.nat 256) null,
   match child with
   | Some t' => ▷ own_Node ptr_child t'
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

(* TODO: not enough time to write down proof record. *)
Definition Proof_own (ptr_proof:loc) (proof:u64) : iProp Σ.
Admitted.
 *)

(*
Pre: valid tree at ptr_tree that goes to some map.
Post: valid tree at ptr_tree that goes to new map.
 *)
Lemma wp_Put ptr_tree entry_map ptr_id id ptr_val val :
  {{{
    "Htree" ∷ Tree.own ptr_tree entry_map ∗
    "Hid" ∷ Id.own ptr_id id ∗
    "Hval" ∷ Val.own ptr_val val
  }}}
  Tree__Put #ptr_tree #ptr_id #ptr_val
  {{{
    sl_digest ptr_proof (err:u64),
    RET ((slice_val sl_digest), #ptr_proof, #err);
    if bool_decide (err = 0) then
      "Htree" ∷ Tree.own ptr_tree (<[id.(Id.B):=val.(Val.B)]>entry_map)
    else True%I
  }}}.
Proof. Admitted.

(* TODO: all the other tree specs. *)

End TreeProofs.

Module MembProof.
Section local_defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) : iProp Σ.
Admitted.
End local_defs.
End MembProof.

Module NonmembProof.
Section local_defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) : iProp Σ.
Admitted.
End local_defs.
End NonmembProof.

Section CheckProofs.
Context `{!heapGS Σ}.

Definition is_path (id : list u8) (val : option (list u8)) (digest : list u8) : iProp Σ :=
  ∃ tree,
  is_tree_hash tree digest ∧
  ⌜contains tree id val⌝.

Lemma wp_MembCheck ptr_proof ptr_id id ptr_val val sl_dig dig :
  {{{
    "Hproof" ∷ MembProof.own ptr_proof ∗
    "Hid" ∷ Id.own ptr_id id ∗
    "Hval" ∷ Val.own ptr_val val ∗
    "Hdig" ∷ own_slice_small sl_dig byteT 1 dig
  }}}
  MembProof__Check #ptr_proof #ptr_id #ptr_val (slice_val sl_dig)
  {{{
    (err:u64), RET #err;
    if bool_decide (err = 0) then
      "Hpath" ∷ is_path (id.(Id.B)) (Some val.(Val.B)) dig
    else True%I
  }}}.
Proof. Admitted.

Lemma wp_NonmembCheck ptr_proof ptr_id id sl_dig dig :
  {{{
    "Hproof" ∷ MembProof.own ptr_proof ∗
    "Hid" ∷ Id.own ptr_id id ∗
    "Hdig" ∷ own_slice_small sl_dig byteT 1 dig
  }}}
  MembProof__Check #ptr_proof #ptr_id (slice_val sl_dig)
  {{{
    (err:u64), RET #err;
    if bool_decide (err = 0) then
      "Hpath" ∷ is_path (id.(Id.B)) None dig
    else True%I
  }}}.
Proof. Admitted.

End CheckProofs.
