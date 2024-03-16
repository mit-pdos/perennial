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
  "HB_ptr" ∷ ptr ↦[Id :: "B"] (slice_val sl_B).
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
  "HB_ptr" ∷ ptr ↦[Id :: "B"] (slice_val sl_B).
End local_defs.
End Val.

Section proof.
Context `{!heapGS Σ}.

(* TODO: will need to carry some invariant that the # of children == 256. *)
Inductive tree : Type :=
  | Leaf : list u8 → tree
  | ChildNode : list (option tree) → tree.

Definition tree_to_map (t : tree) : gmap (list u8) (list u8) :=
  let fix traverse (t : tree) (acc : gmap (list u8) (list u8)) (path : list u8) :=
    match t with
    | Leaf val => <[path:=val]>acc
    | ChildNode children =>
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
  | ChildNode children =>
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



End proof.
