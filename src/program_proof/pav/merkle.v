From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import merkle.

From Perennial.program_proof.pav Require Import cryptoffi cryptoutil.
From Perennial.program_proof Require Import std_proof marshal_stateless_proof.

Notation empty_node_tag := (W8 0) (only parsing).
Notation inner_node_tag := (W8 1) (only parsing).
Notation leaf_node_tag := (W8 2) (only parsing).

Section proof.
Context `{!heapGS Σ}.

(* returns false if bit n of l is 0. *)
Definition get_bit (l : list w8) (n : nat) : option bool. Admitted.

Fixpoint is_merk_proof_recur (depth_inv : nat) (label : list w8) (val : option $ list w8) (proof : list $ list w8) (hash : list w8) : iProp Σ :=
  match depth_inv with
  | 0%nat =>
    match val with
    (* empty node. *)
    | None => is_hash [empty_node_tag] hash
    (* leaf node. *)
    | Some val' => is_hash (leaf_node_tag :: label ++ (u64_le $ length val') ++ val') hash
    end
  | S depth_inv' =>
    let depth := (length proof - depth_inv)%nat in
    ∃ next_hash,
    (* next recurrence. *)
    is_merk_proof_recur depth_inv' label val proof next_hash ∗
    match proof !! depth with None => False | Some sib_hash =>
    match get_bit label depth with None => False | Some next_pos =>
    let children :=
      match next_pos with
      | false => (next_hash, sib_hash)
      | true => (sib_hash, next_hash)
      end in
    (* inner node. *)
    is_hash (inner_node_tag :: children.1 ++ children.2) hash
    end
    end
  end.

Definition is_merk_proof (label : list w8) (val : option $ list w8) (proof : list $ list w8) (dig : list w8) : iProp Σ :=
  is_merk_proof_recur (length proof) label val proof dig.

Lemma is_merk_proof_inj label val0 val1 proof0 proof1 dig :
  is_merk_proof label val0 proof0 dig -∗
  is_merk_proof label val1 proof1 dig -∗
  ⌜ val0 = val1 ⌝.
Proof. Admitted.

End proof.
