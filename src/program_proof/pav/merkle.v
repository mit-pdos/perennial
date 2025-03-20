From Perennial.program_proof Require Import grove_prelude.
From Perennial Require Import base.
From Goose.github_com.mit_pdos.pav Require Import merkle.

From Perennial.Helpers Require Import bytes.
From Perennial.program_proof.pav Require Import cryptoffi cryptoutil.
From Perennial.program_proof Require Import std_proof marshal_stateless_proof.

Notation empty_node_tag := (W8 0) (only parsing).
Notation inner_node_tag := (W8 1) (only parsing).
Notation leaf_node_tag := (W8 2) (only parsing).

Section proof.
Context `{!heapGS Σ}.

(* get_bit returns false if bit n of l is 0. *)
Definition get_bit (l : list w8) (n : nat) : option bool :=
  mjoin (byte_to_bits <$> l) !! n.

(* TODO: rm once seal merged in. *)
Program Definition u64_le_seal := sealed @u64_le.
Definition u64_le_unseal : u64_le_seal = _ := seal_eq _.
Lemma u64_le_seal_len x :
  length $ u64_le_seal x = 8%nat.
Proof. Admitted.

(** Merkle proofs. *)

Fixpoint is_merk_proof_recur (depth : nat) (label : list w8)
    (val : option $ list w8) (proof : list $ list w8)
    (hash : list w8) : iProp Σ :=
  match proof with
  | [] =>
    match val with
    (* empty node. *)
    | None => is_hash [empty_node_tag] hash
    (* leaf node. *)
    | Some val' => is_hash (leaf_node_tag :: label ++ (u64_le_seal $ length val') ++ val') hash
    end
  | sib_hash :: proof' =>
    ∃ next_hash,
    (* next recurrence. *)
    is_merk_proof_recur (S depth) label val proof' next_hash ∗
    ⌜ length sib_hash = hash_len ⌝ ∗
    match get_bit label depth with None => False | Some next_pos =>
    let children :=
      match next_pos with
      | false => next_hash ++ sib_hash
      | true => sib_hash ++ next_hash
      end in
    (* inner node. *)
    is_hash (inner_node_tag :: children) hash
    end
  end.

Definition is_merk_proof (label : list w8) (val : option $ list w8)
    (proof : list $ list w8) (dig : list w8) : iProp Σ :=
  is_merk_proof_recur 0 label val proof dig.

Lemma is_merk_proof_recur_len depth label val proof hash :
  is_merk_proof_recur depth label val proof hash -∗
  ⌜ length hash = hash_len ⌝.
Proof.
  iIntros "H". destruct proof; simpl.
  - case_match; by iApply is_hash_len.
  - iDestruct "H" as (?) "(?&?&?)".
    repeat case_match; try done; by iApply is_hash_len.
Qed.

Lemma is_merk_proof_recur_inj depth label val0 val1 proof0 proof1 hash :
  is_merk_proof_recur depth label val0 proof0 hash -∗
  is_merk_proof_recur depth label val1 proof1 hash -∗
  ⌜ val0 = val1 ⌝.
Proof.
  iIntros "H0 H1".
  iInduction (proof0) as [|sib_hash0] "IH" forall (depth proof1 hash).
  { destruct proof1; simpl;
      [|iDestruct "H1" as (?) "(_ & _ & H1)"];
      repeat case_match; try done;
      iDestruct (is_hash_inj with "H0 H1") as %Heq; try naive_solver.
    (* both leaves. use leaf encoding. *)
    iPureIntro. simplify_eq/=.
    apply app_inj_1 in Heq; [naive_solver|].
    by rewrite !u64_le_seal_len. }
  destruct proof1 as [|sib_hash1]; simpl.
  - iDestruct "H0" as (?) "(_ & % & H0)".
    repeat case_match; try done;
      iDestruct (is_hash_inj with "H0 H1") as %?; naive_solver.
  - iDestruct "H0" as (?) "(HR0 & % & H0)".
    iDestruct "H1" as (?) "(HR1 & % & H1)".
    iDestruct (is_merk_proof_recur_len with "HR0") as %?.
    iDestruct (is_merk_proof_recur_len with "HR1") as %?.
    (* both inner. use inner encoding and next_pos same to get
    the same next_hash. then apply IH. *)
    repeat case_match; try done;
      iDestruct (is_hash_inj with "H0 H1") as %?;
      list_simplifier; iApply ("IH" with "HR0 HR1").
Qed.

Lemma is_merk_proof_inj label val0 val1 proof0 proof1 dig :
  is_merk_proof label val0 proof0 dig -∗
  is_merk_proof label val1 proof1 dig -∗
  ⌜ val0 = val1 ⌝.
Proof. iIntros "H0 H1". iApply (is_merk_proof_recur_inj with "H0 H1"). Qed.

(** Merkle trees. *)

Fixpoint is_merk_tree_recur (depth : nat)
    (elems : gmap (list w8) (list w8)) (hash : list w8) : iProp Σ :=
  match map_to_list elems with
  | [] => is_hash [empty_node_tag] hash
  | [(label, val)] => is_hash (leaf_node_tag :: label ++ (u64_le_seal $ length val) ++ val) hash
  | _ =>
    ∃ elems0 elems1 next_hash0 next_hash1,
    ⌜ elems0 ∪ elems1 = elems ⌝ ∗
    ⌜ elems0 ##ₘ elems1 ⌝ ∗
    ⌜ (∀ l, l ∈ dom elems0 →
      match get_bit l depth with None => False | Some b => ¬Is_true b end) ⌝ ∗
    ⌜ (∀ l, l ∈ dom elems1 →
      match get_bit l depth with None => False | Some b => Is_true b end) ⌝ ∗
    is_merk_tree_recur (S depth) elems0 next_hash0 ∗
    is_merk_tree_recur (S depth) elems1 next_hash1 ∗
    is_hash (inner_node_tag :: next_hash0 ++ next_hash1) hash
  end.

End proof.
