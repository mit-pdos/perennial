From Perennial.program_proof Require Import grove_prelude.

From Perennial.program_proof.pav Require Import classes cryptoffi rpc.

Section chain.
Context `{!heapGS Σ}.

(* is_link represents a single chain link connection.
it removes the need to think about records or encoding. *)
Definition is_link epoch prevLink dig link : iProp Σ :=
  is_hash (chainSepSome.encodesF (chainSepSome.mk epoch prevLink dig)) link.
Notation is_link2 :=
  (λ (a : w64 * list w8 * list w8) b, is_link a.1.1 a.1.2 a.2 b) (only parsing).

Global Instance is_link_func : Func is_link2.
Proof.
  rewrite /Func /is_link.
  iIntros (???) "Hlink0 Hlink1".
  by iDestruct (is_hash_func with "Hlink0 Hlink1") as %->.
Qed.
Global Instance is_link_inj : InjRel is_link2.
Proof.
  rewrite /InjRel /is_link.
  iIntros (???) "Hlink0 Hlink1".
  iDestruct (is_hash_inj with "Hlink0 Hlink1") as %Heq.
  eapply chainSepSome.inj in Heq as [=].
  destruct x1 as [x1' ?], x2 as [x2' ?], x1', x2'.
  naive_solver.
Qed.

(* is_chain binds an entire list of data to a single link. *)
Fixpoint is_chain_aux (data : list (list w8)) (link : list w8) : iProp Σ :=
  match data with
  | [] => is_hash [(W8 0)] link
  | d :: data' =>
    ∃ prevLink,
    is_chain_aux data' prevLink ∗
    is_link (length data') prevLink d link
  end.
Definition is_chain data link := is_chain_aux (reverse data) link.

Global Instance is_chain_pers data link : Persistent (is_chain data link).
Proof. Admitted.
Global Instance is_chain_func : Func is_chain.
Proof. Admitted.
Global Instance is_chain_inj : InjRel is_chain.
Proof. Admitted.

Lemma is_chain_extend data prev_link next_data next_link :
  is_chain data prev_link -∗
  is_link (length data) prev_link next_data next_link -∗
  is_chain (data ++ [next_data]) next_link.
Proof. Admitted.

Lemma is_chain_to_link data prev_link next_data next_link :
  is_chain data prev_link -∗
  is_chain (data ++ [next_data]) next_link -∗
  is_link (length data) prev_link next_data next_link.
Proof. Admitted.

(* is_chain_all is like is_chain, but it talks about all links,
not just the last one. *)
Definition is_chain_all (data links : list (list w8)) : iProp Σ :=
  ([∗ list] epoch ↦ link ∈ links, is_chain (take (uint.nat epoch) data) link).

End chain.
