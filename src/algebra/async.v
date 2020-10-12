From stdpp Require Import countable.
From iris.base_logic Require Import lib.iprop.
From iris.proofmode Require Import tactics.
From Perennial.algebra Require Import log_heap.

Set Default Proof Using "Type".

Section async.
Context {Σ: gFunctors} {K V: Type} `{Countable0: Countable K}.

Implicit Types (γ:gname).

(* this idea is for this to basically be a discrete_funUR from txn_id to gmap K
V. However, we want to be able to own the right to extend the async, which is
part of ephemeral_val_from, and to talk about a particular old transaction
persistently, which is ephemeral_txn_val.

 Durability is orthogonal to this library: separately from the async we know
 that some index is durable, which guarantees that facts about that index and
 below can be carried across a crash. *)
Definition async_ctx γ (σs: async (gmap K V)) : iProp Σ.
Admitted.

Global Instance async_ctx_timeless γ σs : Timeless (async_ctx γ σs).
Admitted.

(* ephemeral_val_from owns ephemeral transactions from i onward (including
future transactions); this is what makes it possible to use ephemeral
maps-to facts to append a new gmap with those addresses updated (see
[map_update_predicate] for the kind of thing we should be able to do) *)
Definition ephemeral_val_from γ (i:nat) (k: K) (v: V) : iProp Σ.
Admitted.

(* ephemeral_txn_val owns only a single point in the ephemeral transactions. We
could probably make this persistent by freezing the address whenever this is
generated. *)
Definition ephemeral_txn_val γ (i:nat) (k: K) (v: V) : iProp Σ.
Admitted.

(* exactly like [ephemeral_txn_val] except owning a half-empty range of
transactions [lo, hi) *)
Definition ephemeral_txn_val_range γ (lo hi:nat) (k: K) (v: V): iProp Σ :=
  [∗ list] i ∈ seq lo (hi-lo), ephemeral_txn_val γ i k v.

Theorem ephemeral_txn_val_range_acc γ lo hi k v i :
  (lo ≤ i < hi)%nat →
  ephemeral_txn_val_range γ lo hi k v -∗
  (* does not return the range under the assumption we make these persistent *)
  ephemeral_txn_val γ i k v.
Proof.
  iIntros (Hbound) "Hrange".
  rewrite /ephemeral_txn_val_range.
  assert (seq lo (hi - lo)%nat !! (i - lo)%nat = Some i).
  { apply lookup_seq; lia. }
  iDestruct (big_sepL_lookup with "Hrange") as "$"; eauto.
Qed.

Theorem ephemeral_val_from_in_bounds γ σs i a v :
  async_ctx γ σs -∗
  ephemeral_val_from γ i a v -∗
  (* if equal, only owns the new transactions and no current ones *)
  ⌜i < length (possible σs)⌝%nat.
Proof.
Admitted.

(* TODO: [ephemeral_val_from i] should probably imply that transaction i is
within bounds, otherwise it doesn't give the right to extend; this rule is then
only valid when i' is also in-bounds *)
Theorem ephemeral_val_from_split i' γ i k v :
  (i ≤ i')%nat →
  ephemeral_val_from γ i k v -∗
  ephemeral_txn_val_range γ i i' k v ∗ ephemeral_val_from γ i' k v.
Proof.
Admitted.

Theorem async_update_map m' γ σs m0 txn_id :
  dom (gset _) m' = dom (gset _) m0 →
  async_ctx γ σs -∗
  ([∗ map] a↦v ∈ m0, ephemeral_val_from γ txn_id a v) -∗
  |==> async_ctx γ (async_put (m' ∪ latest σs) σs) ∗
       ([∗ map] a↦v ∈ m', ephemeral_val_from γ txn_id a v).
Proof.
  (* this can probably be proven by adding a copy of latest σs to the end and
  then updating each address in-place (normally it's not possible to change an
  old txn_id, but perhaps that's fine at the logical level? after all,
  ephemeral_val_from txn_id a v is more-or-less mutable if txn_id is lost) *)
Admitted.

(* this splits off an [ephemeral_val_from] at exactly the last transaction *)
Theorem async_ctx_ephemeral_val_from_split γ σs i a v :
  async_ctx γ σs -∗
  ephemeral_val_from γ i a v -∗
  async_ctx γ σs ∗ ephemeral_txn_val_range γ i (length (possible σs) - 1) a v ∗
  ephemeral_val_from γ (length (possible σs) - 1) a v.
Proof.
  iIntros "Hctx Hi+".
  iDestruct (ephemeral_val_from_in_bounds with "Hctx Hi+") as %Hinbounds.
  iDestruct (ephemeral_val_from_split (length (possible σs) - 1) with "Hi+") as "[Hold H+]"; eauto.
  { lia. }
  iFrame.
Qed.

Theorem async_ctx_ephemeral_val_from_map_split γ σs i m :
  async_ctx γ σs -∗
  big_opM bi_sep (ephemeral_val_from γ i) m -∗
  async_ctx γ σs ∗ big_opM bi_sep (ephemeral_txn_val_range γ i (length (possible σs) - 1)) m ∗
  big_opM bi_sep (ephemeral_val_from γ (length (possible σs) - 1)) m.
Proof.
  iIntros "Hctx Hm".
  iInduction m as [|a v m] "IH" using map_ind.
  - rewrite !big_sepM_empty.
    iFrame.
  - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; auto.
    iDestruct (async_ctx_ephemeral_val_from_split with "Hctx Hi") as "(Hctx&Hrange&H+)".
    iDestruct ("IH" with "Hctx Hm") as "(Hctx&Hmrange&Hm+)".
    iFrame.
    rewrite !big_sepM_insert //; iFrame.
Qed.

End async.
