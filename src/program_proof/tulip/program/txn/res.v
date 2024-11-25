From Perennial.program_proof.tulip.program Require Import prelude.

Section res.
  Context `{!heapGS Σ}.

  Definition txnmap_auth (τ : gname) (m : dbmap) : iProp Σ.
  Admitted.

  Definition txnmap_ptsto (τ : gname) (k : dbkey) (v : dbval) : iProp Σ.
  Admitted.

  Definition txnmap_ptstos (τ : gname) (m : dbmap) : iProp Σ :=
    [∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v.

  Lemma txnmap_alloc m :
    ⊢ |==> ∃ τ, txnmap_auth τ m ∗ ([∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v).
  Admitted.

  Lemma txnmap_lookup τ m k v :
    txnmap_auth τ m -∗
    txnmap_ptsto τ k v -∗
    ⌜m !! k = Some v⌝.
  Admitted.

  Lemma txnmap_update {τ m k v1} v2 :
    txnmap_auth τ m -∗
    txnmap_ptsto τ k v1 ==∗
    txnmap_auth τ (<[k := v2]> m) ∗ txnmap_ptsto τ k v2.
  Admitted.

  Lemma txnmap_subseteq τ m1 m2 :
    txnmap_auth τ m1 -∗
    txnmap_ptstos τ m2 -∗
    ⌜m2 ⊆ m1⌝.
  Admitted.

  Definition local_gid_token (α : gname) (gid : u64) : iProp Σ.
  Admitted.

  Lemma local_gid_tokens_alloc (gids : gset u64) :
    ⊢ |==> ∃ α, [∗ set] gid ∈ gids, local_gid_token α gid.
  Admitted.

  Lemma local_gid_token_ne (α : gname) (gid1 gid2 : u64) :
    local_gid_token α gid1 -∗
    local_gid_token α gid2 -∗
    ⌜gid2 ≠ gid1⌝.
  Admitted.

End res.
