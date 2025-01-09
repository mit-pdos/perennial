From Perennial.base_logic Require Import ghost_map.
From Perennial.program_proof.tulip.program Require Import prelude.

Section res.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition txnmap_auth (τ : gname) (m : gmap dbkey dbval) : iProp Σ := ghost_map_auth τ 1 m.

  Definition txnmap_ptsto (τ : gname) (k : dbkey) (v : dbval) : iProp Σ :=
    ghost_map_elem τ k (DfracOwn 1) v.

  Definition txnmap_ptstos (τ : gname) (m : dbmap) : iProp Σ :=
    [∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v.

  Lemma txnmap_alloc m :
    ⊢ |==> ∃ τ, txnmap_auth τ m ∗ ([∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v).
  Proof. iApply (ghost_map_alloc m). Qed.

  Lemma txnmap_lookup τ m k v :
    txnmap_auth τ m -∗
    txnmap_ptsto τ k v -∗
    ⌜m !! k = Some v⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iApply (ghost_map_lookup with "Hauth Hfrag").
  Qed.

  Lemma txnmap_update {τ m k v1} v2 :
    txnmap_auth τ m -∗
    txnmap_ptsto τ k v1 ==∗
    txnmap_auth τ (<[k := v2]> m) ∗ txnmap_ptsto τ k v2.
  Proof.
    iIntros "Hauth Hfrag".
    iApply (ghost_map_update with "Hauth Hfrag").
  Qed.

  Lemma txnmap_subseteq τ m1 m2 :
    txnmap_auth τ m1 -∗
    txnmap_ptstos τ m2 -∗
    ⌜m2 ⊆ m1⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iApply (ghost_map_lookup_big with "Hauth Hfrag").
  Qed.

  Definition local_gid_token (α : gname) (gid : u64) : iProp Σ :=
    ghost_map_elem α gid (DfracOwn 1) tt.

  Lemma local_gid_tokens_alloc (gids : gset u64) :
    ⊢ |==> ∃ α, [∗ set] gid ∈ gids, local_gid_token α gid.
  Proof.
    iMod (ghost_map_alloc (gset_to_gmap tt gids)) as (α) "[_ Hfrags]".
    rewrite big_sepM_gset_to_gmap.
    by iFrame.
  Qed.

  Lemma local_gid_token_ne (α : gname) (gid1 gid2 : u64) :
    local_gid_token α gid1 -∗
    local_gid_token α gid2 -∗
    ⌜gid2 ≠ gid1⌝.
  Proof.
    iIntros "Hgid1 Hgid2".
    iApply (ghost_map_elem_ne with "Hgid2 Hgid1").
  Qed.

End res.
