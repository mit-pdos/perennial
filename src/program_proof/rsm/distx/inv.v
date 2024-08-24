From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.distx Require Import base.
From Perennial.program_proof.rsm.distx Require Export inv_txnsys inv_key inv_group.
  
Section inv.
  Context `{!heapGS Σ, !distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition distxN := nroot .@ "distx".

  Definition distx_inv γ : iProp Σ :=
    (* txn invariants *)
    "Htxn"    ∷ txnsys_inv γ ∗
    (* keys invariants *)
    "Hkeys"   ∷ ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    (* groups invariants *)
    "Hgroups" ∷ ([∗ set] gid ∈ gids_all, group_inv γ gid).

  #[global]
  Instance distx_inv_timeless γ :
    Timeless (distx_inv γ).
  Admitted.

  Definition know_distx_inv γ : iProp Σ :=
    inv distxN (distx_inv γ).

End inv.
