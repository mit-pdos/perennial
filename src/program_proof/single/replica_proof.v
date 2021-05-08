From Perennial.Helpers Require Export range_set.
From iris.algebra Require Import gmap lib.mono_nat.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.memkv Require Export common_proof.
From Perennial.base_logic Require Export lib.ghost_map.

Section replica_ghost.

Context `{!heapG Σ}.
Context {V:Type}.
Context `{ghost_mapG Σ nat (option V)}.
Context `{f:nat}.

Record single_names :=
{
  pn_gn : gname;
}
.

Implicit Types γ:single_names.
Implicit Types (pn:nat).
Implicit Types (pid:nat).
Implicit Types c:V.

Definition pn_ptsto γ pn (c:V) : iProp Σ :=
  pn ↪[γ.(pn_gn)]□ Some c
.

(*
  If entry ↦ c, then ∃ pn, pn ↦ c ∗ (committed pn).

  Want pn ↦ c ∗ pn' ↦ c' ∗ (committed pn) ∗ ⌜pn' > pn⌝ ={⊤}=∗ c = c'.

  Then, pn' ↦ c

  Only allow a
*)

Definition accepted γ pid pn : iProp Σ.
Admitted.

Instance accepted_pers γ pid pn : Persistent (accepted γ pid pn).
Admitted.

Definition rejected γ pid pn : iProp Σ.
Admitted.

Definition is_valid (Q:gset nat) : Prop :=
  (∀ q, q ∈ Q → q ≤ (2 * f + 1))
.

Definition is_majority (Q:gset nat) : Prop :=
  is_valid Q ∧
  size Q > f + 1.

Definition committed γ pn : iProp Σ :=
  ∃ (Q:gset nat),
    ⌜is_majority Q⌝ ∗
    [∗ set] pid ∈ Q, accepted γ pid pn
.

Definition pn_prop γ (pn:nat) c : iProp Σ :=
  □(
    ∀ (pn':nat) (c':V),
      ⌜pn' < pn⌝ →
      committed γ pn' -∗
      pn_ptsto γ pn' c' -∗
      ⌜c = c'⌝
    )
.

Definition cmd_undec γ : iProp Σ.
Admitted.

Definition cmd_is γ c : iProp Σ.
Admitted.

Definition consensus_inv γ : iProp Σ :=
  cmd_undec γ ∨
  (∃ c, cmd_is γ c).

Definition trivial_inv γ : iProp Σ :=
  ∃ (pnM:gmap nat (option V)),
  "HpnM" ∷ ghost_map_auth γ.(pn_gn) 1 pnM
.

Lemma key_fact N γ pn c :
  inv N (consensus_inv γ) -∗
  pn_ptsto γ pn c -∗
  committed γ pn ={⊤}=∗
  cmd_is γ c
.
Proof.
  iIntros "#Hcinv #Hptsto #Hcom".
  iInv "Hcinv" as "[Hc|Hc]" "Hclose".
  { (* trivial; we get to take the fupd that decides the command *)
    admit.
  }
  {
    (* want to match c0 with c; use pn_prop *)
    admit.
  }
Admitted.

End replica_ghost.
