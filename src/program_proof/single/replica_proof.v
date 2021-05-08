From Perennial.Helpers Require Export range_set.
From iris.algebra Require Import gmap lib.mono_nat.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.memkv Require Export common_proof.
From Perennial.base_logic Require Export lib.ghost_map.
From iris.algebra Require Import excl agree auth gmap csum.

Section replica_ghost.

Context `{!heapG Σ}.
Context {V:Type}.
Context `{ghost_mapG Σ nat (option V)}.

Definition one_shot_decideR := csumR (exclR unitR) (agreeR (leibnizO V)).
Context `{inG Σ one_shot_decideR}.

Context `{f:nat}.

Record single_names :=
{
  pn_gn : gname;
  val_gn : gname;
}
.

Implicit Types γ:single_names.
Implicit Types (pn:nat).
Implicit Types (pid:nat).
Implicit Types c:V.

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

Instance accepted_tmlss γ pid pn : Timeless (accepted γ pid pn).
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
    (∃ c, pn ↪[γ.(pn_gn)]□ Some c) ∗
    ⌜is_majority Q⌝ ∗
    [∗ set] pid ∈ Q, accepted γ pid pn
.

(* witness that all smaller pn that were committed must have command c *)
Definition pn_prop γ (pn:nat) c : iProp Σ :=
  □(
    ∀ (pn':nat),
      ⌜pn' < pn⌝ →
      committed γ pn' -∗
      pn' ↪[γ.(pn_gn)]□ Some c
    )
.

(* each witness for a proposal choice carries a witness that all smaller
proposals that were committed must match the value that this proposal chose *)
Definition pn_ptsto γ pn (c:V) : iProp Σ :=
  pn ↪[γ.(pn_gn)]□ Some c ∗
  pn_prop γ pn c
.

Definition cmd_undec γ : iProp Σ :=
  own γ.(val_gn) (Cinl (Excl ()))
.

Definition cmd_is γ c : iProp Σ :=
  own γ.(val_gn) (Cinr (to_agree (c:leibnizO V))) ∗
  (∃ pn, pn_ptsto γ pn c ∗ committed γ pn)
.

Definition consensus_inv γ : iProp Σ :=
  cmd_undec γ ∨
  (∃ c, cmd_is γ c).

Definition trivial_inv γ : iProp Σ :=
  ∃ (pnM:gmap nat (option V)),
  "HpnM" ∷ ghost_map_auth γ.(pn_gn) 1 pnM
.

Lemma key_fact1 N γ pn c :
  inv N (consensus_inv γ) -∗
  pn_ptsto γ pn c -∗
  committed γ pn ={⊤}=∗
  cmd_is γ c
.
Proof.
  iIntros "#Hcinv #Hptsto #Hcom".
  iInv "Hcinv" as "[>Hc|>#Hc]" "Hclose".
  { (* trivial; we get to take the fupd that decides the command *)
    iMod (own_update _ _ (Cinr (to_agree (c:leibnizO V))) with "[$Hc]") as "#Hcmd".
    {
      apply cmra_update_exclusive.
      done.
    }
    iFrame "Hcmd".
    iExists pn.
    iFrame "#".
    iMod ("Hclose" with "[]"); last done.
    iNext.
    iRight.
    iExists _; iFrame "#".
    iExists _; iFrame "#".
  }
  {
    (* want to match c0 with c; use pn_prop *)
    iDestruct "Hc" as (c') "Hc".
    iAssert (_) with "Hc" as "#Hcbackup".
    iDestruct "Hc" as "[#Hc' #Hpn]".

    iDestruct "Hpn" as (pn') "[#Hptsto' #Hcom']".

    assert (pn' < pn) as Hineq by admit. (* cases *)
    iDestruct "Hptsto" as "[Hptsto Hprop]".
    iDestruct ("Hprop" $! pn' with "[] Hcom'") as "Hptsto'2".
    { done. }
    (* TODO: use the two pn_ptstos we have to match up c and c', then finish *)
    admit.
  }
Admitted.

End replica_ghost.
