From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.base_logic Require Export lib.ghost_map.
From iris.algebra Require Import excl agree auth gmap csum.

Section replica_ghost.

Definition one_shotR V := csumR (exclR unitR) (agreeR (leibnizO V)).

Class paxosG Σ (V : Type) := PaxosG {
  paxos_oneshotG :> inG Σ (one_shotR V);
  paxos_proposalG :> ghost_mapG Σ nat (option V);
  paxos_acceptG :> ghost_mapG Σ (nat*nat) (option bool);
}.

Context (f:nat).
Context {V:Type}.
Context `{!paxosG Σ V}.
Context `{!invG Σ}.

Record single_names :=
{
  acc_gn: gname;
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
*)

Definition undecided γ pid pn : iProp Σ :=
  (pn,pid) ↪[γ.(acc_gn)] None
.

Definition accepted γ pid pn : iProp Σ :=
  (pn,pid) ↪[γ.(acc_gn)]□ Some true
.

Definition rejected γ pid pn : iProp Σ :=
  (pn,pid) ↪[γ.(acc_gn)]□ Some false
.

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
      ⌜pn' ≤ pn⌝ →
      committed γ pn' -∗
      pn' ↪[γ.(pn_gn)]□ Some c (* NOTE: generalize this to knowledge that c is a superset of what was proposed earlier *)
    )
.

(* each witness for a proposal choice carries a witness that all smaller
proposals that were committed must match the value that this proposal chose *)
Definition pn_ptsto γ pn (c:V) : iProp Σ :=
  pn ↪[γ.(pn_gn)]□ Some c ∗
  pn_prop γ pn c
.

Definition pn_undec γ pn : iProp Σ :=
  pn ↪[γ.(pn_gn)] None
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

    assert (pn' ≤ pn ∨ pn < pn') as [Hineq|Hineq] by lia. (* cases *)
    {
      iDestruct "Hptsto" as "[Hptsto Hprop]".
      iDestruct ("Hprop" $! pn' with "[] Hcom'") as "Hptsto'2".
      { done. }
      Search "ghost_map".
      iDestruct "Hptsto'" as "[Hptsto' Hprop']".
      iDestruct (ghost_map_elem_agree with "Hptsto' Hptsto'2") as %Heq.
      replace (c) with (c') by naive_solver.
      iFrame "#".
      iMod ("Hclose" with "[]"); last done.
      iRight.
      iExists _; iFrame "#".
    }
    {
      iDestruct "Hptsto'" as "[Hptsto' Hprop']".
      iDestruct ("Hprop'" $! pn with "[] Hcom") as "Hptsto2".
      { iPureIntro. lia. }
      iDestruct "Hptsto" as "[Hptsto Hprop]".
      iDestruct (ghost_map_elem_agree with "Hptsto Hptsto2") as %Heq.
      replace (c) with (c') by naive_solver.
      iFrame "#".
      iMod ("Hclose" with "[]"); last done.
      iRight.
      iExists _; iFrame "#".
    }
  }
Qed.

(* Choosing proposals; this is where the real heavy-lifting will be *)
Lemma key_fact2 γ pn pn' c :
  pn' < pn →
  pn_undec γ pn -∗
  pn_ptsto γ pn' c -∗
  □(∀ pn'', ⌜pn' < pn''⌝ → ⌜pn'' < pn⌝ → committed γ pn'' -∗ False) ==∗
  pn_ptsto γ pn c
.
Proof.
  iIntros (Hineq) "Hpn #Hptsto #Hrej".
  iMod (ghost_map_update (Some c) with "[] Hpn") as "[_ Hpn]".
  { admit. }
  iMod (ghost_map_elem_persist with "Hpn") as "#Hpn".
  iFrame "Hpn".

  iModIntro. iModIntro.
  unfold pn_prop.
  iIntros (pm' Hmineq) "Hcom'".
  (* case 1: pm' < pn' *)
  assert (pm' <= pn' ∨ pn' < pm') as [Hcase|Hcase] by lia.
  (* TODO: missing pm' = pn' case *)
  {
    iDestruct "Hptsto" as "[Hptsto Hprop]".
    iDestruct ("Hprop" with "[] Hcom'") as "$".
    { done. }
  }
  {
    assert (pm' = pn ∨ pm' < pn) as [Hcase2|Hcase2] by lia.
    { (* equality case; we already have ghost state for that *)
      rewrite Hcase2.
      iFrame "#".
    }

    iSpecialize ("Hrej" $! pm' with "[] [] Hcom'").
    { done. }
    { done. }
    done.
  }
Admitted. (* FIXME: don't use ghost_map, because we don't want an auth *)

End replica_ghost.
