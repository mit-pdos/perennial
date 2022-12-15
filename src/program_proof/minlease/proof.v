From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.ffi Require Export grove_ffi_time_axiom.
From Perennial.base_logic.lib Require Import ghost_var.
From Goose.github_com.mit_pdos.gokv Require Import minlease.
From iris.bi.lib Require Import fixpoint.
From Perennial.base_logic Require Import lib.saved_prop.

Section proof.

Context `{!heapGS Σ}.
Context `{!ghost_varG Σ u64}.
Context `{!savedPropG Σ }.

Context {γtime:gname}.

Notation is_time_lb := (is_time_lb γtime).
Notation own_time := (own_time γtime).

(* Q is the lease obligation *)
Definition underLease (N:namespace) (leaseExpiration:u64) (P:iProp Σ) (Q:iProp Σ) : iProp Σ :=
  ∃ γprop,
  saved_prop_own γprop (DfracOwn (1/2)) P ∗
  inv N (∃ P',
    saved_prop_own γprop (DfracOwn (1/2)) P' ∗
    (P' ∗ (P' -∗ Q) ∨ is_time_lb leaseExpiration)
  ).

Lemma underLease_mono P' P Q e N :
  (P -∗ P') -∗
  (P' -∗ Q) -∗
  underLease N e P Q -∗
  underLease N e P' Q
.
Proof.
Admitted.

Lemma lease_acc_update N e P Q :
  underLease N e P Q -∗
  £ 1 -∗
  £ 1 -∗
  ∀ (t:u64),
  ⌜int.nat t < int.nat e⌝ →
  own_time t ={↑N,∅}=∗
  (P ∗ (∀ P', P' -∗ (P' -∗ Q) ={∅,↑N}=∗ own_time t ∗ underLease N e P' Q))
.
Proof.
  iIntros "Hlease Hlc Hlc2".
  iIntros (?) "%Hineq Htime".
  iDestruct "Hlease" as (γprop) "[Hprop #Hinv]".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iDestruct "Hi" as (?) "[Hprop2 Hi]".
  iDestruct (saved_prop_agree with "Hprop Hprop2") as "#Hagree1".
  iMod (lc_fupd_elim_later with "Hlc2 Hagree1") as "#Hagree".
  replace (↑N ∖ ↑N) with (∅:coPset) by set_solver.
  iModIntro.
  iDestruct "Hi" as "[[HP HQwand]| Hbad]"; last first.
  {
    iDestruct (mono_nat_lb_own_valid with "Htime Hbad") as %[_ Hbad].
    exfalso.
    word.
  }
  iSplitL "HP".
  {
    by iRewrite "Hagree".
  }
  iIntros (R) "HR HRwandQ".
  iMod (saved_prop_update_2 R with "Hprop Hprop2") as "[Hprop Hprop2]".
  { apply Qp.half_half. }
  iFrame "Htime".
  iMod ("Hclose" with "[HRwandQ HR Hprop2]").
  {
    iNext.
    iExists _; iFrame "Hprop2".
    iLeft.
    iFrame.
  }
  iModIntro.
  iExists _; iFrame "∗#".
Qed.

Definition postLease (N:namespace) (leaseExpiration:u64) (Q:iProp Σ) :=
  is_time_lb leaseExpiration ={↑N}=∗ Q
.

(* P are resources you can access and modify at the moment you check that the
   lease is unexpired.
 *)

Definition own_Server s γ : iProp Σ :=
  ∃ (v:u64) (leaseExpiration:u64),
  "Hval" ∷ s ↦[Server :: "val"] #v ∗
  "HleaseExpiration" ∷ s ↦[Server :: "leaseExpiration"] #leaseExpiration ∗
  "Hauth" ∷ ghost_var γ (1/2) v
.

Definition is_Server s γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock nroot mu (own_Server s γ)
.

Definition clientPre s γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock nroot mu (own_Server s γ)
.

End proof.
