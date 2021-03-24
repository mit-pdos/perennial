From Perennial.Helpers Require Import Transitions.
From Perennial.base_logic Require Import base_logic lib.invariants.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.

Section simulation.
  Context `{!invG Σ}.
  Context {state: Type} (wf: state -> Prop) (P: state -> iProp Σ).
  Context (E: coPset).
  (* TODO: if we can start using this everywhere I think we can start proving
  generic theorems about simulation, like the one below *)
  Definition simulation_fupd {T} (tr: transition state T) (Q: T -> iProp Σ): iProp Σ :=
    (∀ σ σ' r,
         ⌜wf σ⌝ -∗
         ⌜relation.denote tr σ σ' r⌝ -∗
        (P σ ={E}=∗ P σ' ∗ ⌜wf σ'⌝ ∗ Q r)).

  Theorem simulation_bind_fupd {A B}
          (tr1: transition state A)
          (tr2: A -> transition state B)
          (Q: B -> iProp Σ) :
    simulation_fupd tr1 (fun x => simulation_fupd (tr2 x) Q) -∗
    simulation_fupd (bind tr1 tr2) Q.
  Proof.
    iIntros "Hfupd".
    iIntros (σ1 σ3 r Hwf Htr) "HP".
    simpl in Htr.
    inversion Htr; subst; clear Htr.
    rename s2 into σ2.
    iMod ("Hfupd" with "[] [] HP") as "(HP&%Hwf2&Hfupd2)"; eauto.
    iMod ("Hfupd2" with "[] [] HP") as "(HP&%Hwf3&HQ)"; eauto.
    iFrame.
    auto.
  Qed.
End simulation.
