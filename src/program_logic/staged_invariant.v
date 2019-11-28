From iris.algebra Require Import gmap auth agree gset coPset excl.
From iris.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Import wsat invariants saved_prop.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Class stagedG (Σ : gFunctors) : Set := WsatG {
  staging_saved_inG :> savedPropG Σ;
  staging_auth_inG :> inG Σ (authR (optionUR (exclR gnameO)));
}.

Definition staged_inv `{!invG Σ, !stagedG Σ} (N: namespace) (γ: gname) (Q: iProp Σ) : iProp Σ :=
  (inv N (∃ γprop P, own γ (● Excl' γprop) ∗ saved_prop_own γprop P ∗ P ∗ □ (P -∗ Q)))%I.

Definition staged_value `{!stagedG Σ} (N: namespace) (γ: gname) (Q: iProp Σ) : iProp Σ :=
  (∃ γprop, own γ (◯ Excl' γprop) ∗ saved_prop_own γprop Q)%I.

Section inv.
Context `{!invG Σ, !stagedG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

Global Instance staged_contractive N γ : Contractive (staged_inv N γ).
Proof. rewrite /staged_inv. solve_contractive. Qed.

Global Instance staged_ne N γ : NonExpansive (staged_inv N γ).
Proof. apply contractive_ne, _. Qed.

Global Instance staged_proper N γ : Proper ((⊣⊢) ==> (⊣⊢)) (staged_inv N γ).
Proof. apply ne_proper, _. Qed.

Global Instance staged_persistent N γ P : Persistent (staged_inv N γ P).
Proof. rewrite /staged_inv. apply _. Qed.

Lemma staged_inv_iff N γ P Q : ▷ □ (P ↔ Q) -∗ staged_inv N γ P -∗ staged_inv N γ Q.
Proof.
  iIntros "#HPQ". iApply inv_iff. iNext. iAlways. iSplit.
  - iIntros "H". iDestruct "H" as (? P0) "(?&?&?&#HP0)". iExists _, P0. iFrame.
    iAlways. iIntros. iApply "HPQ". by iApply "HP0".
  - iIntros "H". iDestruct "H" as (? P0) "(?&?&?&#HP0)". iExists _, P0. iFrame.
    iAlways. iIntros. iApply "HPQ". by iApply "HP0".
Qed.

Lemma staged_inv_alloc N E P Q: ▷ Q ∗ □ (Q -∗ P) ={E}=∗ ∃ γ, staged_inv N γ P ∗ staged_value N γ Q.
Proof.
  iMod (saved_prop_alloc Q) as (γprop) "#Hsaved".
  iMod (own_alloc (● (Excl' γprop) ⋅ ◯ (Excl' γprop))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iIntros "HP".
  iMod (inv_alloc N E _ with "[HP H1]") as "HI"; last first.
  { iModIntro. iExists γ. iSplitL "HI".
    - iApply "HI".
    - iExists γprop. by iFrame.
  }
  iNext. iExists γprop, Q. iFrame. auto.
Qed.


Lemma staged_inv_open E N γ P Q:
  ↑N ⊆ E → staged_inv N γ P ∗ staged_value N γ Q
           ={E,E∖↑N}=∗ ▷ ▷ Q ∗ (∀ Q', ▷ Q' ∗ □ (Q' -∗ P) ={E∖↑N,E}=∗ staged_value N γ Q').
Proof.
  iIntros (?) "(#Hinv&Hval)".
  iDestruct "Hval" as (γprop) "(Hγ&#Hsaved)".
  iInv N as (γprop' Qsaved) "H" "HC".
  iDestruct "H" as "(>Hγ'&#Hsaved'&HQ0&#Himp)".
  iDestruct (own_valid_2 with "Hγ' Hγ") as "#H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  iSplitL "HQ0".
  - iModIntro. iNext. iDestruct (saved_prop_agree with "Hsaved Hsaved'") as "Hequiv".
    iNext. by iRewrite "Hequiv".
  - iModIntro. iIntros (Q'). iIntros "(HQ'&#HQ'impl)".
    iMod (saved_prop_alloc Q') as (γprop_new) "#Hsaved_new".
    iMod (own_update_2 _ _ _ (● Excl' γprop_new ⋅ ◯ Excl' γprop_new) with "Hγ' Hγ") as "[Hγ' Hγ]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    iMod ("HC" with "[HQ' Hγ']").
    * iNext. iExists _, _. iFrame "#". iFrame.
    * iModIntro. iExists _. by iFrame.
Qed.

Lemma staged_inv_weak_open E N γ P:
  ↑N ⊆ E → staged_inv N γ P ={E,E∖↑N}=∗ ▷ P.
Proof.
  iIntros (?) "#Hinv".
  iInv N as (γprop' Qsaved) "H" "HC".
  iDestruct "H" as "(>Hγ'&#Hsaved'&HQ0&#Himp)".
  iModIntro. iNext. iApply "Himp". eauto.
Qed.

Global Instance into_inv_staged_inv1 N γ P : IntoInv (staged_inv N γ P) N := {}.

Definition staged_inv_exact N Pweak P :=
  (∃ γ, staged_inv N γ Pweak ∗ staged_value N γ P)%I.

(*
Global Instance into_acc_inv E N γ Pweak P :
  IntoAcc (staged_inv_exact N γ Pweak P)
          (↑N ⊆ E) True (fupd E (E∖↑N)) (fupd (E∖↑N) E)
          (λ _, ▷ ▷ P)%I (λ Q, Q ∗ ▷ P)%I (λ Q, Some (staged_value N γ Q))%I.
Proof.
  rewrite /IntoAcc /accessor.
  iIntros (?) "(#Hinv&Hvalue) _". iMod (staged_inv_open with "[Hvalue]") as "($&?)"; first done.
  { by iFrame. }
  simpl default.
  { auto.

  i

                                                                 Apply inv_open; done.
Qed.

Lemma inv_open_timeless E N P `{!Timeless P} :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ True).
Proof.
  iIntros (?) "Hinv". iMod (inv_open with "Hinv") as "[>HP Hclose]"; auto.
  iIntros "!> {$HP} HP". iApply "Hclose"; auto.
Qed.
*)

End inv.
