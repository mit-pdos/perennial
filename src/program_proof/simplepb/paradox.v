From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Import state.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_apply_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From iris.algebra Require Import dfrac_agree mono_list.

Section paradox_proof.

Context `{!heapGS Σ}.
Context `{!inG Σ dfracR}.

Definition N := nroot.

Definition s (γ:gname) : iProp Σ := own γ (DfracOwn 1).
Definition f (γ:gname) : iProp Σ := own γ (DfracDiscarded).
Definition sprop γ P : iProp Σ :=
  inv N (s γ ∨ (f γ ∗ □ P)).

Lemma lemma_3 P :
  ⊢ |={⊤}=> ∃ γ, sprop γ P.
Proof.
  iIntros.
  iMod (own_alloc (DfracOwn 1)) as (?) "Hs".
  { done. }
  iExists _.
  iMod (inv_alloc with "[Hs]") as "$".
  {
    iNext.
    iLeft.
    iFrame.
  }
  done.
Qed.

Lemma lemma_4_a γ P Q :
  bi_entails
  (£ 1 ∗ sprop γ P ∗ sprop γ Q ∗ (□ P)) (|={⊤}=> (□ Q))
.
Proof.
  iIntros "(Hlc&#HsP&#HsQ&#HP)".
  iAssert (|={⊤}=> f γ)%I as "HH".
  {
    iInv "HsP" as "H" "Hclose".
    iDestruct "H" as "[>H|H]".
    {
      iMod (own_update with "H") as "H".
      { apply dfrac_discard_update. }
      iDestruct "H" as "#Hf".
      iFrame "Hf".
      iMod ("Hclose" with "[Hf HP]").
      { iRight. iNext. iFrame "#". }
      done.
    }
    {
      iDestruct "H" as "[>#Hf HP2]".
      iFrame "Hf".
      iMod ("Hclose" with "[Hf HP]").
      { iRight. iNext. iFrame "#". }
      done.
    }
  }

  iMod "HH" as "#Hf".
  iInv "HsQ" as "H" "Hclose".
  iDestruct "H" as "[>Hbad|H]".
  {
    iDestruct (own_valid_2 with "Hbad Hf") as %Hvalid.
    exfalso. done.
  }
  iMod (lc_fupd_elim_later with "Hlc H") as "#[Hf2 HQ]".
  iFrame "#".
  iMod ("Hclose" with "[Hf HQ]").
  { iRight. iNext. iFrame "#". }
  done.
Qed.

Definition neg P : iProp Σ := (P -∗ False).

Definition A γ : iProp Σ := ∃ (P:iProp Σ), □(neg P) ∧ sprop γ P.

Lemma lemma_2_a γ :
  bi_entails
  (sprop γ (A γ)) (□(neg (A γ))).
Proof.
  iIntros "#HsA".
  iModIntro.
  iIntros "#HA".
  iAssert (_) with "HA" as "HA2".
  iDestruct "HA2" as (P) "[HnotP HsP]".
  iDestruct (lemma_4_a with "[HsP HsA HA]") as "HH".
  {
    iFrame "".
  }
Qed.

Lemma lemma_2_b γ :
  bi_entails
  (sprop γ (A γ)) (A γ).
Proof.
Admitted.

Lemma paradox :
  {{{
        £ 1 ∗
        £ 1 ∗
  }}}
    () #()
  {{{
        RET #(); True
  }}}.

End paradox_proof.
