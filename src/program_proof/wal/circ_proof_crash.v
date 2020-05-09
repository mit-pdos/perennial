From iris.bi.lib Require Import fractional.
From Perennial.algebra Require Import deletable_heap.
From Perennial.algebra Require Import fmcounter.

From RecordUpdate Require Import RecordSet.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.Helpers Require Import Transitions.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.Helpers Require Import NamedProps.
From Perennial.program_proof Require Import proof_prelude disk_lib.
From Perennial.program_proof Require Import wal.lib.
From Perennial.program_proof Require Import marshal_proof util_proof.
From Perennial.program_proof Require Import circ_proof.


Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!circG Σ}.

Context (N: namespace).
Context (P: circΣ.t -> iProp Σ).

(* XXX: this instance seems dangerous, I don't want it to get picked up for an l ↦ v, for example.
  But it seems not to since those definitions are sealed. *)
Local Instance own_into_crash {A} `{inG Σ A} (γ: gname) (x: A):
  IntoCrash (own γ x) (λ _, own γ x).
Proof.
  rewrite /IntoCrash. iApply post_crash_nodep.
Qed.

Instance  is_circular_state_durable γ (σ : circΣ.t):
  IntoCrash (is_circular_state γ σ) (λ _, is_circular_state γ σ).
Proof. apply _. Qed.

Lemma is_circular_post_crash γ P' :
  (∀ s, IntoCrash (▷ P s) (P' s)) →
  is_circular N P γ ={↑N, ∅}=∗ post_crash (λ hG, ∃ σ, is_circular_state γ σ ∗ P' σ hG).
Proof.
  iIntros (?) "His".
  rewrite /is_circular.
  iInv "His" as "Hinner" "Hclo".
  iDestruct "Hinner" as (σ) "(>His&HP)".
  rewrite difference_diag_L.
  iModIntro. iCrash. iExists _. iFrame.
Qed.

End heap.
