From iris.bi.lib Require Import fractional.
From Perennial.algebra Require Import deletable_heap.

From RecordUpdate Require Import RecordSet.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.program_logic Require Import staged_wpc.
From Perennial.Helpers Require Import Transitions.
From Perennial.goose_lang Require Import crash_modality fmcounter.
From Perennial.Helpers Require Import NamedProps.
From Perennial.program_proof Require Import proof_prelude disk_lib.
From Perennial.program_proof Require Import wal.lib.
From Perennial.program_proof Require Import marshal_block util_proof.
From Perennial.program_proof Require Import circ_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.


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

Global Instance is_circular_state_durable γ (σ : circΣ.t):
  IntoCrash (is_circular_state γ σ) (λ _, is_circular_state γ σ).
Proof. apply _. Qed.

Lemma is_circular_state_post_crash σ γ P':
  (IntoCrash (P σ) (P' σ)) →
  is_circular_state γ σ ∗ P σ -∗ post_crash (λ hG, is_circular_state γ σ ∗ P' σ hG).
Proof. iIntros (?) "His". rewrite /is_circular. iCrash. eauto. Qed.

Lemma is_circular_post_crash γ P' :
  (∀ s, IntoCrash (P s) (P' s)) →
  is_circular N P γ ={↑N, ∅}=∗ ▷ post_crash (λ hG, ∃ σ, is_circular_state γ σ ∗ P' σ hG).
Proof.
  iIntros (?) "His".
  rewrite /is_circular.
  iInv "His" as "Hinner" "_".
  iDestruct "Hinner" as (σ) "(>His&HP)".
  rewrite difference_diag_L.
  iModIntro. iNext. iPoseProof (is_circular_state_post_crash with "[$]") as "H".
  iCrash. eauto.
Qed.

(* Once the circular buffer is initialized or recovered, the is_circular
   invariant can be allocated. By allocating that invariant, we no longer need
   to show is_circular_state γ σ ∗ P σ in the crash condition anymore, because at
   crash time we know that this will hold because it is in an invariant.

   This lemma encodes this principle.
 *)

Lemma circ_buf_crash_obligation e (Φ: val → iProp Σ) Φc Φc' E2 E2' k σ γ:
  E2 ⊆ E2' →
  ↑N ⊆ E2' ∖ E2 →
  is_circular_state γ σ  -∗
  P σ -∗
  □ ((∃ σ', is_circular_state γ σ' ∗ P σ') -∗ Φc -∗ Φc') -∗
  (is_circular N P γ -∗ (WPC e @ NotStuck; k; ⊤; E2 {{ Φ }} {{ Φc }})) -∗
  |={⊤}=> is_circular N P γ ∗ WPC e @ NotStuck; k; ⊤; E2' {{ Φ }} {{ Φc' }}%I.
Proof.
  iIntros (??) "Hstate HP #Hcrash1 HWP". rewrite /is_circular.
  iMod (inv_alloc N _ (∃ σ, is_circular_state γ σ ∗ P σ)%I with "[Hstate HP]") as "#Hinv".
  { iNext. iExists _. iFrame. }
  iFrame "Hinv".
  iModIntro.
  iApply (wpc_inv'); try eassumption. iFrame "Hinv".
  iSplitL "HWP".
  { by iApply "HWP". }
  iModIntro. iIntros "H HΦc".
  iApply ("Hcrash1" with "[$] [$]").
Qed.

(* Note: the version above is more usable, but this helps understand what it achieves *)
Lemma circ_buf_crash_obligation_simple e (Φ: val → iProp Σ) k σ γ:
  is_circular_state γ σ  -∗
  P σ -∗
  (is_circular N P γ -∗ (WPC e @ NotStuck; k; ⊤; ∅ {{ Φ }} {{ True }})) -∗
  |={⊤}=> is_circular N P γ ∗
          WPC e @ NotStuck; k; ⊤; ↑N {{ Φ }} {{ ∃ σ', is_circular_state γ σ' ∗ P σ' }}%I.
Proof.
  iIntros "Hstate HP HWP".
  iApply (circ_buf_crash_obligation with "[$] [$] [] [$]"); auto; set_solver+.
Qed.

End heap.
