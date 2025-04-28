From Perennial.program_proof Require Import grove_prelude.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list csum.
From Perennial.algebra Require Import map.
From Perennial Require Import replica.protocol.

Section primary_protocol.

Context `{EntryType}.

Record primary_system_names :=
{
  prim_init_proposal_gn : gname ;
}.

Record primary_server_names :=
{
  prim_escrow_gn : gname ; (* escrow for getting ownership of proposal *)
}.

Class primary_ghostG Σ := {
    #[global] primary_ghost_map_logG :: fmlist_mapG Σ u64 EntryType;
    #[global] primary_escrowG :: mapG Σ u64 unit;
}.

Definition primary_ghostΣ :=
  #[fmlist_mapΣ u64 EntryType; mapΣ u64 unit].
Global Instance subG_pbΣ {Σ} : subG (primary_ghostΣ) Σ → (primary_ghostG Σ).
Proof. solve_inG. Qed.

Context `{!primary_ghostG Σ}.
Context `{!gooseGlobalGS Σ}.

Implicit Type γsrv : primary_server_names.
Implicit Type γsys : primary_system_names.
Implicit Type σ : list EntryType.
Implicit Type epoch : u64.

Notation "lhs ⪯ rhs" := (prefix lhs rhs)
(at level 20, format "lhs  ⪯  rhs") : stdpp_scope.

(* FIXME: ideally, this init proposal stuff and the escrow tokens should be a
   separate higher-level protocol *)
Definition own_init_proposal_unused γsys epoch : iProp Σ :=
  epoch ⤳l[γsys.(prim_init_proposal_gn)] [].
Definition is_init_proposal γsys epoch σ : iProp Σ :=
  epoch ⤳l[γsys.(prim_init_proposal_gn)]□ σ.
Definition is_init_proposal_ub γsys epoch σ : iProp Σ :=
  ∃ σexact,
  ⌜σexact ⪯ σ⌝ ∗
  is_init_proposal γsys epoch σexact.

Definition own_tok γsrv epoch : iProp Σ :=
  epoch ⤳[γsrv.(prim_escrow_gn)] ().

Definition is_tok γsrv epoch : iProp Σ :=
  epoch ⤳[γsrv.(prim_escrow_gn)]□ ().

Definition is_proposal_facts_prim γ epoch σ: iProp Σ :=
  is_init_proposal_ub γ epoch σ
.

Definition own_escrow_toks γsrv epoch : iProp Σ :=
  [∗ set] epoch' ∈ (fin_to_set u64), ⌜uint.nat epoch' ≤ uint.nat epoch⌝ ∨ own_tok γsrv epoch'
.

Definition own_primary_escrow_ghost γsrv epoch : iProp Σ :=
  "Htoks" ∷ own_escrow_toks γsrv epoch
  (* "Htok" ∷ (if canBecomePrimary then own_tok γsrv epoch else True) *)
.

Lemma ghost_primary_accept_new_epoch γsrv epoch epoch' :
  uint.nat epoch < uint.nat epoch' →
  own_primary_escrow_ghost γsrv epoch -∗
  own_primary_escrow_ghost γsrv epoch' ∗ own_tok γsrv epoch'.
Proof.
  intros Hineq.
  iIntros "Htoks".
  iDestruct (big_sepS_elem_of_acc_impl epoch' with "Htoks") as "[Htok Htoks]".
  { set_solver. }
  iDestruct "Htok" as "[%Hbad|Htok]".
  { exfalso. word. }
  iFrame "Htok".
  iApply "Htoks".
  {
    iModIntro.
    iIntros (???) "[%Hineq2|$]".
    iLeft.
    iPureIntro.
    word.
  }
  { by iLeft. }
Qed.

Lemma own_tok_is_tok_false γ epoch :
  own_tok γ epoch -∗
  is_tok γ epoch -∗
  False.
Proof.
  iIntros "Htok His".
  iDestruct (ghost_map_points_to_valid_2 with "His Htok") as %Hbad.
  naive_solver.
Qed.

Definition become_primary_escrow γsys γsrv epoch σ R : iProp Σ :=
  is_init_proposal γsys epoch σ ∗
  inv pbN (R ∨ is_tok γsrv epoch)
.

Lemma primary_ghost_init_primary γsys σ epoch :
  own_init_proposal_unused γsys epoch ==∗
  is_init_proposal γsys epoch σ ∗
  is_proposal_facts_prim γsys epoch σ
.
Proof.
  iIntros "Hinit".
  iMod (fmlist_ptsto_update σ with "Hinit") as "Hinit".
  { apply prefix_nil. }
  by iMod (fmlist_ptsto_persist with "Hinit") as "#$".
Qed.

Lemma primary_ghost_init_primary_escrow R γsys γsrv σ epoch :
  is_init_proposal γsys epoch σ -∗
  R
  ={↑pbN}=∗
  become_primary_escrow γsys γsrv epoch σ R
.
Proof.
  iIntros "$ HR".
  iMod (inv_alloc with "[HR]") as "$".
  { iLeft. iFrame. }
  done.
Qed.

Lemma ghost_become_primary γsys γsrv epoch σprop σ R :
  £ 1 -∗
  become_primary_escrow γsys γsrv epoch σprop R -∗
  is_proposal_facts_prim γsys epoch σ -∗
  own_tok γsrv epoch ={↑pbN}=∗
  ⌜σprop ⪯ σ⌝ ∗
  R
.
Proof.
  iIntros "Hlc #Hescrow #Hinit_ub Htok".
  iDestruct "Hescrow" as "[#Hinit Hescrow]".
  iInv "Hescrow" as "Hown" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hown" ) as "Hown".
  iDestruct "Hown" as "[HR|#His_primary]"; last first.
  { by iDestruct (own_tok_is_tok_false with "Htok His_primary") as "?". }

  iFrame "HR".
  iMod (ghost_map_points_to_persist with "Htok") as "#His_primary".
  iMod ("Hclose" with "[$His_primary]").
  iModIntro.

  iDestruct "Hinit_ub" as (?) "[%Hineq Hinit2]".
  iDestruct (fmlist_ptsto_agree with "Hinit Hinit2") as %Heq.
  by subst.
Qed.

Lemma is_proposal_facts_prim_mono γ epoch σ σ' :
  σ ⪯ σ' →
  is_proposal_facts_prim γ epoch σ -∗
  is_proposal_facts_prim γ epoch σ'
.
Proof.
  intros.
  iIntros "(% & % & Hlb)".
  iExists _; iFrame.
  iPureIntro. by transitivity σ.
Qed.

Lemma own_unused_facts_false γ epoch σ :
  own_init_proposal_unused γ epoch -∗
  is_proposal_facts_prim γ epoch σ -∗
  False.
Proof.
  iIntros "? (% & (% & H))".
  iDestruct (fmlist_ptsto_valid_2 with "[$] [$]") as "[% _]".
  exfalso.
  done.
Qed.

Definition primary_init_for_config γ : iProp Σ :=
  ([∗ set] epoch' ∈ (fin_to_set u64), ⌜uint.nat 0 < uint.nat epoch'⌝
                                  → own_init_proposal_unused γ epoch')
.

Lemma alloc_primary_protocol :
  ⊢ |==> ∃ γ, primary_init_for_config γ ∗
              is_proposal_facts_prim γ 0 []
.
Proof.
  iMod (fmlist_map_alloc_fin []) as (?) "H".
  iExists {| prim_init_proposal_gn := γ |}.
  iDestruct (big_sepS_elem_of_acc_impl (W64 0) with "H") as "[Hprop H]".
  { set_solver. }
  iMod (fmlist_ptsto_persist with "Hprop") as "#?".
  iModIntro.
  iSplitL.
  { iApply "H".
    { iModIntro. iIntros. iFrame. }
    { iIntros. exfalso. replace (uint.nat (W64 0)) with 0 in H0 by word. word. }
  }
  by iExists _; iFrame "#".
Qed.

Lemma alloc_primary_protocol_server :
  ⊢ |==> ∃ γsrv, own_primary_escrow_ghost γsrv (W64 0)
.
Proof.
  iMod (ghost_map_alloc_fin ()) as (?) "H".
  iExists {| prim_escrow_gn := _ |}.
  iModIntro.
  iApply (big_sepS_impl with "H").
  iModIntro. iIntros. iFrame.
Qed.

End primary_protocol.
