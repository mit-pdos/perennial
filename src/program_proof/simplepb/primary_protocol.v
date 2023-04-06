From Perennial.program_proof Require Import grove_prelude.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list csum.
From Perennial.program_proof.simplepb Require Import pb_protocol.

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
    primary_ghost_map_logG :> fmlist_mapG Σ u64 EntryType;
    primary_escrowG :> inG Σ (gmapR u64 (dfrac_agreeR unitO))
}.

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
  own γsrv.(prim_escrow_gn) {[ epoch := to_dfrac_agree (DfracOwn 1) ()]}.

Definition is_tok γsrv epoch : iProp Σ :=
  own γsrv.(prim_escrow_gn) {[ epoch := to_dfrac_agree (DfracDiscarded) ()]}.

Definition is_proposal_facts_prim γ epoch σ: iProp Σ :=
  is_init_proposal_ub γ epoch σ
.

Definition own_escrow_toks γsrv epoch : iProp Σ :=
  [∗ set] epoch' ∈ (fin_to_set u64), ⌜int.nat epoch' ≤ int.nat epoch⌝ ∨ own_tok γsrv epoch'
.

Definition own_primary_escrow_ghost γsys γsrv (canBecomePrimary:bool) epoch : iProp Σ :=
  "Htoks" ∷ own_escrow_toks γsrv epoch ∗
  "Htok" ∷ (if canBecomePrimary then own_tok γsrv epoch else True)
.

Lemma ghost_primary_accept_new_epoch γsys γsrv epoch canBecomePrimary epoch' :
  int.nat epoch < int.nat epoch' →
  own_primary_escrow_ghost γsys γsrv canBecomePrimary epoch -∗
  own_primary_escrow_ghost γsys γsrv true epoch'.
Proof.
  intros Hineq.
  iNamed 1.
  iClear "Htok".
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
  iDestruct (own_valid_2 with "His Htok") as %Hbad.
  rewrite singleton_op singleton_valid dfrac_agree_op_valid in Hbad.
  naive_solver.
Qed.

Definition become_primary_escrow γsys γsrv epoch σ R : iProp Σ :=
  is_init_proposal γsys epoch σ ∗
  inv pbN (R ∨ is_tok γsrv epoch)
.

Lemma primary_ghost_init_primary R γsys γsrv σ epoch :
  own_init_proposal_unused γsys epoch -∗
  R
  ={↑pbN}=∗
  become_primary_escrow γsys γsrv epoch σ R ∗
  is_proposal_facts_prim γsys epoch σ
.
Proof.
  iIntros "Hinit HR".
  iMod (fmlist_ptsto_update σ with "Hinit") as "Hinit".
  { apply prefix_nil. }
  iMod (fmlist_ptsto_persist with "Hinit") as "#Hinit".
  iMod (inv_alloc with "[HR]") as "$".
  { iLeft. iFrame. }
  iModIntro.
  iFrame "#".
  iExists _; iFrame "#".
  done.
Qed.

Lemma ghost_become_primary γsys γsrv epoch σprop σ R :
  £ 1 -∗
  become_primary_escrow γsys γsrv epoch σprop R -∗
  is_proposal_facts_prim γsys epoch σ -∗
  own_primary_escrow_ghost γsys γsrv true epoch ={↑pbN}=∗
  ⌜σprop ⪯ σ⌝ ∗
  own_primary_escrow_ghost γsys γsrv false epoch ∗
  R
.
Proof.
  iIntros "Hlc #Hescrow #Hinit_ub".
  iNamed 1.
  iDestruct "Hescrow" as "[#Hinit Hescrow]".
  iInv "Hescrow" as "Hown" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hown" ) as "Hown".
  iDestruct "Hown" as "[HR|#His_primary]"; last first.
  { (* contradiction, since we still have the token *)
    iDestruct (own_valid_2 with "Htok His_primary") as %Hbad.
    exfalso.
    rewrite singleton_op singleton_valid dfrac_agree_op_valid in Hbad.
    destruct Hbad as [Hbad _].
    done.
  }

  iFrame "HR".
  iMod (own_update with "Htok") as "His_primary".
  {
    apply singleton_update.
    apply dfrac_agree_persist.
  }
  iDestruct "His_primary" as "#His_primary".
  iMod ("Hclose" with "[$His_primary]").
  iModIntro.

  iDestruct "Hinit_ub" as (?) "[%Hineq Hinit2]".
  iDestruct (fmlist_ptsto_agree with "Hinit Hinit2") as %Heq.
  subst.
  iSplitR; first done.
  iFrame.
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

End primary_protocol.
