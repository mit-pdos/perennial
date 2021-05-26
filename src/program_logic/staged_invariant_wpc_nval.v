From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From Perennial.base_logic.lib Require Import wsat invariants ae_invariants saved_prop.
From Perennial.Helpers Require Import Qextra.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_weakestpre ae_invariants_mutable later_res private_invariants staged_invariant_alt wpc_nval.

Existing Instances pri_inv_tok_timeless later_tok_timeless.

Section def.
Context `{IRISG: !irisGS Λ Σ}.
Context `{!pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.

Lemma staged_inv_wpc_nval E P Qs Qs' R :
  staged_value ⊤ Qs P -∗
  ▷ (Qs -∗ |NC={E}=> □ (Qs' -∗ P) ∗ Qs' ∗ R) -∗
  wpc_nval E (R ∗ staged_value ⊤ Qs' P).
Proof.
  iIntros "Hstaged Hwand".
  rewrite /wpc_nval.
  iIntros (E' e s k Φ Φc Hnval Hsub) "Hwp".
  iDestruct "Hstaged" as (??????) "(Hown&Hownstat&#Hsaved1&#Hsaved2&Hltok&Hitok&Hinv)".
  iDestruct "Hinv" as (mj_wp_init mj_ishare Hlt) "#Hinv".
  rewrite /staged_inv.
  rewrite wpc_eq /wpc_def. iIntros (mj).

  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre. iSplit; last first.
  {
    iSpecialize ("Hwp" $! mj). rewrite wpc0_unfold /wpc_pre.
    iDestruct "Hwp" as "(_&Hwp)".
    iIntros (g1 ns D' κs) "Hg #HC".
    iSpecialize ("Hwp" with "[$] [$]").
    iApply (step_fupd2N_inner_wand with "Hwp"); auto.
  }
  rewrite Hnval.
  iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC".
  iDestruct (pri_inv_tok_disj_inv_half with "[$]") as %Hdisj.
  iMod (pri_inv_acc with "[$]") as "(Hinner&Hclo)".
  { set_solver. }
  iEval (rewrite staged_inv_inner_unfold) in "Hinner".
  iDestruct "Hinner" as (?????) "(>Hown'&#Hsaved1'&#Hsaved2'&>Hstatus'&>Hitok_ishare&Hinner)".
  iDestruct (own_valid_2 with "Hown' Hown") as "#H".
  iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  iDestruct (own_valid_2 with "Hstatus' Hownstat") as "#Heq_status".
  iDestruct "Heq_status" as %[Heq_status%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  inversion Heq; subst.
  iMod (later_tok_decr with "[$]") as (ns' Hlt') "Hg".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
  iModIntro. simpl. iModIntro. iNext. iModIntro. iApply (step_fupd2N_le (S (S (num_laters_per_step ns')))).
  { etransitivity; last eapply (num_laters_per_step_exp ns'); lia. }
  simpl.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
  iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".
  iModIntro. iModIntro. iModIntro.
  iDestruct "Hinner" as "[(HPs&_)|Hfin]"; last first.
  { (* Impossible, since we have NC token. *)
    iDestruct "Hfin" as "(_&HC&_)". iDestruct (NC_C with "[$] [$]") as %[]. }
  iRewrite -"Hequiv1" in "HPs".
  iMod "Hclo'".
  iSpecialize ("Hwand" with "[$]").
  rewrite ncfupd_eq /ncfupd_def. iSpecialize ("Hwand" with "[$]").
  iPoseProof (fupd_fupd2 with "Hwand") as "Hwand".
  iMod (fupd2_mask_mono with "Hwand") as "((#Hwand&HQs'&HR)&HNC)"; eauto.
 
  iSpecialize ("Hwp" $! mj). rewrite wpc0_unfold /wpc_pre.
  rewrite Hnval. iDestruct "Hwp" as "(Hwp&_)".
  iMod (saved_prop_alloc Qs') as (γprop_stored') "#Hsaved1''".
  iMod (saved_prop_alloc True%I) as (γprop_remainder') "#Hsaved2''".
  iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                              ◯ Excl' (γprop_stored', γprop_remainder'))
              with "Hown' Hown") as "[Hown' Hown]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod ("Hclo" with "[Hown' Hstatus' HQs' Hitok_ishare]").
  { iNext.
    iEval (rewrite staged_inv_inner_unfold).
    iExists _, _, _, _, _. iFrame "∗ #".
    iLeft.
    iSplit; eauto.
    { iIntros. iDestruct ("Hwand" with "[$]") as "$". eauto. }
  }
  iMod ("Hwp" with "[$] [$] [$]") as "H".
  iApply (step_fupd2N_wand with "H").
  iIntros "($&H)".
  iIntros.
  iMod ("H" with "[//]") as "($&Hg&Hwpc0&$)".
  iMod (later_tok_incr with "[$]") as "(Hg&Hltok)".
  iMod (global_state_interp_le with "Hg") as "$".
  { apply lt_le_S, step_count_next_mono; lia. }
  iModIntro.
  iApply (wpc0_strong_mono with "Hwpc0"); auto.
  iSplit.
  { iIntros (?) "H". iDestruct ("H" with "[-]") as "H".
    { iFrame. iExists _, _, _, _, _, _. iFrame "# ∗".
      iExists _, _. iFrame "#". eauto. }
    iFrame. eauto. }
  eauto.
Qed.

End def.
