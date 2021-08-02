From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From Perennial.base_logic.lib Require Import wsat invariants ae_invariants saved_prop.
From Perennial.Helpers Require Import Qextra.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_weakestpre ae_invariants_mutable later_res private_invariants staged_invariant_alt wpc_nval wp_nval.

Existing Instances pri_inv_tok_timeless later_tok_timeless.

Section def.
Context `{IRISG: !irisGS Λ Σ}.
Context `{!pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.

Lemma staged_inv_wp_nval E P Qs Qs' R :
  staged_value ⊤ Qs P -∗
  ▷ (Qs -∗ wp_nval E (□ (Qs' -∗ P) ∗ Qs' ∗ R)) -∗
  wp_nval E (R ∗ staged_value ⊤ Qs' P).
Proof.
  iIntros "Hstaged Hwand".
  rewrite /wp_nval.
  iIntros (mj q g1 ns D κs) "Hg HNC".
  iDestruct "Hstaged" as (??????) "(Hown&Hownstat&#Hsaved1&#Hsaved2&Hltok&Hitok&Hinv)".
  iDestruct "Hinv" as (mj_wp_init mj_ishare Hlt) "#Hinv".
  rewrite /staged_inv.
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
  iApply (step_fupd2N_le).
  { apply le_n_S. apply (num_laters_per_step_exp ns'). lia. }
  iApply (step_fupd2N_le (S (S (S (num_laters_per_step ns'))))).
  { lia. }
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
  iModIntro. simpl. iModIntro. iNext.
  simpl.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
  iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".
  iModIntro. iModIntro. iModIntro.
  iDestruct "Hinner" as "[(HPs&_)|Hfin]"; last first.
  { (* Impossible, since we have NC token. *)
    iDestruct "Hfin" as "(_&HC&_)". iDestruct (NC_C with "[$] [$]") as %[]. }
  iRewrite -"Hequiv1" in "HPs".
  iMod "Hclo'".

  iDestruct (pri_inv_tok_global_valid with "Hg") as %(Hmin&Hvalid).
  destruct (Qp_plus_inv_2_gt_1_split mj) as (mj_ukeep&mj_ushare&Heq_mj&Hinvalid); first auto.
  set (mj_wp := (mj_wp_init `min` mj `min` (/2 + mj_ishare) `min` (/2 + mj_ushare))%Qp).
  assert (/ 2 < mj_wp)%Qp.
  {
    - rewrite /mj_wp. apply Qp_min_glb1_lt; auto.
      * apply Qp_min_glb1_lt; auto.
        ** apply Qp_min_glb1_lt; auto.
        ** apply Qp_lt_add_l.
      * apply Qp_lt_add_l.
  }
  iDestruct (pri_inv_tok_global_le_acc _ _ _ mj_wp with "[] Hg") as "(Hg_inv&Hg_inv_clo)".
  { iPureIntro; split; auto.
    rewrite /mj_wp.
    etransitivity; first eapply Qp_le_min_l.
    etransitivity; first eapply Qp_le_min_l.
    apply Qp_le_min_r.
  }

  iDestruct (pri_inv_tok_join with "[$Hitok] [$]") as "Hitok".
  iDestruct (pri_inv_tok_le_acc mj_wp with "Hitok") as "(Hitok_wp&Hitok_inv_clo)".
  { rewrite /mj_wp.
    etransitivity; first eapply Qp_le_min_l.
    apply Qp_le_min_r. }


  iMod (pri_inv_tok_disable_reenable with "[$]") as "(Hg&Hreenable)".
  iSpecialize ("Hwand" with "[$]").
  replace (⊤ ∖ D ∖ E2) with (⊤ ∖ (E2 ∪ D)) by set_solver.
  iMod ("Hwand" with "[$] [$]") as "Hwp".
  simpl. iModIntro.
  iApply (step_fupd2N_wand with "Hwp"). iNext. iIntros "Hwp".
  iMod ("Hwp") as "(Hg&(#Hshift&HQs'&HR)&HNC)".
  iMod (later_tok_incr with "[$]") as "(Hg&Hltok)".
    iMod (saved_prop_alloc Qs') as (γprop_stored') "#Hsaved1''".
    iMod (saved_prop_alloc True%I) as (γprop_remainder') "#Hsaved2''".
    iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                              ◯ Excl' (γprop_stored', γprop_remainder'))
            with "Hown' Hown") as "[Hown' Hown]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    iMod (own_update_2 _ _ _ (● Excl' idle ⋅ ◯ Excl' idle)
            with "Hstatus' Hownstat") as "[Hstatus' Hownstat]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    iMod ("Hreenable" with "[$Hg //]") as "(Hitok&Hg)".
    iDestruct ("Hitok_inv_clo" with "[$]") as "Hitok".
    iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok_u&Hitok_ishare)".
    iMod ("Hclo" with "[Hown' Hstatus' HQs' Hshift Hitok_ishare]").
    { iNext.
      iEval (rewrite staged_inv_inner_unfold).
      iExists _, _, _, _, _. iFrame "∗ #".
      iLeft. iSplit; first by iFrame "∗".
      iIntros. iDestruct ("Hshift" with "[$]") as "$"; eauto.
    }
    iDestruct ("Hg_inv_clo" with "Hg") as "Hg".
    iMod (global_state_interp_le with "Hg") as "$".
    { lia. }
    iModIntro. iFrame.
    iExists _, _, _, _, _, _. iFrame "∗ #".
    iExists _, _. iFrame "#"; eauto.
Qed.

End def.
