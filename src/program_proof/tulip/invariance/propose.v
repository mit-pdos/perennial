From Perennial.program_proof.tulip Require Import prelude.

Section propose.
  Context `{!tulip_ghostG Σ}.

  Lemma group_inv_propose γ gid ts rk p :
    rk ≠ O ->
    safe_proposal γ gid ts rk p -∗
    exclusive_proposal γ gid ts rk -∗
    group_inv γ gid ==∗
    group_inv γ gid ∗
    is_group_prepare_proposal γ gid ts rk p.
  Proof.
    iIntros (Hnz) "#Hsafepsl Hexcl Hgroup".
    do 2 iNamed "Hgroup". iNamed "Hpsm".
    destruct (psm !! ts) as [ps |] eqn:Hpsmts; last first.
    { (* Case: [psm !! ts = None]. *)
      iMod (group_prepare_proposal_init ts with "Hpsm") as "Hpsm".
      { apply Hpsmts. }
      iMod (group_prepare_proposal_insert ts _ rk p with "Hpsm") as "Hpsm".
      { by rewrite lookup_insert_eq. }
      { done. }
      rewrite insert_empty insert_insert_eq.
      iDestruct (group_prepare_proposal_witness ts _ rk p with "Hpsm") as "#Hpsl".
      { by rewrite lookup_insert_eq. }
      { by rewrite lookup_singleton_eq. }
      iFrame "∗ # %".
      iModIntro.
      iSplit.
      { iApply (big_sepM_insert_2 with "[Hexcl] Hfresh").
        by rewrite /exclusive_proposals dom_singleton_L big_sepS_singleton.
      }
      iSplit.
      { iApply big_sepM_insert_2; last done.
        by rewrite /safe_proposals big_sepM_singleton.
      }
      iPureIntro.
      by apply map_Forall_insert_2; first rewrite lookup_insert_ne.
    }
    (* Case: [psm !! ts = Some ps]. *)
    (* Prove freshness of rank [rk] in [ps]. *)
    destruct (ps !! rk) as [b |] eqn:Hfresh.
    { iDestruct (big_sepM_lookup with "Hfresh") as "Hexcls"; first apply Hpsmts.
      apply elem_of_dom_2 in Hfresh.
      iDestruct (big_sepS_elem_of with "Hexcls") as "Hexcl'"; first apply Hfresh.
      iDestruct (exclusive_proposal_excl with "Hexcl Hexcl'") as %[].
    }
    iMod (group_prepare_proposal_insert ts _ rk p with "Hpsm") as "Hpsm".
    { apply Hpsmts. }
    { apply Hfresh. }
    iDestruct (group_prepare_proposal_witness ts _ rk p with "Hpsm") as "#Hpsl".
    { by rewrite lookup_insert_eq. }
    { by rewrite lookup_insert_eq. }
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { rewrite -insert_delete_eq.
      iDestruct (big_sepM_delete with "Hfresh") as "[Hfreshts Hfresh]".
      { apply Hpsmts. }
      iApply (big_sepM_insert_2 with "[Hfreshts Hexcl] Hfresh").
      rewrite /exclusive_proposals dom_insert_L.
      iApply (big_sepS_insert_2 with "Hexcl Hfreshts").
    }
    iSplit.
    { iApply big_sepM_insert_2; last done.
      iDestruct (big_sepM_lookup with "Hsafepsm") as "Hsafeps".
      { apply Hpsmts. }
      by iApply big_sepM_insert_2.
    }
    iPureIntro.
    apply map_Forall_insert_2; last done.
    rewrite lookup_insert_ne; last done.
    by specialize (Hzunused _ _ Hpsmts).
  Qed.

End propose.
