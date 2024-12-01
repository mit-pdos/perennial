From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_attach.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__attach (txn : loc) ts γ :
    {{{ ([∗ set] gid ∈ gids_all, own_txn_client_token γ ts gid) ∗ own_txn_init txn ts γ }}}
      Txn__attach #txn
    {{{ RET #(); own_txn_init txn ts γ }}}.
  Proof.
    iIntros (Φ) "[Hctks Htxn] HΦ".
    wp_rec.

    (*@ func (txn *Txn) attach() {                                              @*)
    (*@     for _, gcoord := range(txn.gcoords) {                               @*)
    (*@         gcoord.Attach(txn.ts)                                           @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Htxn". iNamed "Hgcoords".
    wp_loadField.
    set P := (λ (mx : gmap u64 loc),
                "Hts"   ∷ own_txn_ts txn ts ∗
                "Hctks" ∷ [∗ set] gid ∈ gids_all ∖ (dom mx), own_txn_client_token γ ts gid)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Hgcoords [$Hts Hctks]").
    { subst P. simpl. by rewrite dom_empty_L difference_empty_L. }
    { clear Φ.
      iIntros (m g p Φ) "!> [HP %Hp] HΦ".
      destruct Hp as [Hnotin Hin].
      iNamed "HP". iNamed "Hts".
      wp_loadField.
      iDestruct (big_sepS_delete _ _ g with "Hctks") as "[Hctk Hctks]".
      { apply not_elem_of_dom_2 in Hnotin.
        apply elem_of_dom_2 in Hin.
        set_solver.
      }
      iDestruct (big_sepM_lookup with "Hgcoordsabs") as "Hgcoordabs".
      { apply Hin. }
      wp_apply (wp_GroupCoordinator__Attach with "Hgcoordabs [Hctk]").
      { by rewrite Htsword. }
      iApply "HΦ".
      iFrame "∗ %".
      by rewrite dom_insert_L difference_difference_l_L union_comm_L.
    }
    iIntros "[Hgcoords HP]".
    iNamed "HP".
    wp_pures.
    iApply "HΦ".
    iAssert (own_txn_gcoords txn γ)%I with "[Hgcoords HgcoordsP]" as "Hgcoords".
    { by iFrame "∗ # %". }
    by iFrame "∗ # %".
  Qed.

End program.
