From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import greader_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupReader__clearVersions (grd : loc) (key : byte_string) qreadm ts γ :
    {{{ own_greader_qreadm grd qreadm ts γ }}}
      GroupReader__clearVersions #grd #(LitString key)
    {{{ RET #(); own_greader_qreadm grd (delete key qreadm) ts γ }}}.
  Proof.
    iIntros (Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) clearVersions(key string) {                     @*)
    (*@     delete(grd.qreadm, key)                                             @*)
    (*@ }                                                                       @*)
    iNamed "Hgrd".
    wp_loadField.
    wp_apply (wp_MapDelete with "HqreadmM").
    iIntros "HqreadmM".
    wp_pures.
    iDestruct (big_sepM2_dom with "Hqreadm") as %Hdomqreadm.
    iApply "HΦ".
    destruct (decide (key ∈ dom qreadm)) as [Hin | Hnotin]; last first.
    { apply not_elem_of_dom in Hnotin.
      rewrite delete_id; last apply Hnotin.
      assert (Hnone : qreadmM !! key = None).
      { by rewrite -not_elem_of_dom Hdomqreadm not_elem_of_dom. }
      rewrite /map_del delete_id; last apply Hnone.
      by iFrame "∗ # %".
    }
    assert (is_Some (qreadmM !! key)) as [p Hp].
    { by rewrite -elem_of_dom Hdomqreadm. }
    apply elem_of_dom in Hin as [m Hm].
    iDestruct (big_sepM2_delete with "Hqreadm") as "[_ Hqreadm]".
    { apply Hp. }
    { apply Hm. }
    iDestruct (big_sepM_delete with "Hqread") as "[_ Hqread']".
    { apply Hm. }
    iFrame "∗ # %".
    iPureIntro.
    by apply map_Forall_delete.
  Qed.

End program.
