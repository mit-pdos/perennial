From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__GetLeader (gcoord : loc) addrm rk ts gid γ :
    is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__GetLeader #gcoord
    {{{ (leader : u64), RET #leader; ⌜leader ∈ dom addrm⌝ }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    iNamed "Hgcoord". iNamed "Hleader".
    do 2 wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗ %". }
    wp_pures.
    iNamed "Haddrm".
    wp_loadField.
    iMod (readonly_load with "Hrps") as (q) "Hrpsro".
    assert (is_Some (rps !! uint.nat idxleader)) as [leader Hlead].
    { apply lookup_lt_is_Some.
      assert (length rps = size (dom addrm)); last word.
      by rewrite Hdomaddrm size_list_to_set.
    }
    wp_apply (wp_SliceGet with "[$Hrpsro]").
    { done. }
    iIntros "_".
    iApply "HΦ".
    iPureIntro.
    apply list_elem_of_lookup_2 in Hlead.
    by rewrite Hdomaddrm elem_of_list_to_set.
  Qed.

End program.
