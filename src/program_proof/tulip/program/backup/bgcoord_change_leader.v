From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__ChangeLeader (gcoord : loc) addrm rk ts gid γ :
    is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__ChangeLeader #gcoord
    {{{ (leader : u64), RET #leader; ⌜leader ∈ dom addrm⌝ }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    iNamed "Hgcoord". iNamed "Hleader".
    iNamed "Haddrm".
    do 2 wp_loadField.
    wp_apply wp_slice_len.
    wp_storeField.
    iMod (readonly_load with "Hrps") as (q) "Hrpsro".
    iDestruct (own_slice_small_sz with "Hrpsro") as %Hlenrps.
    wp_loadField.
    set idxleader' := word.modu _ _.
    assert (Hltrps : (uint.nat idxleader' < length rps)%nat).
    { assert (size (dom addrm) = length rps) as Hszaddrm.
      { by rewrite Hdomaddrm size_list_to_set. }
      rewrite word.unsigned_modu_nowrap; [word | lia].
    }
    wp_apply (wp_Mutex__Unlock with "[-HΦ Hrpsro]").
    { iFrame "Hlock Hlocked ∗ %".
      iPureIntro. simpl.
      rewrite Hdomaddrm size_list_to_set; [lia | done].
    }
    wp_pures.
    wp_loadField.
    assert (is_Some (rps !! uint.nat idxleader')) as [leader Hlead].
    { by apply lookup_lt_is_Some. }
    wp_apply (wp_SliceGet with "[$Hrpsro]").
    { done. }
    iIntros "_".
    iApply "HΦ".
    apply list_elem_of_lookup_2 in Hlead.
    by rewrite Hdomaddrm elem_of_list_to_set.
  Qed.

End program.
