From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__keyToGroup (txn : loc) (key : byte_string) q wrs :
    valid_key key ->
    {{{ own_txn_wrs txn q wrs }}}
      Txn__keyToGroup #txn #(LitString key)
    {{{ (gid : u64), RET #gid; own_txn_wrs txn q wrs ∗ ⌜key_to_group key = gid⌝ }}}.
  Proof.
    iIntros (Hvk Φ) "Htxn HΦ".
    wp_rec.

    (*@ func (txn *Txn) keyToGroup(key string) uint64 {                         @*)
    (*@     return uint64(len(key)) % uint64(len(txn.gcoords))                  @*)
    (*@ }                                                                       @*)
    iNamed "Htxn".
    wp_loadField.
    iNamed "Hwrs".
    wp_apply (wp_MapLen with "HpwrsmP").
    iIntros "[%Hnoof HpwrsmP]".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ %".
    iPureIntro.
    rewrite /key_to_group.
    rewrite -size_dom Hdomwrs.
    pose proof size_gids_all as Hszall.
    set x := length key.
    set y := size gids_all.
    apply valid_key_length in Hvk.
    word with (rewrite -> !wrap_small in H by word).
  Qed.

End program.
