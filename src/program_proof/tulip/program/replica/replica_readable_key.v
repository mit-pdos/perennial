From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition key_readable (ptsm : gmap dbkey nat) (ts : nat) (key : dbkey) :=
    match ptsm !! key with
    | Some pts => pts = O ∨ (ts < pts)%nat
    | _ => False
    end.

  Theorem wp_Replica__readableKey rp (ts : u64) key ptsm sptsm :
    key ∈ keys_all ->
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__readableKey #rp #ts #(LitString key)
    {{{ (ok : bool), RET #ok;
        own_replica_ptsm_sptsm rp ptsm sptsm ∗
        ⌜if ok then key_readable ptsm (uint.nat ts) key else True⌝
    }}}.
  Proof.
    iIntros (Hkey Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) readableKey(ts uint64, key string) bool {            @*)
    (*@     pts := rp.ptsm[key]                                                 @*)
    (*@     if pts != 0 && pts <= ts {                                          @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapGet with "HptsmM").
    iIntros (pts ok) "[%Hpts HptsmM]".
    wp_apply wp_and_pure.
    { wp_pures. by rewrite -bool_decide_not. }
    { iIntros (_). by wp_pures. }
    case_bool_decide as Hcond; wp_pures.
    { iApply "HΦ". by iFrame. }

    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    apply Classical_Prop.not_and_or in Hcond.
    assert (Hreadable : key_readable ptsm (uint.nat ts) key).
    { specialize (Hptsmabs _ Hkey).
      destruct ok.
      { apply map_get_true in Hpts.
        rewrite Hpts in Hptsmabs.
        rewrite /key_readable Hptsmabs.
        destruct Hcond as [Hz | Hlt].
        { left. apply dec_stable in Hz. inv Hz. by rewrite uint_nat_W64_0. }
        { right. clear -Hlt. word. }
      }
      apply map_get_false in Hpts as [Hpts _].
      rewrite Hpts in Hptsmabs.
      rewrite /key_readable Hptsmabs.
      by left.
    }
    by iFrame.
  Qed.

End program.
