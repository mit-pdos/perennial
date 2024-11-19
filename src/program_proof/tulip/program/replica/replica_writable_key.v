From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition key_writable_ptsm (ptsm : gmap dbkey nat) (key : dbkey) :=
    match ptsm !! key with
    | Some pts => pts = O
    | _ => False
    end.

  Definition key_writable_sptsm (sptsm : gmap dbkey nat) (ts : nat) (key : dbkey) :=
    match sptsm !! key with
    | Some spts => (spts < ts)%nat
    | _ => False
    end.

  Definition key_writable (ptsm sptsm : gmap dbkey nat) (ts : nat) (key : dbkey) :=
    key_writable_ptsm ptsm key ∧ key_writable_sptsm sptsm ts key.

  Theorem wp_Replica__writableKey rp (ts : u64) key ptsm sptsm :
    key ∈ keys_all ->
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__writableKey #rp #ts #(LitString key)
    {{{ (ok : bool), RET #ok;
        own_replica_ptsm_sptsm rp ptsm sptsm ∗
        ⌜if ok then key_writable ptsm sptsm (uint.nat ts) key else True⌝
    }}}.
  Proof.
    iIntros (Hkey Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) writableKey(ts uint64, key string) bool {            @*)
    (*@     // The default of prepare timestamps are 0, so no need to check existence. @*)
    (*@     pts := rp.ptsm[key]                                                 @*)
    (*@     if pts != 0 {                                                       @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapGet with "HptsmM").
    iIntros (pts okpts) "[%Hpts HptsmM]".
    wp_pures.
    case_bool_decide as Hptsz; wp_pures; last first.
    { iApply "HΦ". by iFrame. }

    (*@     // Even though the default of smallest preparable timestamps are 1, using @*)
    (*@     // the fact that @ts is positive also means no need to check existence. @*)
    (*@     spts := rp.sptsm[key]                                               @*)

    (*@     if ts <= spts {                                                     @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapGet with "HsptsmM").
    iIntros (spts okspts) "[%Hspts HsptsmM]".
    wp_pures.
    case_bool_decide as Hgespts; wp_pures.
    { iApply "HΦ". by iFrame "HptsmP HsptsmP ∗". }

    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    assert (Hwritable : key_writable ptsm sptsm (uint.nat ts) key).
    { inv Hptsz.
      split.
      { specialize (Hptsmabs _ Hkey).
        destruct okpts.
        { apply map_get_true in Hpts.
          rewrite Hpts uint_nat_W64_0 in Hptsmabs.
          by rewrite /key_writable_ptsm Hptsmabs.
        }
        apply map_get_false in Hpts as [Hpts _].
        rewrite Hpts in Hptsmabs.
        by rewrite /key_writable_ptsm Hptsmabs.
      }
      { specialize (Hsptsmabs _ Hkey).
        destruct okspts.
        { apply map_get_true in Hspts.
          rewrite Hspts in Hsptsmabs.
          rewrite /key_writable_sptsm Hsptsmabs.
          clear -Hgespts. word.
        }
        apply map_get_false in Hspts as [Hspts _].
        rewrite Hspts in Hsptsmabs.
        rewrite /key_writable_sptsm Hsptsmabs.
        clear -Hgespts. word.
      }
    }
    by iFrame "HptsmP HsptsmP ∗".
  Qed.

End program.
