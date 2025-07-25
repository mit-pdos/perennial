From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__bumpKey rp (ts : u64) key ptsm sptsm :
    uint.Z ts ≠ 0 ->
    key ∈ keys_all ->
    {{{ own_replica_ptsm_sptsm rp ptsm sptsm }}}
      Replica__bumpKey #rp #ts #(LitString key)
    {{{ (spts : nat), RET #(bool_decide (spts < pred (uint.nat ts))%nat);
        own_replica_ptsm_sptsm rp ptsm (<[key := (spts `max` pred (uint.nat ts))%nat]> sptsm) ∗
        ⌜sptsm !! key = Some spts⌝
    }}}.
  Proof.
    iIntros (Htsnz Hkey Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) bumpKey(ts uint64, key string) bool {                @*)
    (*@     spts := rp.sptsm[key]                                               @*)
    (*@     if ts - 1 <= spts {                                                 @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@     rp.sptsm[key] = ts - 1                                              @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapGet with "HsptsmM").
    iIntros (sptsW ok) "[%Hspts HsptsmM]".
    wp_pures.
    case_bool_decide as Hcond; wp_pures.
    { rewrite word.unsigned_sub_nowrap in Hcond; last word.
      destruct ok.
      { apply map_get_true in Hspts.
        iSpecialize ("HΦ" $! (uint.nat sptsW)).
        case_bool_decide as Hts; first word.
        iApply "HΦ".
        iFrame "HptsmP HsptsmP ∗ %".
        iPureIntro.
        split; last first.
        { specialize (Hsptsmabs _ Hkey).
          by rewrite Hspts in Hsptsmabs.
        }
        intros k Hk.
        destruct (decide (k = key)) as [-> | Hne]; last first.
        { rewrite lookup_insert_ne; last done.
          by apply Hsptsmabs.
        }
        rewrite lookup_insert_eq Hspts.
        f_equal.
        clear -Hts. word.
      }
      { apply map_get_false in Hspts as [Hspts ->].
        simpl in Hcond.
        iSpecialize ("HΦ" $! O).
        case_bool_decide as Hts; first word.
        assert (uint.Z ts = 1) by word.
        iApply "HΦ".
        iFrame "HptsmP HsptsmP ∗ %".
        iPureIntro.
        assert (Hz : sptsm !! key = Some O).
        { specialize (Hsptsmabs _ Hkey).
          by rewrite Hspts in Hsptsmabs.
        }
        split; last apply Hz.
        replace (_ `max` _)%nat with O; last word.
        by rewrite insert_id.
      }
    }
    rewrite word.unsigned_sub_nowrap in Hcond; last word.
    wp_loadField.
    wp_apply (wp_MapInsert with "HsptsmM"); first done.
    iIntros "HsptsmM".
    wp_pures.
    destruct ok.
    { apply map_get_true in Hspts.
      iSpecialize ("HΦ" $! (uint.nat sptsW)).
      case_bool_decide as Hts; last word.
      iApply "HΦ".
      iFrame "HptsmP HsptsmP ∗ %".
      iPureIntro.
      split; last first.
      { specialize (Hsptsmabs _ Hkey).
        by rewrite Hspts in Hsptsmabs.
      }
      intros k Hk.
      destruct (decide (k = key)) as [-> | Hne]; last first.
      { do 2 (rewrite lookup_insert_ne; last done).
        by apply Hsptsmabs.
      }
      rewrite 2!lookup_insert_eq.
      f_equal.
      clear -Hcond. word.
    }
    { apply map_get_false in Hspts as [Hspts ->].
      simpl in Hcond.
      iSpecialize ("HΦ" $! O).
      case_bool_decide as Hts; last word.
      { iApply "HΦ".
        assert (Hsptsmkey : sptsm !! key = Some O).
        { specialize (Hsptsmabs _ Hkey).
          by rewrite Hspts in Hsptsmabs.
        }
        iFrame "HptsmP HsptsmP ∗ %".
        iPureIntro.
        intros k Hk.
        destruct (decide (k = key)) as [-> | Hne]; last first.
        { do 2 (rewrite lookup_insert_ne; last done).
          by apply Hsptsmabs.
        }
        rewrite 2!lookup_insert_eq.
        f_equal.
        word.
      }
    }
  Qed.

End program.
