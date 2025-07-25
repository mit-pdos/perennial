From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof Require Import std_proof.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__countFastProposals
    (gpp : loc) (b : bool) pps rk ts cid gid γ :
    {{{ own_backup_gpreparer_pps gpp pps rk ts cid gid γ }}}
      BackupGroupPreparer__countFastProposals #gpp #b
    {{{ (n : u64), RET #n;
        own_backup_gpreparer_pps gpp pps rk ts cid gid γ ∗
        ⌜uint.nat n = size (filter (λ x, x.2.2 = b) pps)⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpps HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) countFastProposals(b bool) uint64 {     @*)
    (*@     var nprep uint64                                                    @*)
    (*@                                                                         @*)
    wp_pures.
    wp_apply wp_ref_of_zero; first by auto.
    iIntros (nP) "HnP".

    (*@     for _, pp := range(gpp.pps) {                                       @*)
    (*@         if b == pp.Prepared {                                           @*)
    (*@             nprep = std.SumAssumeNoOverflow(nprep, 1)                   @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hpps".
    wp_loadField.
    set P := (λ (mx : gmap u64 ppsl),
                ∃ (n : u64),
                  "HnP" ∷ nP ↦[uint64T] #n ∗
                  "%Hn" ∷ ⌜uint.nat n = size (filter (λ x, x.2.2 = b) mx)⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Hpps [$HnP]").
    { iPureIntro. by rewrite uint_nat_W64_0 map_filter_empty map_size_empty. }
    { clear Φ.
      iIntros (mx k v Φ) "!> [HP %Hmk] HΦ".
      iNamed "HP".
      wp_pures.
      destruct Hmk as [Hmk _].
      case_bool_decide as Hvb; wp_pures.
      { wp_load.
        wp_apply wp_SumAssumeNoOverflow.
        iIntros (Hnoof).
        wp_store.
        iApply "HΦ".
        iFrame.
        iPureIntro.
        rewrite uint_nat_word_add_S; last first.
        { clear -Hnoof. word. }
        rewrite map_filter_insert_True; last by inv Hvb.
        rewrite map_size_insert_None; last first.
        { rewrite map_lookup_filter_None.
          by left.
        }
        by rewrite Hn.
      }
      iApply "HΦ".
      iFrame.
      iPureIntro.
      rewrite map_filter_insert_False; last first.
      { simpl. intros Heq. by rewrite Heq in Hvb. }
      by rewrite delete_id.
    }
    iIntros "[Hm HP]". iNamed "HP".

    (*@     return nprep                                                        @*)
    (*@ }                                                                       @*)
    wp_load.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
