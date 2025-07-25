From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof Require Import std_proof.
From Goose.github_com.mit_pdos.tulip Require Import util.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_CountBoolMap (mP : loc) (m : gmap u64 bool) (b : bool) :
    {{{ own_map mP (DfracOwn 1) m }}}
      CountBoolMap #mP #b
    {{{ (n : u64), RET #n; 
        own_map mP (DfracOwn 1) m ∗ ⌜uint.nat n = size (filter (λ x, x.2 = b) m)⌝
    }}}.
  Proof.
    iIntros (Φ) "Hm HΦ".
    wp_rec.

    (*@ func CountBoolMap(m map[uint64]bool, b bool) uint64 {                   @*)
    (*@     var n uint64 = 0                                                    @*)
    (*@     for _, v := range(m) {                                              @*)
    (*@         if v == b {                                                     @*)
    (*@             // TODO: We should be able to remove this by using the fact that @n @*)
    (*@             // is always le the size of @m, and that the size of @m fits into @*)
    (*@             // uint64. See the proof [wp_MapLen'] in map.v for reference on how @*)
    (*@             // to prove the latter.                                     @*)
    (*@             n = std.SumAssumeNoOverflow(n, 1)                           @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return n                                                            @*)
    (*@ }                                                                       @*)
    wp_pures.
    wp_apply wp_ref_to; first by auto.
    iIntros (nP) "HnP".
    set P := (λ (mx : gmap u64 bool),
                ∃ (n : u64),
                  "HnP" ∷ nP ↦[uint64T] #n ∗
                  "%Hn" ∷ ⌜uint.nat n = size (filter (λ x, x.2 = b) mx)⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Hm [$HnP]").
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
      { simpl. by intros ->. }
      by rewrite delete_id.
    }
    iIntros "[Hm HP]". iNamed "HP".
    wp_load.
    iApply "HΦ".
    by iFrame "∗ %".
  Qed.

End program.
