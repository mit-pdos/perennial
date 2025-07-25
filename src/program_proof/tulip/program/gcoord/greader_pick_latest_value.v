From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import quorum.
From Perennial.program_proof.tulip.program.gcoord Require Import greader_repr.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupReader__pickLatestValue (grd : loc) (key : byte_string) qreadm verm ts γ :
    qreadm !! key = Some verm ->
    cquorum_size rids_all (dom verm) ->
    {{{ own_greader_qreadm grd qreadm ts γ }}}
      GroupReader__pickLatestValue #grd #(LitString key)
    {{{ (value : dbval), RET (dbval_to_val value); 
        own_greader_qreadm grd qreadm ts γ ∗ quorum_read γ key ts value
    }}}.
  Proof.
    iIntros (Hqread Hqsize Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) pickLatestValue(key string) tulip.Value {       @*)
    (*@     var lts uint64                                                      @*)
    (*@     var value tulip.Value                                               @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first done.
    iIntros (ltsP) "HltsP".
    wp_apply wp_ref_of_zero; first done.
    iIntros (valueP) "HvalueP".

    (*@     verm := grd.qreadm[key]                                             @*)
    (*@                                                                         @*)
    iNamed "Hgrd".
    wp_loadField.
    wp_apply (wp_MapGet with "HqreadmM").
    iIntros (vermP ok) "[%Hok HqreadmM]".
    wp_pures.
    destruct ok; last first.
    { iDestruct (big_sepM2_dom with "Hqreadm") as %Hdomqreadm.
      apply map_get_false in Hok as [Hnone _].
      rewrite -not_elem_of_dom Hdomqreadm in Hnone.
      by apply elem_of_dom_2 in Hqread.
    }
    apply map_get_true in Hok.
    iDestruct (big_sepM2_lookup_acc with "Hqreadm") as "[Hverm HqreadmC]".
    { apply Hok. }
    { apply Hqread. }

    (*@     for _, ver := range(verm) {                                         @*)
    (*@         if lts <= ver.Timestamp {                                       @*)
    (*@             value = ver.Value                                           @*)
    (*@             lts = ver.Timestamp                                         @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    set P := (λ (mx : gmap u64 (u64 * dbval)),
                ∃ (lts : u64) (value : dbval),
                  "HltsP"     ∷ ltsP ↦[uint64T] #lts ∗
                  "HvalueP"   ∷ valueP ↦[boolT * (stringT * unitT)%ht] (dbval_to_val value) ∗
                  "%Hlargest" ∷ ⌜map_Forall (λ _ x, uint.Z x.1 ≤ uint.Z lts) mx⌝ ∗
                  "%Hin"      ∷ ⌜if decide (mx = ∅)
                                 then lts = U64 0
                                 else map_Exists (λ _ x, x = (lts, value)) mx⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Hverm [HltsP HvalueP]").
    { iExists _, None. by iFrame. }
    { clear Φ.
      iIntros (mx rid [t v] Φ) "!> [HP %Hmx] HΦ".
      iNamed "HP".
      wp_load.
      wp_pures.
      case_bool_decide as Horder; wp_pures.
      { wp_apply (wp_StoreAt with "HvalueP").
        { destruct v; by auto. }
        iIntros "HvalueP".
        wp_store.
        iApply "HΦ".
        subst P.
        iFrame.
        iPureIntro.
        split.
        { intros rid' [t' v'] Hv'. simpl.
          destruct (decide (rid' = rid)) as [-> | Hne].
          { rewrite lookup_insert_eq in Hv'. by inv Hv'. }
          rewrite lookup_insert_ne in Hv'; last done.
          specialize (Hlargest _ _ Hv'). simpl in Hlargest.
          clear -Hlargest Horder. lia.
        }
        { destruct (decide (<[rid:=(t, v)]> mx = ∅)) as [He | Hne].
          { by apply insert_non_empty in He. }
          by apply map_Exists_insert_2_1.
        }
      }
      iApply "HΦ".
      subst P.
      iFrame.
      iPureIntro.
      split.
      { apply map_Forall_insert_2; last done.
        simpl. lia.
      }
      { case_decide as Hmxe.
        { clear -Horder Hin. word. }
        case_decide as Hinsert.
        { by apply insert_non_empty in Hinsert. }
        destruct Hmx as [Hmx _].
        by apply map_Exists_insert_2_2.
      }
    }
    iIntros "[Hverm HP]".
    subst P. iNamed "HP".
    wp_pures.
    wp_load.

    (*@     return value                                                        @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iDestruct ("HqreadmC" with "Hverm") as "HqreadmC".
    iFrame "∗ # %".
    iDestruct (big_sepM_lookup with "Hqread") as "Hqreadkey"; first apply Hqread.
    case_decide as Hverm.
    { exfalso.
      rewrite -dom_empty_iff_L -size_empty_iff_L in Hverm.
      clear -Hqsize Hverm. rewrite /cquorum_size in Hqsize. lia.
    }
    destruct Hin as (rid & [t v] & Hvermrid & Htv).
    inv Htv.
    iDestruct (big_sepM_lookup with "Hqreadkey") as "Hlver"; first apply Hvermrid.
    iNamed "Hlver".
    iFrame "Hv %".
    iModIntro.
    iExists (dom verm).
    iSplit.
    { rewrite big_sepS_big_sepM.
      iApply (big_sepM_mono with "Hqreadkey").
      iIntros (r [t v] Htv).
      iNamed 1. simpl.
      iApply (read_promise_weaken_lb with "Hioa").
      specialize (Hlargest _ _ Htv). simpl in Hlargest.
      clear -Hlargest. lia.
    }
    iPureIntro.
    by specialize (Hvrids _ _ Hqread).
  Qed.

End program.
