From Perennial.program_proof.rsm Require Import spaxos_prelude spaxos_propose.

Section prog.
  Context `{!heapGS Σ, !spaxos_ghostG Σ}.

  Definition of_length_five (s : byte_string) := length s = 5%nat.

  Definition length_of_consensus v :=
    match v with
    | Chosen s => of_length_five s
    | _ => True
    end.

  Definition length_of_candidates (vs : gset byte_string) :=
    set_Forall of_length_five vs.

  Definition inv_example1 γ : iProp Σ :=
    ∃ v vs,
      "Hv"  ∷ own_consensus_half γ v ∗
      "Hvs" ∷ own_candidates_half γ vs ∗
      "%Hlenv"  ∷ ⌜length_of_consensus v⌝ ∗
      "%Hlenvs" ∷ ⌜length_of_candidates vs⌝.

  #[global]
  Instance inv_example1_timeless γ :
    Timeless (inv_example1 γ).
  Admitted.

  Definition example1N := nroot .@ "example1N".
  Definition know_inv_example1 γ : iProp Σ :=
    inv example1N (inv_example1 γ).

  #[global]
  Instance ite_is_chosens_consensus_persistent γ (b : bool) v :
    Persistent (if b then is_chosen_consensus γ v else True)%I.
  Proof. destruct b; apply _. Qed.

  Theorem wp_example1 :
    {{{ True }}}
      example1 #()
    {{{ RET #(); True }}}.
  Proof using heapGS0 spaxos_ghostG0 Σ.
    iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures.

    (*@ func example1() {                                                       @*)
    (*@     px := MkPaxos()                                                     @*)
    (*@                                                                         @*)
    wp_apply wp_MkPaxos.
    iIntros (γ px) "Hinit".
    iNamed "Hinit".
    wp_pures.
    iMod (inv_alloc example1N _ (inv_example1 γ) with "[Hv Hvs]") as "#Hinvapp".
    { do 2 iExists _. eauto 5 with iFrame. }

    (*@     px.Propose("hello")                                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Propose with "Hpx").
    iInv "Hinvapp" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iExists vs. iFrame.
    iIntros "Hvs".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Hv Hvs]") as "_".
    { do 2 iExists _. iFrame.
      iPureIntro. split; first done.
      unfold length_of_candidates.
      apply set_Forall_union; last done.
      by rewrite set_Forall_singleton.
    }
    iIntros "!>" (okp1) "_".
    wp_pures.
    clear Hlenv Hlenvs v vs.

    (*@     px.Propose("world")                                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Propose with "Hpx").
    iInv "Hinvapp" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iExists vs. iFrame.
    iIntros "Hvs".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Hv Hvs]") as "_".
    { do 2 iExists _. iFrame.
      iPureIntro. split; first done.
      unfold length_of_candidates.
      apply set_Forall_union; last done.
      by rewrite set_Forall_singleton.
    }
    iIntros "!>" (okp2) "_".
    wp_pures.
    clear Hlenv Hlenvs v vs.

    (*@     // Notice in the proof how we transfer the invariant from the candidate set @*)
    (*@     // to the consensus.                                                @*)
    (*@     v1, ok1 := px.Outcome()                                             @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Outcome with "Hpx").
    iInv "Hinvapp" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iExists v. iFrame.
    iIntros (v1 ok1) "Hv".
    iAssert (if ok1 then is_chosen_consensus γ v1 else True)%I with "[Hv]" as "#Hv1".
    { by destruct ok1. }
    iMod "Hmask" as "_".
    iAssert (⌜if ok1 then of_length_five v1 else True⌝)%I as %Hlenv1.
    { iAssert (⌜if ok1 then v1 ∈ vs else True⌝)%I as %Hin.
      { destruct ok1; [by iApply consensus_incl | done]. }
      destruct ok1; last done.
      by specialize (Hlenvs _ Hin).
    }
    iMod ("HinvC" with "[Hv Hvs]") as "_".
    { do 2 iExists _. iFrame. iPureIntro.
      split; last done.
      by destruct ok1.
    }
    iIntros "!> _".
    wp_pures.
    clear Hlenv Hlenvs v vs.

    (*@     v2, ok2 := px.Outcome()                                             @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__Outcome with "Hpx").
    iInv "Hinvapp" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iExists v. iFrame.
    iIntros (v2 ok2) "Hv".
    iAssert (if ok2 then is_chosen_consensus γ v2 else True)%I with "[Hv]" as "#Hv2".
    { by destruct ok2. }
    iMod "Hmask" as "_".
    iAssert (⌜if ok2 then of_length_five v2 else True⌝)%I as %Hlenv2.
    { iAssert (⌜if ok2 then v2 ∈ vs else True⌝)%I as %Hin.
      { destruct ok2; [by iApply consensus_incl | done]. }
      destruct ok2; last done.
      by specialize (Hlenvs _ Hin).
    }
    iMod ("HinvC" with "[Hv Hvs]") as "_".
    { do 2 iExists _. iFrame. iPureIntro.
      split; last done.
      by destruct ok2.
    }
    iIntros "!> _".
    wp_pures.
    clear Hlenv Hlenvs v vs.

    (*@     if ok1 && ok2 {                                                     @*)
    (*@         machine.Assert(v1 == v2)                                        @*)
    (*@         machine.Assert(len(v1) == 5)                                    @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_and_pure (ok1 = true) (ok2 = true)).
    { wp_pures. iPureIntro.
      case_bool_decide as H; first by rewrite H.
      rewrite not_true_iff_false in H. by rewrite H.
    }
    { iIntros (_). wp_pures. iPureIntro.
      case_bool_decide as H; first by rewrite H.
      rewrite not_true_iff_false in H. by rewrite H.
    }
    wp_if_destruct; last by iApply "HΦ".
    destruct Heqb as [Hok1 Hok2]. subst ok1 ok2.
    iDestruct (consensus_agree with "Hv1 Hv2") as %Heq.
    wp_apply wp_Assert.
    { subst v1. by rewrite bool_decide_eq_true. }
    wp_pures.
    wp_apply wp_Assert; first by rewrite Hlenv1.
    wp_pures.
    by iApply "HΦ".
  Qed.

End prog.
