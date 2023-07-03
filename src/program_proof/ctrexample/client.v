From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.ctrexample Require Import interface.
From Perennial.program_proof Require Import marshal_proof.
From Goose.github_com.mit_pdos.gokv.ctrexample Require Import client.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.program_proof.ctrexample Require Import wpc_proofmode.

Section client_proof.

Context `{!heapGS Σ}.
Context `{!filesysG Σ}.
Context `{!inG Σ mono_natUR}.
Context `{!urpcregG Σ}.

Lemma wpc_ClientMain γurpc_gn γ :
  is_CtrServer_urpc γurpc_gn γ -∗
    counter_lb γ 0 -∗
    WP main #()
  {{
      v, True
  }}.
Proof.
  iIntros "#Hsrv #Hlb".
  wp_lam.
  wp_pures.
  wp_apply (wp_MakeClient).
  iIntros (cl_ptr) "#Hcl".
  wp_pures.
  wp_apply (wp_ref_to).
  { eauto. }
  iIntros (localBound_ptr) "HlocalBound".
  wp_pures.

  iAssert (∃ x, counter_lb γ x ∗ localBound_ptr ↦[uint64T] #(U64 x))%I with "[HlocalBound Hlb]" as "HH".
  {
    iExists 0%nat. iFrame "#∗".
  }
  wp_forBreak.
  wp_pures.

  iClear "Hlb".
  iDestruct "HH" as (localBound) "[#Hlb HlocalBound]".

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  wp_apply (wp_NewSlice _ _ byteT).
  iIntros (empty_req) "Hempty_sl".

  iDestruct (own_slice_to_small with "Hempty_sl") as "Hempty_sl".
  wp_apply (wp_Client__Call_pred with "[$Hrep $Hempty_sl]").
  { iFrame "Hcl". iDestruct "Hsrv" as "[$ _]".
  (* FIXME: why doesn't [$Hcl] work? *)
    instantiate (1:=(λ l, ∃ (x:nat), ⌜has_encoding l [EncUInt64 (U64 x)] ∧ localBound ≤ x⌝ ∗ counter_lb γ x)%I).
    iModIntro.
    iModIntro.
    simpl.
    iIntros (x) "Hctr".
    rewrite /counter_own /counter_lb.
    iDestruct (own_valid_2 with "Hctr Hlb") as %Hineq.
    (* FIXME: Q: what is setoid_rewrite, and why does it work when rewrite does not? *)
    setoid_rewrite mono_nat_both_valid in Hineq.
    rewrite mono_nat_auth_lb_op.
    iDestruct (own_op with "Hctr") as "[Hctr #Hlb2]".
    iDestruct (own_update with "Hctr") as ">$".
    { apply mono_nat_update. word. }
    iModIntro.
    iIntros.
    iExists x.
    unfold counter_lb.
    iFrame "#".
    iPureIntro.
    split.
    { done. }
    lia.
  }
  iIntros (err) "(Hreq & Hrep)".
  wp_pures.
  wp_if_destruct.
  {
    iLeft. iModIntro.
    iSplitL ""; first done.
    iFrame "∗#".
    iExists _; iFrame "∗#".
  }
  destruct err.
  {
    exfalso.
    destruct c; done.
  }
  iNamed "Hrep".
  iDestruct "Hrep" as "(Hrep & Hrep_sl & HPost)".
  iDestruct "HPost" as (x) "[[%HencPost %Hlb2] Hlb2]".
  wp_pures.
  wp_load.
  wp_apply (wp_new_dec with "[Hrep_sl]").
  { done. }
  { done. }
  iIntros (dec) "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply (wp_Assert).
  {
    apply bool_decide_eq_true.
    (* FIXME: overflow related *)
    admit.
  }
  wp_pures.
  wp_store.
  iModIntro.
  iLeft.
  iSplitL ""; first done.
  iFrame.
  iExists _; iFrame "∗#".
Admitted.

End client_proof.
