From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Export ffi.grove_filesys_axioms.
From Perennial.program_proof.ctrexample Require Import interface.
From Perennial.program_proof Require Import marshal_proof.
From Goose.github_com.mit_pdos.gokv.ctrexample Require Import client.
From Perennial.program_proof.memkv Require Import rpc_proof.
From Perennial.program_proof.ctrexample Require Import wpc_proofmode.

Section client_proof.

Context `{!heapGS Σ}.
Context `{!filesysG Σ}.
Context `{!inG Σ mono_natUR}.
Context `{!rpcregG Σ}.

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
  wp_apply (wp_MakeRPCClient).
  iIntros (cl_ptr) "Hcl".
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

  wp_apply (wp_RPCClient__Call with "[$Hcl $Hrep $Hempty_sl]").
  {
    iDestruct "Hsrv" as "[$ _]".
    instantiate (1:=(λ l, ∃ (x:nat), ⌜has_encoding l [EncUInt64 (U64 x)] ∧ x ≤ localBound⌝)%I).
    iModIntro.
    iModIntro.
    simpl.
    iIntros (x) "Hctr".
    unfold counter_own.
    rewrite mono_nat_auth_lb_op.
    iDestruct (own_op with "Hctr") as "[Hctr #Hlb2]".
    iDestruct (own_update with "Hctr") as ">$".
    { apply mono_nat_update. word. }
    iModIntro.
    iIntros.
    iExists x.
    unfold counter_lb.
    iFrame "#".
    admit.
  }
  iIntros (err) "(Hcl & Hreq & Hrep)".
  destruct err.
  {
    wp_pures.
    wp_if_destruct.
    {
      admit.
    }
    admit.
  }
  iNamed "Hrep".
  iDestruct "Hrep" as "(Hrep & Hrep_sl & HPost)".
  iDestruct "HPost" as (x) ">[%HencPost #Hlb2]".
  wp_pures.

End client_proof.
