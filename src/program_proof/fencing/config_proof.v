From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import frontend.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.grove_shared Require Export erpc_lib urpc_proof urpc_spec.
From Perennial.program_proof.fencing Require Export ctr_proof.
From Perennial.program_proof Require Export marshal_proof.
From iris.base_logic Require Import mono_nat.
From Perennial.goose_lang Require Import prelude.

Module config.
Section config_proof.
Context `{!heapGS Σ}.

Record names :=
  {
    urpc_gn:server_chan_gnames
  }.

Program Definition Get_spec host_inv :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∀ v l, ⌜has_encoding l [EncUInt64 v]⌝ -∗ host_inv v -∗ Φ l)%I
.
Next Obligation.
  solve_proper.
Defined.

Program Definition AcquireEpoch_spec epoch_tok host_inv :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∃ newhost, ⌜has_encoding reqData [EncUInt64 newhost]⌝ ∗
  □ host_inv newhost ∗
  (∀ l epoch, ⌜has_encoding l [EncUInt64 epoch]⌝ -∗ epoch_tok epoch -∗ Φ l))%I
.
Next Obligation.
  solve_proper.
Defined.

Program Definition trivial_spec :=
  λ (reqData:list u8), λne (Φ : list u8 -d> iPropO Σ),
  (∀ (l:list u8), True -∗ Φ l)%I
.
Next Obligation.
  solve_proper.
Defined.

Context `{!urpcregG Σ}.

Definition is_host γ (host:u64) (epoch_tok : u64 → iProp Σ) (host_inv:u64 → iProp Σ): iProp Σ :=
  is_urpc_spec_pred γ.(urpc_gn) host (W64 0) (AcquireEpoch_spec epoch_tok host_inv) ∗
  is_urpc_spec_pred γ.(urpc_gn) host (W64 1) (Get_spec host_inv) ∗
  is_urpc_spec_pred γ.(urpc_gn) host (W64 2) trivial_spec ∗
  is_urpc_dom γ.(urpc_gn) {[ (W64 0) ; (W64 1) ; (W64 2)]}
.

Definition is_Clerk γ (ck:loc) epoch_tok host_inv : iProp Σ :=
  ∃ (cl:loc) host,
    "#Hcl" ∷ readonly (ck ↦[Clerk :: "cl"] #cl) ∗
    "#His_cl" ∷ is_uRPCClient cl host ∗
    "#His_host" ∷ is_host γ host epoch_tok host_inv
.

Lemma wp_MakeClerk γ host epoch_tok host_inv :
  is_host γ host epoch_tok host_inv -∗
  {{{
        True
  }}}
    config.MakeClerk #host
  {{{
        (ck:loc), RET #ck; is_Clerk γ ck epoch_tok host_inv
  }}}.
Proof.
  iIntros "#Hhost !#" (Φ) "_ HΦ".
  wp_rec.
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (ck) "Hck".
  wp_pures.
  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".
  wp_apply (wp_MakeClient).
  iIntros (?) "#His_cl".
  wp_storeField.
  iMod (readonly_alloc_1 with "cl") as "#Hcl".
  iApply "HΦ".
  iModIntro.
  iExists _, _.
  iFrame "#".
Qed.

Lemma wp_Clerk__AcquireEpoch γ ck (newHost:u64) epoch_tok host_inv :
  is_Clerk γ ck epoch_tok host_inv -∗
  {{{
        □ host_inv newHost
  }}}
    config.Clerk__AcquireEpoch #ck #newHost
  {{{
        (epoch:u64), RET #epoch; epoch_tok epoch
  }}}.
Proof.
  iIntros "#Hck !#" (Φ) "#Hhost HΦ".
  wp_rec.
  wp_pures.
  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { done. }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (reply_ptr) "Hrep".
  wp_pures.
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (req_sl req_data) "(%Hreq_enc & %Hreq_len & Hreq_sl)".
  iNamed "Hck".
  wp_loadField.

  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_apply (wp_Client__Call_pred with "[$Hreq_sl $Hrep]").
  { iFrame "#". iDestruct "His_host" as "[$ _]".
    do 2 iModIntro.
    simpl.
    iExists newHost.
    iFrame "#".
    iSplitL ""; first done.
    iIntros.
    instantiate (1:=λ l, (∃ epoch, ⌜has_encoding l [EncUInt64 epoch]⌝ ∗ epoch_tok epoch)%I).
    simpl.
    iExists _; iFrame.
    done.
  }
  iIntros (err) "(Hreq_sl & Hpost)".
  destruct err.
  { (* there was an error; just Exit() *)
    simpl.
    wp_pures.
    rewrite bool_decide_eq_false_2; last first.
    { by destruct c. }
    wp_pures.
    wp_apply (wp_Exit).
    iIntros.
    by exfalso.
  }
  wp_pures.

  iNamed "Hpost".
  iDestruct "Hpost" as "(Hrep & Hrep_sl & Hpost)".
  wp_load.
  iDestruct "Hpost" as (?) "[%Hrep_enc Hepoch_tok]".
  wp_apply (wp_new_dec with "Hrep_sl").
  { done. }
  iIntros (dec) "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros.
  iApply "HΦ".
  iFrame.
Qed.

Lemma wp_Clerk__Get γ ck epoch_tok host_inv :
  is_Clerk γ ck epoch_tok host_inv -∗
  {{{
        True
  }}}
    config.Clerk__Get #ck
  {{{
        (v:u64), RET #v; host_inv v
  }}}.
Proof.
  iIntros "#Hck !#" (Φ) "#Hhost HΦ".
  wp_rec.
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (reply_ptr) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_apply (wp_NewSlice).
  iIntros (dummy_req_sl) "Hreq_sl".
  wp_loadField.

  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_apply (wp_Client__Call_pred with "[$Hreq_sl $Hrep His_cl]").
  { iFrame "#". iDestruct "His_host" as "[_ [$ _]]".
    do 2 iModIntro.
    simpl.
    iIntros.
    instantiate (1:=λ l, (∃ v, ⌜has_encoding l [EncUInt64 v]⌝ ∗ host_inv v)%I).
    simpl.
    iExists _; iFrame.
    done.
  }
  iIntros (err) "(Hreq_sl & Hpost)".
  destruct err.
  { (* there was an error; just Exit() *)
    simpl.
    wp_pures.
    rewrite bool_decide_eq_false_2; last first.
    { by destruct c. }
    wp_pures.
    wp_apply (wp_Exit).
    iIntros.
    by exfalso.
  }
  wp_pures.

  iNamed "Hpost".
  iDestruct "Hpost" as "(Hrep & Hrep_sl & Hpost)".
  wp_load.
  iDestruct "Hpost" as (?) "[%Hrep_enc Hepoch_tok]".
  wp_apply (wp_new_dec with "Hrep_sl").
  { done. }
  iIntros (dec) "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros.
  iApply "HΦ".
  iFrame.
Qed.

End config_proof.
End config.
