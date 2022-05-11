From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import client.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.grove_shared Require Export erpc_lib urpc_proof urpc_spec.
From Perennial.program_proof.fencing Require Export config_proof frontend_proof.
From Perennial.program_proof Require Export marshal_proof.
From iris.base_logic Require Import mono_nat.
From Perennial.goose_lang Require Import prelude ffi.grove_exit_axiom.

Module client.
Section client_proof.
Context `{!heapGS Σ}.

Record client_names :=
  {
    config_gn: config.names;
    kv_gn : gname;
  }.

Implicit Type γ : client_names.
Context `{!urpcregG Σ}.
Context `{!ctrG Σ}.

Definition config_host_inv γ (host:u64) : iProp Σ :=
  ∃ γfe,
  ⌜γfe.(frontend.kv_gn) = γ.(kv_gn)⌝ ∗
  frontend.is_host γfe host.

(* This is "own" not "is" because the frontendCk field is written to inside of
   FetchAndIncrement, so it's actually not safe for one Clerk to have concurrent
   FAIs. *)
Definition own_Clerk γ ck : iProp Σ :=
  ∃ (configCk frontendCk:loc) γfe,
  "HconfigCk" ∷ ck ↦[client.Clerk :: "configCk"] #configCk ∗
  "HfrontendCk" ∷ ck ↦[client.Clerk :: "frontendCk"] #frontendCk ∗

  "#HconfigCk_is" ∷ config.is_Clerk γ.(config_gn) configCk (λ _, True) (config_host_inv γ) ∗
  "#HfrontendCk_is" ∷ frontend.is_Clerk γfe frontendCk ∗
  "%Hfrontend_gn" ∷ ⌜γfe.(frontend.kv_gn) = γ.(kv_gn)⌝
.

Lemma wp_MakeClerk γ configHost :
  config.is_host γ.(config_gn) configHost (λ _, True) (config_host_inv γ) -∗
  {{{
        True
  }}}
    client.MakeClerk #configHost
  {{{
        (ck:loc), RET #ck; own_Clerk γ ck
  }}}
.
Proof.
  iIntros "#Hcfg !#" (Φ) "_ HΦ".
  wp_call.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (ck) "Hck".
  wp_pures.

  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".
  wp_apply (config.wp_MakeClerk with "Hcfg").
  iIntros (configCk) "#HconfigCk_is".
  wp_storeField.
  wp_loadField.
  wp_apply (config.wp_Clerk__Get with "HconfigCk_is").
  iIntros (frontendHost) "#HfrontendHost".
  iDestruct "HfrontendHost" as (?) "[%Hfe_gn #HfrontendHost]".
  wp_pures.
  wp_apply (frontend.wp_MakeClerk with "HfrontendHost").
  iIntros (frontendCk) "#HfrontendCk_is".
  wp_storeField.
  iApply "HΦ".
  iExists _, _, _.
  iFrame "∗#".
  done.
Qed.

Lemma wp_FetchAndIncrement γ ck (key:u64) Φ :
  key = 0 ∨ key = 1 →
  own_Clerk γ ck -∗
  □ (|={⊤∖↑frontend.frontendN, ∅}=> ∃ v, frontend.kv_ptsto γ.(kv_gn) key v
        ∗ (frontend.kv_ptsto γ.(kv_gn) key (word.add v 1) ={∅, ⊤∖↑frontend.frontendN}=∗ (own_Clerk γ ck -∗ Φ #v))
    ) -∗
  WP client.Clerk__FetchAndIncrement #ck #key {{ Φ }}
.
Proof.
  intros Hkey.
  iIntros "Hck #Hupd".
  wp_call.

  wp_apply (wp_ref_of_zero).
  { done. }

  iIntros (ret_ptr) "Hret".
  wp_pures.

  wp_forBreak.
  wp_pures.

  iNamed "Hck".
  wp_loadField.
  wp_bind (frontend.Clerk__FetchAndIncrement _ _ _).
  wp_apply (wp_frame_wand with "[HconfigCk HfrontendCk]").
  {
    iNamedAccu.
  }
  wp_apply (frontend.wp_Clerk__FetchAndIncrement with "HfrontendCk_is [Hret]").
  { done. }
  {
    iFrame.
  }
  { (* non-error case *)
    iModIntro.
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (?) "[Hkv Hupd]".
    rewrite Hfrontend_gn.
    iExists _. iFrame "Hkv".
    iIntros "Hkv".
    iMod ("Hupd" with "Hkv") as "Hupd".
    iModIntro.
    iIntros "Hret".
    iNamed 1.
    wp_pures.
    iModIntro.
    iRight.
    iSplitL ""; first done.
    wp_pures.
    wp_load.
    iApply "Hupd".
    iExists _, _, _.
    iFrame "∗#".
    done.
  }
  { (* got error from frontend; try another one *)
    iModIntro.
    iIntros (err Herr).
    iIntros "Hret".
    iNamed 1.

    wp_pures.
    rewrite bool_decide_false; last first.
    {
      naive_solver.
    }
    wp_pures.

    wp_loadField.
    wp_apply (config.wp_Clerk__Get with "HconfigCk_is").
    iIntros (frontendHost) "HfrontendHost".
    iDestruct "HfrontendHost" as (γfe_new) "[%Hfrontend_gn_new #HfrontendHost]".
    wp_pures.
    wp_apply (frontend.wp_MakeClerk with "HfrontendHost").
    iClear "HfrontendCk_is".
    iIntros (frontendCk2) "#HfrontendCk_is".
    wp_storeField.
    iModIntro.
    iLeft.
    iFrame.
    iSplitL ""; first done.
    iExists _, _, _.
    iFrame "∗#".
    done.
  }
Qed.

End client_proof.
End client.
