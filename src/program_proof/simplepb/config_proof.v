From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export config.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.simplepb Require Import config_marshal_proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof.

Section config_proof.

Record config_names :=
{
  urpc_gn:server_chan_gnames;
  epoch_gn:gname ;
  config_val_gn:gname;
}.

Class configG Σ := {
    config_epochG :> mono_natG Σ ;
    config_configG :> inG Σ (dfrac_agreeR (leibnizO (list u64)));
}.

Implicit Type γ : config_names.

Context `{!heapGS Σ}.
Context `{!configG Σ}.

Definition own_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) (1/2) (int.nat epoch).
Definition is_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (int.nat epoch).

Definition own_config γ (conf:list u64) : iProp Σ :=
  own γ.(config_val_gn) (to_dfrac_agree (DfracOwn (1/2)) (conf: (leibnizO _)))
.

Program Definition GetEpochAndConfig_core_spec γ Φ :=
  (£ 1 ={⊤,∅}=∗ ∃ epoch conf, own_epoch γ epoch ∗ own_config γ conf ∗
    (⌜int.nat epoch < int.nat (word.add epoch (U64 1))⌝ -∗ own_epoch γ (word.add epoch (U64 1)) -∗ own_config γ conf ={∅,⊤}=∗
      Φ (word.add epoch 1) conf
      )
    )%I.

Program Definition GetEpochAndConfig_spec γ :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( (* no args *)
    GetEpochAndConfig_core_spec γ (λ newEpoch conf,
                                  ∀ reply enc_conf,
                                   ⌜Config.has_encoding enc_conf conf⌝ -∗
                                   ⌜reply = u64_le newEpoch ++ enc_conf⌝ -∗
                                   Φ reply
                                  )
    )%I.
Next Obligation.
  solve_proper.
Defined.

Context `{!urpcregG Σ}.

Definition is_host (host:u64) γ :=
  handler_spec γ.(urpc_gn) host (U64 0) (GetEpochAndConfig_spec γ).

Definition is_Clerk (ck:loc) γ : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[config.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_uRPCClient cl srv ∗
  "#Hhost" ∷ is_host srv γ
.

Lemma wp_MakeClerk configHost γ:
  {{{
      is_host configHost γ
  }}}
    config.MakeClerk #configHost
  {{{
      ck, RET #ck; is_Clerk ck γ
  }}}
.
Proof.
  iIntros (Φ) "#Hhost HΦ".
  wp_call.
  wp_apply (wp_MakeClient).
  iIntros (cl) "#Hcl".
  iApply wp_fupd.
  wp_apply (wp_allocStruct).
  { eauto. }
  iIntros (ck) "Hck".
  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "cl") as "#cl".
  iModIntro.
  iApply "HΦ".
  iExists _, _. iFrame "#".
Qed.

Lemma wp_Clerk__GetEpochAndConfig (ck:loc) γ Φ :
  is_Clerk ck γ -∗
  □ (£ 1 ={⊤,∅}=∗ ∃ epoch conf, own_epoch γ epoch ∗
                                    own_config γ conf ∗
    (⌜int.nat epoch < int.nat (word.add epoch (U64 1))⌝ -∗ own_epoch γ (word.add epoch (U64 1)) -∗ own_config γ conf ={∅,⊤}=∗
      (∀ conf_sl, is_slice_small conf_sl uint64T 1 conf -∗ Φ (#(LitInt (word.add epoch (U64 1))), slice_val conf_sl)%V)
                                )
  ) -∗
  WP config.Clerk__GetEpochAndConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.

  wp_forBreak.
  wp_pures.
  iNamed "Hck".

  wp_apply (wp_NewSlice).
  iIntros (dummy_args) "Hargs".
  wp_loadField.
  iDestruct (is_slice_to_small with "Hargs") as "Hargs_sl".
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  {
    iDestruct "Hhost" as "$".
  }
  {
    iModIntro.
    iNext.
    iIntros "Hlc".
    iMod ("HΦ" with "Hlc") as "Hupd".
    iModIntro.
    iDestruct "Hupd" as (??) "(H1&H2&Hupd)".
    iExists _, _.
    iFrame "H1 H2".
    iIntros.
    iMod ("Hupd" with "[% //] [$] [$]") as "Hupd".
    iModIntro.
    iIntros (??) "%Hconf_enc %Henc Hargs_sl".
    iIntros (?) "Hrep Hrep_sl".
    wp_pures.
    iRight.
    iModIntro.
    iSplitR; first done.
    wp_pures.
    wp_apply (wp_ref_of_zero).
    { done. }
    iIntros (epoch_ptr) "Hepoch".
    wp_pures.
    wp_load.
    rewrite Henc.
    wp_apply (wp_ReadInt with "Hrep_sl").
    iIntros (rep_sl1) "Hrep_sl".
    wp_pures.
    wp_store.
    wp_store.
    wp_load.
    wp_apply (Config.wp_Decode with "[$Hrep_sl]").
    { done. }
    iIntros (?) "Hconf_own".
    wp_pures.
    wp_load.
    wp_pures.
    iModIntro.
    iApply "Hupd".
    iFrame.
  }
  {
    iIntros (err) "%Herr Hargs_sl Hrep".
    wp_pures.
    wp_if_destruct.
    {
      exfalso. done.
    }
    iLeft.
    iModIntro.
    iSplitR; first done.
    iFrame.
  }
Qed.

Lemma wp_Clerk__WriteConfig (ck:loc) new_conf new_conf_sl epoch γ Φ :
  is_Clerk ck γ -∗
  is_slice_small new_conf_sl uint64T 1 new_conf -∗
  □ (£ 1 -∗ |={⊤,∅}=> ∃ latest_epoch, own_epoch γ latest_epoch ∗
      if (decide (latest_epoch = epoch)) then
        ∃ conf, own_config γ conf ∗ (own_config γ new_conf -∗ own_epoch γ epoch ={∅,⊤}=∗
                                      is_slice_small new_conf_sl uint64T 1 new_conf -∗
                                            Φ #0)
      else
        (own_epoch γ latest_epoch ={∅,⊤}=∗ (∀ (err:u64), ⌜err ≠ 0⌝ →
                                                         is_slice_small new_conf_sl uint64T 1 new_conf -∗
                                                         Φ #err))
  ) -∗
  WP config.Clerk__WriteConfig #ck #epoch (slice_val new_conf_sl)
  {{ Φ }}
.
Proof.
Admitted.

End config_proof.
