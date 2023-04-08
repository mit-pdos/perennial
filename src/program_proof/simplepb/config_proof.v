From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export config.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof Require Import marshal_stateless_proof std_proof.
From Perennial.program_proof.simplepb Require Import config_marshal_proof renewable_lease.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From iris.base_logic Require Export lib.ghost_var mono_nat.

Section config_global.

Record config_names :=
{
  epoch_gn:gname ;
  config_val_gn:gname;
}.

Class configG Σ := {
    config_configG :> ghost_varG Σ (list u64) ;
    config_urpcG :> urpcregG Σ ;
    config_epochG :> mono_natG Σ ;
    config_leaseG :> renewable_leaseG Σ ;
}.

Definition configΣ := #[mono_natΣ ; ghost_varΣ (list u64) ; urpcregΣ ; renewable_leaseΣ ].

Global Instance subG_configΣ {Σ} : subG configΣ Σ → configG Σ.
Proof. intros. solve_inG. Qed.

Implicit Type γ : config_names.

Context `{!gooseGlobalGS Σ}.
Context `{!configG Σ}.

Definition own_latest_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) (1/2) (int.nat epoch).

Definition is_latest_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(epoch_gn) (int.nat epoch).

Definition own_config γ (conf:list u64) : iProp Σ :=
  ghost_var γ.(config_val_gn) (1/2) conf
.

Definition epochLeaseN := nroot .@ "epochLeaseN".

Program Definition GetEpochAndConfig_core_spec γ Φ :=
  (
    £ 1 -∗
    (|={⊤,∅}=> ∃ epoch conf, own_latest_epoch γ epoch ∗ own_config γ conf ∗
    (⌜int.nat epoch < int.nat (word.add epoch (U64 1))⌝ -∗ own_latest_epoch γ (word.add epoch (U64 1)) -∗ own_config γ conf ={∅,⊤}=∗
      Φ (U64 0) (word.add epoch 1) conf
      )) ∧
      (∀ (err:u64), ⌜err ≠ 0⌝ → Φ err (U64 0) [])
    )%I.

Program Definition GetConfig_core_spec γ Φ :=
  (£ 1 ={⊤,∅}=∗ ∃ conf, own_config γ conf ∗ (own_config γ conf ={∅,⊤}=∗ Φ conf))%I.

Program Definition WriteConfig_core_spec γ (epoch:u64) (new_conf:list u64) Φ : iProp Σ :=
  (£ 1 -∗ |={⊤,↑epochLeaseN}=> ∃ latest_epoch, own_latest_epoch γ latest_epoch ∗
      if (decide (latest_epoch = epoch)) then
        ∃ conf, own_config γ conf ∗ (own_config γ new_conf -∗ own_latest_epoch γ epoch ={↑epochLeaseN,⊤}=∗
                                            Φ (U64 0))
      else
        (own_latest_epoch γ latest_epoch ={↑epochLeaseN,⊤}=∗ (∀ (err:u64), ⌜err ≠ 0⌝ → Φ err))
  ).

Program Definition GetLease_core_spec γ (epoch:u64) Φ : iProp Σ :=
  (∀ (leaseExpiration:u64) γl,
    is_lease epochLeaseN γl (own_latest_epoch γ epoch) -∗
    is_lease_valid_lb γl leaseExpiration -∗ Φ (U64 0) leaseExpiration
  ) ∧
  (∀ (err:u64), ⌜err ≠ 0⌝ → Φ err (U64 0))
.

Program Definition GetEpochAndConfig_spec γ :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( (* no args *)
    GetEpochAndConfig_core_spec γ (λ err newEpoch conf,
                                  ∀ reply enc_conf,
                                   ⌜Config.has_encoding enc_conf conf⌝ -∗
                                   ⌜reply = u64_le err ++ u64_le newEpoch ++ enc_conf⌝ -∗
                                   Φ reply
                                  )
    )%I.
Next Obligation.
  solve_proper.
Defined.

Program Definition GetConfig_spec γ :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( (* no args *)
    GetConfig_core_spec γ (λ conf, ∀ reply,
                                   ⌜Config.has_encoding reply conf⌝ -∗
                                   Φ reply
                                  )
    )%I.
Next Obligation.
  solve_proper.
Defined.

Program Definition WriteConfig_spec γ :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( ∃ epoch new_conf enc_new_conf,
    ⌜enc_args = u64_le epoch ++ enc_new_conf⌝ ∗
    ⌜Config.has_encoding enc_new_conf new_conf⌝ ∗
    WriteConfig_core_spec γ epoch new_conf (λ err, ∀ reply,
                                   ⌜reply = u64_le err⌝ -∗
                                   Φ reply
                                  )
    )%I.
Next Obligation.
  unfold WriteConfig_core_spec.
  solve_proper.
Defined.

Program Definition GetLease_spec γ :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( ∃ epoch ,
    ⌜enc_args = u64_le epoch⌝ ∗
    GetLease_core_spec γ epoch (λ (err:u64) (leaseExpiration:u64), ∀ reply,
                                   ⌜reply = u64_le err ++ u64_le leaseExpiration⌝ -∗
                                   Φ reply
                                  )
    )%I.
Next Obligation.
  unfold GetLease_core_spec.
  solve_proper.
Defined.

Definition is_host (host:u64) γ : iProp Σ :=
  ∃ γrpc,
  handler_spec γrpc host (U64 0) (GetEpochAndConfig_spec γ) ∗
  handler_spec γrpc host (U64 1) (GetConfig_spec γ) ∗
  handler_spec γrpc host (U64 2) (WriteConfig_spec γ) ∗
  handler_spec γrpc host (U64 3) (GetLease_spec γ) ∗
  handlers_dom γrpc {[ (U64 0) ; (U64 1) ; (U64 2) ; (U64 3) ]}
.

End config_global.

Section config_proof.

Context `{!heapGS Σ}.
Context `{!configG Σ}.

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

Definition own_Config_ghost γ leaseExpiration epoch : iProp Σ :=
  "Hepoch_lease" ∷ ((∃ γl, is_lease epochLeaseN γl (own_latest_epoch γ epoch) ∗
                          own_lease_expiration γl leaseExpiration ∗
                          post_lease epochLeaseN γl (own_latest_epoch γ epoch)) ∨
                          own_latest_epoch γ epoch
                   )
.

Lemma lease_expired_get_epoch γ leaseExpiration epoch :
  is_time_lb leaseExpiration -∗
  own_Config_ghost γ leaseExpiration epoch ={↑epochLeaseN}=∗
  own_latest_epoch γ epoch
.
Proof.
  iIntros "Htime_lb Hghost".
  iDestruct "Hghost" as "[H | $]"; last done.
  iDestruct "H" as (?) "(_ & Hexp & Hpost_lease)".
  iMod ("Hpost_lease" with "Hexp Htime_lb") as ">$"; done.
Qed.

Lemma lease_acc_epoch γ t leaseExpiration epoch :
  own_time t -∗
  own_Config_ghost γ leaseExpiration epoch ={↑epochLeaseN, ∅}=∗
  own_latest_epoch γ epoch ∗ (own_latest_epoch γ epoch ={∅,↑epochLeaseN}=∗
                       own_time t ∗
                       own_Config_ghost γ leaseExpiration epoch
                      ).
Proof.
  iIntros "Ht Hghost".
  iDestruct "Hghost" as "[H | Hepoch]".
  2:{ (* case: we own the epoch directly; just do some meaningless stuff to get
         the right masks *)
    iFrame "Hepoch".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "Hmask".
    iIntros "Hepoch".
    iMod "Hmask" as "_".
    by iFrame.
  }
  {
    iDestruct "H" as (?) "(#Hlease & Hexp & Hpost)".
    destruct (decide (int.nat t < int.nat leaseExpiration)) eqn:Hineq.
    { (* case: lease is unexpired. Access own_latest_epoch from the lease. *)
      iDestruct (lease_get_lb with "Hexp") as "#Hvalid".
      iMod (lease_acc with "Hvalid Hlease Ht") as "[>$ HH]".
      { done. }
      iModIntro.
      iIntros "Hepoch".
      iMod ("HH" with "Hepoch") as "$".
      iModIntro.
      iLeft.
      iExists _; iFrame "∗#".
    }
    { (* case: lease is expired.  *)
      iDestruct (own_time_get_lb with "Ht") as "#Hlb".
      iMod ("Hpost" with "Hexp [Hlb]") as ">Hepoch".
      { iApply is_time_lb_mono; last done. word. }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "Hmask".
      iFrame.
      iIntros "Hepoch".
      iMod "Hmask". iModIntro.
      iFrame.
    }
  }
Qed.

Definition own_Server (s:loc) γ : iProp Σ :=
  ∃ (epoch leaseExpiration:u64) (conf:list u64) conf_sl,
  "Hepoch" ∷ s ↦[config.Server :: "epoch"] #epoch ∗
  "HleaseExpiration" ∷ s ↦[config.Server :: "leaseExpiration"] #leaseExpiration ∗
  "Hconf" ∷ s ↦[config.Server :: "config"] (slice_val conf_sl) ∗
  "Hconf_sl" ∷ is_slice_small conf_sl uint64T 1 conf ∗
  "Hepoch_lease" ∷ own_Config_ghost γ leaseExpiration epoch ∗
  "Hconf_ghost" ∷ own_config γ conf
.

Definition configN := nroot .@ "config".

Definition is_Server (s:loc) γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[config.Server :: "mu"] mu) ∗
  "#His_mu" ∷ is_lock configN mu (own_Server s γ).

Lemma wp_Server__GetEpochAndConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config.Server__GetEpochAndConfig #server
  {{{
        (f:val), RET f; impl_handler_spec2 f (GetEpochAndConfig_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold impl_handler_spec2.
  clear Φ.
  iIntros (enc_args Φ Ψ req_sl rep_ptr dummy_sl dummy) "!# Harg_sl Hrep _ HΦ HΨ".
  wp_call.

  iNamed "His_srv".
  wp_apply wp_GetTimeRange.
  iIntros (?????) "Htime".
  rewrite /GetEpochAndConfig_spec /GetEpochAndConfig_core_spec.
  iDestruct (own_time_get_lb with "Htime") as "#Htime_lb".
  iFrame "Htime".
  iModIntro.

  wp_loadField.
  wp_apply (acquire_spec with "[$His_mu]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pure1_credit "Hlc".
  wp_loadField.
  wp_if_destruct.
  { (* lock service *)
    wp_loadField.
    wp_apply (release_spec with "[- HΨ HΦ Hrep Hlc]").
    {
      iFrame "His_mu Hlocked".
      iNext.
      repeat iExists _.
      iFrame.
    }
    wp_pures.
    wp_apply wp_NewSliceWithCap.
    { word. }
    (* marshalling reply *)
    iIntros (?) "Hrep_sl".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "Hrep_sl").
    iIntros (?) "Hrep_sl".
    clear.
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "Hrep_sl").
    iIntros (?) "Hrep_sl".
    wp_store.
    replace slice.nil with (slice_val Slice.nil) by done.
    wp_apply (Config.wp_Encode with "[]").
    { by iApply is_slice_small_nil. }
    iIntros (??) "(%Henc & ? & Hsl)".
    wp_load.
    iDestruct (is_slice_to_small with "Hsl") as "Hsl".
    wp_apply (wp_WriteBytes with "[$Hrep_sl $Hsl]").
    iIntros (?) "[Hrep_sl _]".
    wp_store.
    iSpecialize ("HΨ" with "Hlc").
    iRight in "HΨ".
    iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iApply ("HΦ" with "[HΨ] [$Hrep] [$Hrep_sl]").
    rewrite replicate_0 app_nil_l -app_assoc.
    iApply "HΨ"; iPureIntro; last done; done.
  }

  wp_loadField.
  wp_apply (wp_SumAssumeNoOverflow).
  iIntros (Hno_overflow).
  wp_storeField.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (ptr) "Hsl".
  wp_store.
  wp_load.
  wp_apply (wp_WriteInt with "Hsl").
  iIntros (?) "Hrep_sl".
  wp_store.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Hrep_sl").
  iIntros (enc_sl) "Hrep_sl".
  wp_store.
  wp_loadField.
  wp_apply (Config.wp_Encode with "[Hconf_sl]").
  { iFrame. }
  iIntros (enc_conf enc_conf_sl) "(%Hconf_enc & Hconf_sl & Henc_conf_sl)".
  wp_load.
  wp_apply (wp_WriteBytes with "[$Hrep_sl Henc_conf_sl]").
  {
    iDestruct (is_slice_to_small with "Henc_conf_sl") as "$".
  }
  iIntros (rep_sl) "[Hrep_sl Henc_conf_sl]".
  replace (int.nat 0%Z) with 0%nat by word.
  wp_store.
  wp_loadField.

  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑epochLeaseN)) as "Hmask".
  { set_solver. }
  iMod (lease_expired_get_epoch with "[Htime_lb] Hepoch_lease") as "Hepoch_ghost".
  { iApply is_time_lb_mono; last done. word. }
  iMod "Hmask".
  iSpecialize ("HΨ" with "Hlc").
  iLeft in "HΨ".
  iMod "HΨ".
  iDestruct "HΨ" as (??) "(Hepoch_ghost2 & Hconf_ghost2 & Hupd)".
  iDestruct (ghost_var_agree with "Hconf_ghost Hconf_ghost2") as %->.


  iDestruct (mono_nat_auth_own_agree with "Hepoch_ghost Hepoch_ghost2") as %[_ Heq].
  replace (epoch0) with (epoch) by word.
  iCombine "Hepoch_ghost Hepoch_ghost2" as "Hepoch_ghost".
  iMod (mono_nat_own_update (int.nat (word.add epoch 1)) with "Hepoch_ghost") as "[[Hepoch_ghost Hepoch_ghost2] _]".
  { word. }
  iSpecialize ("Hupd" with "[%] Hepoch_ghost2 Hconf_ghost2").
  { word. }
  iMod "Hupd".
  iModIntro.

  wp_apply (release_spec with "[$Hlocked $His_mu Hepoch Hconf Hconf_ghost Hconf_sl Hepoch_ghost HleaseExpiration]").
  {
    iNext.
    repeat iExists _.
    iFrame "∗#%".
  }
  wp_pures.
  iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
  iSpecialize ("Hupd" with "[% //] [% //]").
  iApply ("HΦ" with "Hupd Hrep Hrep_sl").
Qed.

Lemma wp_Server__GetConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config.Server__GetConfig #server
  {{{
        (f:val), RET f; impl_handler_spec2 f (GetConfig_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold impl_handler_spec2.
  clear Φ.
  iIntros (enc_args Φ Ψ req_sl rep_ptr dummy_sl dummy) "!# Harg_sl Hrep _ HΦ HΨ".
  wp_call.

  iNamed "His_srv".
  wp_loadField.
  wp_apply (acquire_spec with "[$His_mu]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pure1_credit "Hlc".
  wp_loadField.
  wp_apply (Config.wp_Encode with "[Hconf_sl]").
  { iFrame. }
  iIntros (enc_conf rep_sl) "(%Hconf_enc & Hconf_sl & Hrep_sl)".
  wp_store.
  wp_loadField.

  iApply fupd_wp.
  iMod ("HΨ" with "Hlc") as "HΨ".
  iDestruct "HΨ" as (?) "(Hconf_ghost2 & Hupd)".
  iDestruct (ghost_var_agree with "Hconf_ghost Hconf_ghost2") as %->.
  iMod ("Hupd" with "Hconf_ghost2") as "Hupd".
  iModIntro.

  wp_apply (release_spec with "[$Hlocked $His_mu Hepoch Hconf Hconf_ghost Hconf_sl Hepoch_lease HleaseExpiration]").
  {
    iNext.
    repeat iExists _.
    iFrame.
  }
  wp_pures.
  iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
  iSpecialize ("Hupd" with "[% //]").
  iApply ("HΦ" with "Hupd Hrep Hrep_sl").
Qed.

Lemma wp_Server__WriteConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config.Server__WriteConfig #server
  {{{
        (f:val), RET f; impl_handler_spec2 f (WriteConfig_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold impl_handler_spec2.
  clear Φ.
  iIntros (enc_args Φ Ψ req_sl rep_ptr dummy_sl dummy) "!# Harg_sl Hrep _ HΦ HΨ".
  wp_call.
  iNamed "His_srv".
  wp_loadField.
  wp_apply (acquire_spec with "[$His_mu]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.

  unfold WriteConfig_spec.
  iDestruct "HΨ" as (new_epoch new_conf enc_new_conf) "(%Henc & %Henc_conf & HΨ)".
  rewrite Henc.
  wp_apply (wp_ReadInt with "Harg_sl").
  iIntros (args_sl) "Hargs_sl".
  wp_pure1_credit "Hlc".

  replace (slice.nil) with (slice_val Slice.nil) by done.
  wp_loadField.
  wp_if_destruct.
  {
    wp_apply (wp_WriteInt with "[]").
    {
      iApply is_slice_zero.
    }
    iIntros (rep_sl) "Hrep_sl".
    wp_store.
    wp_loadField.

    wp_apply wp_time_acc.
    { done. }
    iIntros (t) "Htime".
    iMod ("HΨ" with "Hlc") as "HΨ".
    iDestruct "HΨ" as (?) "(Hepoch_ghost2 & HΨ)".
    iAssert (|={↑epochLeaseN}=> ⌜epoch = latest_epoch⌝ ∗ _)%I with "[Hepoch_lease Htime Hepoch_ghost2]" as ">[%Heq HH]".
    {
      iMod (lease_acc_epoch with "Htime Hepoch_lease") as "[Hepoch_ghost HH]".
      iDestruct (mono_nat_auth_own_agree with "Hepoch_ghost Hepoch_ghost2") as %[_ Heq].
      iMod ("HH" with "Hepoch_ghost") as "[Htime Hepoch_lease]".
      iModIntro.
      iSplitR.
      1: iPureIntro;word.
      iNamedAccu.
    }
    iNamed "HH".
    subst.
    destruct (decide (_)).
    {
      exfalso. rewrite e in Heqb.
      done.
    }
    simpl.
    iMod ("HΨ" with "Hepoch_ghost2") as "HΨ".
    iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iDestruct ("HΨ" with "[%] [% //]") as "HΨ".
    { instantiate (1:=1). done. }
    iDestruct ("HΦ" with "HΨ Hrep Hrep_sl") as "HΦ".
    iModIntro.
    iFrame.
    wp_apply (release_spec with "[$Hlocked $His_mu Hepoch Hconf Hconf_sl Hepoch_lease Hconf_ghost HleaseExpiration]").
    {
      iNext.
      iExists _,_,_.
      eauto with iFrame.
    }
    wp_pures.
    iModIntro.
    done.
  }
  {
    wp_apply (Config.wp_Decode with "[$Hargs_sl]").
    { done. }
    iIntros (new_conf_sl) "Hnew_conf_sl".
    wp_storeField.
    wp_apply (wp_WriteInt with "[]").
    {
      iApply is_slice_zero.
    }
    iIntros (rep_sl) "Hrep_sl".
    wp_store.

    wp_apply wp_time_acc.
    { done. }
    iIntros (?) "Htime".
    iMod ("HΨ" with "Hlc") as "HΨ".
    iDestruct "HΨ" as (?) "[Hepoch_ghost2 HΨ]".

    iAssert (|={↑epochLeaseN}=> ⌜epoch = latest_epoch⌝ ∗ _)%I with "[Hepoch_lease Htime Hepoch_ghost2]" as ">[%Heq HH]".
    {
      iMod (lease_acc_epoch with "Htime Hepoch_lease") as "[Hepoch_ghost HH]".
      iDestruct (mono_nat_auth_own_agree with "Hepoch_ghost Hepoch_ghost2") as %[_ Heq].
      iMod ("HH" with "Hepoch_ghost") as "[Htime Hepoch_lease]".
      iModIntro.
      iSplitR.
      1: iPureIntro;word.
      iNamedAccu.
    }
    iNamed "HH".
    subst.
    iFrame.
    destruct (decide (_)); last first.
    {
      exfalso.
      done.
    }
    {
      iDestruct "HΨ" as (?) "[Hconf_ghost2 HΨ]".
      iDestruct (ghost_var_agree with "Hconf_ghost Hconf_ghost2") as %->.
      iCombine "Hconf_ghost Hconf_ghost2" as "Hconf_ghost".
      iMod (ghost_var_update new_conf with "Hconf_ghost") as "[Hconf_ghost Hconf_ghost2]".
      iMod ("HΨ" with "Hconf_ghost2 Hepoch_ghost2") as "HΨ".
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iSpecialize ("HΨ" with "[%]").
      { done. }
      iSpecialize ("HΦ" with "HΨ Hrep Hrep_sl").
      iModIntro.

      wp_loadField.
      wp_apply (release_spec with "[$Hlocked $His_mu Hepoch Hconf Hnew_conf_sl Hepoch_lease HleaseExpiration Hconf_ghost]").
      {
        iNext.
        iExists _,_,_.
        eauto with iFrame.
      }
      wp_pures.
      iModIntro.
      done.
    }
  }
Qed.

(* NOTE: There's a lot of case distinction with this lease stuff. Some of it
   feels redundant. In particular, there are two cases in which we'll have
   direct ownership of own_latest_epoch: either the mutex inv just has it, or the lease
   is expired and we can get it immediately from post_lease.  This corresponds
   to the two places that R shows up in renewable_lease: either pre-expiration,
   or post-expiration but prior to escrow claiming it.

  Here's a "cleanup" lemma to avoid this distinction.
  It says that either you own the epoch number, or you have a valid lease.
 *)
Lemma own_Config_ghost_normalize t γ epoch leaseExpiration :
  own_time t -∗
  own_Config_ghost γ leaseExpiration epoch
  ={↑epochLeaseN}=∗
  own_time t ∗
  (own_latest_epoch γ epoch ∨
   ∃ γl,
    ⌜int.nat t < int.nat leaseExpiration⌝ ∗
    own_lease_expiration γl leaseExpiration ∗
    is_lease epochLeaseN γl (own_latest_epoch γ epoch) ∗
    post_lease epochLeaseN γl (own_latest_epoch γ epoch)
  )
.
Proof.
  iIntros "Ht Hghost".
  iDestruct "Hghost" as "[Hghost|$]".
  2: by iFrame.
  iDestruct "Hghost" as (?) "(#Hlease & Hexp & Hpost)".
  destruct (decide (int.nat t < int.nat leaseExpiration)) eqn:Hlease.
  { (* case: lease is not expired. *)
    iFrame.
    iModIntro.
    iRight. iExists _; iFrame "∗#%".
  }
  { (* case: lease is expired *)
    iDestruct (own_time_get_lb with "Ht") as "#?".
    iMod ("Hpost" with "Hexp []") as ">$".
    { iApply is_time_lb_mono; last done.
      word.
    }
    by iFrame.
  }
Qed.

Lemma get_lease_step newLeaseExpiration t γ epoch leaseExpiration :
  int.nat leaseExpiration <= int.nat newLeaseExpiration →
  own_time t -∗
  own_Config_ghost γ leaseExpiration epoch
  ={↑epochLeaseN}=∗
  ∃ γl,
  own_time t ∗
  is_lease epochLeaseN γl (own_latest_epoch γ epoch) ∗
  is_lease_valid_lb γl newLeaseExpiration ∗
  own_Config_ghost γ newLeaseExpiration epoch
.
Proof.
  iIntros (?) "Htime Hghost".
  iMod (own_Config_ghost_normalize with "Htime Hghost") as "[Htime Hghost]".
  iDestruct "Hghost" as "[Hepoch|Hlease]".
  { (* create a new lease *)
    iMod (lease_alloc newLeaseExpiration with "Hepoch") as (?) "(#Hlease & Hpost & Hexp)".
    iDestruct (lease_get_lb with "Hexp") as "#?".
    iModIntro.
    iExists _; iFrame "∗#".
    iLeft. iExists _; iFrame "∗#".
  }
  {(* renew the existing lease *)
    iDestruct "Hlease" as (?) "(% & Hexp & #Hlease & ?)".
    iMod (renew_lease newLeaseExpiration with "Hlease Hexp Htime") as "[$ Hexp]".
    { done. }
    { done. }
    iModIntro.
    iDestruct (lease_get_lb with "Hexp") as "#?".
    iExists _; iFrame "∗#".
    iLeft. iExists _; iFrame "∗#".
  }
Qed.

Lemma get_lease_step_old oldLeaseExpiration t γ epoch leaseExpiration :
  int.nat oldLeaseExpiration <= int.nat leaseExpiration →
  own_time t -∗
  own_Config_ghost γ leaseExpiration epoch
  ={↑epochLeaseN}=∗
  ∃ γl,
  own_time t ∗
  is_lease epochLeaseN γl (own_latest_epoch γ epoch) ∗
  is_lease_valid_lb γl oldLeaseExpiration ∗
  own_Config_ghost γ leaseExpiration epoch
.
Proof.
  iIntros (?) "Htime Hghost".
  iMod (own_Config_ghost_normalize with "Htime Hghost") as "[Htime Hghost]".
  iDestruct "Hghost" as "[Hepoch|Hlease]".
  { (* create a new lease *)
    iMod (lease_alloc leaseExpiration with "Hepoch") as (?) "(#Hlease & Hpost & Hexp)".
    iDestruct (lease_get_lb with "Hexp") as "#?".
    iModIntro.
    iExists _; iFrame "∗#".
    iSplitR.
    { by iApply lease_lb_mono. }
    iLeft. iExists _; iFrame "∗#".
  }
  {
    iDestruct "Hlease" as (?) "(_ & Hexp & #Hlease & Hpost)".
    iDestruct (lease_get_lb with "Hexp") as "#?".
    iModIntro.
    iExists _. iFrame "∗#".
    iSplitR.
    { by iApply lease_lb_mono. }
    iLeft. iExists _; iFrame "∗#".
  }
Qed.

Lemma wp_Server__GetLease (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config.Server__GetLease #server
  {{{
        (f:val), RET f; impl_handler_spec2 f (GetLease_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold impl_handler_spec2.
  clear Φ.
  iIntros (enc_args Φ Ψ req_sl rep_ptr dummy_sl dummy) "!# Harg_sl Hrep _ HΦ HΨ".
  wp_call.
  iNamed "His_srv".
  iDestruct "HΨ" as (?) "[% HΨ]".
  subst.
  wp_apply (wp_ReadInt with "Harg_sl").
  iIntros (?) "Hargs_sl".
  wp_loadField.
  wp_apply (acquire_spec with "[$His_mu]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* case: epoch number that the caller wants is not the latest epoch *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ Hrep]").
    {
      iFrame "His_mu Hlocked".
      iNext.
      repeat iExists _.
      iFrame.
    }
    replace (slice.nil) with (slice_val Slice.nil) by done.
    wp_apply (wp_WriteInt with "[]").
    { iApply is_slice_zero. }
    iIntros (?) "Hsl".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "[$]").
    iIntros (?) "Hsl".
    wp_store.
    iRight in "HΨ".
    iDestruct (is_slice_to_small with "Hsl") as "Hsl".
    iApply ("HΦ" with "[HΨ] [$] [$]").
    rewrite app_nil_l.
    iApply "HΨ".
    2: iPureIntro; done.
    done.
  }
  (* case: can give out lease *)
  (* There are two logical subcases.
     If the lease is still valid, we extend it.
     Otherwise, we have direct ownership of own_latest_epoch and we create a new lease
     around it.
   *)
  wp_apply wp_GetTimeRange.
  iIntros (?????) "Htime".
  iMod (fupd_mask_subseteq (↑epochLeaseN)) as "Hmask".
  { set_solver. }
  set (newLeaseExpiration:=(word.add l (U64 1000000000))).
  destruct (decide (int.nat leaseExpiration < int.nat newLeaseExpiration)).
  { (* the newLeaseExpiration time is actually bigger *)
    iMod (get_lease_step newLeaseExpiration with "Htime Hepoch_lease") as (?) "($ & #? & #? & Hghost)".
    { word. }
    iMod "Hmask" as "_".
    iModIntro.
    wp_pures.
    wp_loadField.
    wp_if_destruct.
    2:{ exfalso. subst newLeaseExpiration. word. }
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ Hrep]").
    {
      iFrame "His_mu Hlocked".
      iNext.
      repeat iExists _.
      iFrame.
    }

    replace (slice.nil) with (slice_val Slice.nil) by done.
    wp_apply wp_WriteInt.
    { iApply is_slice_zero. }
    iIntros (?) "?".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "[$]").
    iIntros (?) "Hsl".
    wp_store.
    iModIntro.
    rewrite app_nil_l.
    iDestruct (is_slice_to_small with "Hsl") as "Hsl".
    iApply ("HΦ" with "[HΨ] [$] [$]").
    iLeft in "HΨ".
    iApply "HΨ"; done.
  }
  { (* the newLeaseExpiration time is smaller than the old lease expiration time. *)
    iMod (get_lease_step_old newLeaseExpiration with "Htime Hepoch_lease") as (?) "($ & #? & #? & Hghost)".
    { word. }
    iMod "Hmask" as "_".
    iModIntro.
    wp_pures.
    wp_loadField.
    wp_if_destruct.
    1:{ exfalso. subst newLeaseExpiration. word. }
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ Hrep]").
    {
      iFrame "His_mu Hlocked".
      iNext.
      repeat iExists _.
      iFrame.
    }

    replace (slice.nil) with (slice_val Slice.nil) by done.
    wp_apply wp_WriteInt.
    { iApply is_slice_zero. }
    iIntros (?) "?".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "[$]").
    iIntros (?) "Hsl".
    wp_store.
    iModIntro.
    rewrite app_nil_l.
    iDestruct (is_slice_to_small with "Hsl") as "Hsl".
    iApply ("HΦ" with "[HΨ] [$] [$]").
    iLeft in "HΨ".
    iApply "HΨ"; done.
  }
Qed.

Lemma wp_Clerk__GetEpochAndConfig (ck:loc) γ Φ :
  is_Clerk ck γ -∗
  □ (£ 1 -∗
      (|={⊤,∅}=> ∃ epoch conf, own_latest_epoch γ epoch ∗ own_config γ conf ∗
       (⌜int.nat epoch < int.nat (word.add epoch (U64 1))⌝ -∗
        own_latest_epoch γ (word.add epoch (U64 1)) -∗ own_config γ conf ={∅,⊤}=∗
         (∀ conf_sl, is_slice_small conf_sl uint64T 1 conf -∗
           Φ (#(U64 0), #(LitInt $ word.add epoch (U64 1)), slice_val conf_sl)%V)))
      ∧
      (∀ (err:u64) conf_sl, ⌜err ≠ 0⌝ -∗
           Φ (#err, #0, slice_val conf_sl)%V)
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
  iNamed "Hhost".
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  {
    iDestruct "Hhost" as "[$ _]".
  }
  {
    iModIntro.
    iNext.
    iIntros "Hlc".
    iDestruct ("HΦ" with "Hlc") as "Hupd".
    iSplit.
    { (* case: got a new epoch, no error *)
      iLeft in "Hupd".
      iMod "Hupd".
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
      wp_apply (wp_ref_of_zero).
      { done. }
      iIntros (err_ptr) "Herr_ptr".
      wp_load.
      rewrite Henc.
      wp_apply (wp_ReadInt with "Hrep_sl").
      iIntros (rep_sl1) "Hrep_sl".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_apply (wp_ReadInt with "Hrep_sl").
      iIntros (?) "Hrep_sl".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_apply (Config.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (?) "Hconf_own".
      wp_pures.
      wp_load.
      wp_load.
      wp_pures.
      iModIntro.
      iApply "Hupd".
      iFrame.
    }
    { (* case: got an error from the server; (i.e. lease is unexpired) *)
      iRight in "Hupd".
      iIntros (? Herr ? ? ? ?) "_".
      iIntros (?) "Hreply Hrep_sl".
      wp_pures.
      iRight.
      iModIntro.
      iSplitR; first done.
      wp_pures.
      wp_apply (wp_ref_of_zero).
      { done. }
      iIntros (epoch_ptr) "Hepoch".
      wp_pures.
      wp_apply (wp_ref_of_zero).
      { done. }
      iIntros (err_ptr) "Herr_ptr".
      wp_load.
      subst.
      wp_apply (wp_ReadInt with "Hrep_sl").
      iIntros (rep_sl1) "Hrep_sl".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_apply (wp_ReadInt with "Hrep_sl").
      iIntros (?) "Hrep_sl".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_apply (Config.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (?) "Hconf_own".
      wp_pures.
      wp_load.
      wp_load.
      wp_pures.
      iModIntro.
      iApply "Hupd".
      done.
    }
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

Lemma wp_Clerk__GetConfig (ck:loc) γ Φ :
  is_Clerk ck γ -∗
  □ (£ 1 ={⊤,∅}=∗ ∃ conf, own_config γ conf ∗ (own_config γ conf ={∅,⊤}=∗
      (∀ conf_sl, is_slice_small conf_sl uint64T 1 conf -∗ Φ (slice_val conf_sl)%V)
                                )
  ) -∗
  WP config.Clerk__GetConfig #ck {{ Φ }}
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
  iNamed "Hhost".
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  {
    iDestruct "Hhost" as "[_ [$ _]]".
  }
  {
    iModIntro.
    iNext.
    iIntros "Hlc".
    iMod ("HΦ" with "Hlc") as "Hupd".
    iModIntro.
    iDestruct "Hupd" as (?) "(H1&Hupd)".
    iExists _.
    iFrame "H1".
    iIntros.
    iMod ("Hupd" with "[$]") as "Hupd".
    iModIntro.
    iIntros (?) "%Henc_rep Hargs".
    iIntros (?) "Hrep Hrep_sl".
    wp_pures.
    iRight.
    iModIntro.
    iSplitR; first done.
    wp_pures.
    wp_load.
    wp_apply (Config.wp_Decode with "[$Hrep_sl]").
    { done. }
    iIntros (?) "Hconf_own".
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
  □ (£ 1 -∗ |={⊤,↑epochLeaseN}=> ∃ latest_epoch, own_latest_epoch γ latest_epoch ∗
      if (decide (latest_epoch = epoch)) then
        ∃ conf, own_config γ conf ∗ (own_config γ new_conf -∗ own_latest_epoch γ epoch ={↑epochLeaseN,⊤}=∗
                                      is_slice_small new_conf_sl uint64T 1 new_conf -∗
                                            Φ #0)
      else
        (own_latest_epoch γ latest_epoch ={↑epochLeaseN,⊤}=∗ (∀ (err:u64), ⌜err ≠ 0⌝ →
                                                         is_slice_small new_conf_sl uint64T 1 new_conf -∗
                                                         Φ #err))
  ) -∗
  (∀ (err:u64) , ⌜err ≠ 0⌝ → is_slice_small new_conf_sl uint64T 1 new_conf -∗ Φ #err) -∗
  WP config.Clerk__WriteConfig #ck #epoch (slice_val new_conf_sl)
  {{ Φ }}
.
Proof.
  iIntros "#Hck Hconf_sl #HΦ Hfail".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.

  wp_pures.
  iNamed "Hck".
  wp_apply (wp_slice_len).
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hargs_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (args_ptr) "Hargs".
  wp_pures.

  wp_load.
  wp_apply (wp_WriteInt with "Hargs_sl").
  iIntros (args_sl) "Hargs_sl".
  wp_store.
  wp_apply (Config.wp_Encode with "Hconf_sl").
  iIntros (enc_new_conf enc_new_conf_sl) "(%Henc_new_conf & Hconf & Henc_conf_sl)".
  wp_load.
  iDestruct (is_slice_to_small with "Henc_conf_sl") as "Henc_conf_sl".
  wp_apply (wp_WriteBytes with "[$Hargs_sl $Henc_conf_sl]").
  iIntros (args_sl2) "[Hargs_sl Henc_conf_sl]".
  replace (int.nat 0%Z) with 0%nat by word.
  wp_store.

  wp_apply (wp_frame_wand with "Hconf").

  wp_load.
  wp_loadField.
  iDestruct (is_slice_to_small with "Hargs_sl") as "Hargs_sl".
  iNamed "Hhost".
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  {
    iDestruct "Hhost" as "[_ [_ [$ _]]]".
  }
  {
    iModIntro.
    iNext.
    iExists _, _, _.
    iSplitR; first done.
    iSplitR; first done.
    iIntros "Hlc".
    iMod ("HΦ" with "Hlc") as "Hupd".
    iModIntro.
    iDestruct "Hupd" as (?) "(H1 & Hupd)".
    iExists _.
    iFrame "H1".
    destruct (decide (_)).
    {
      iDestruct "Hupd" as (?) "[H1 Hupd]".
      iExists _.
      iFrame "H1".
      iIntros "H1 H2".
      iMod ("Hupd" with "H1 H2") as "Hupd".
      iModIntro.
      iIntros (?) "%Henc_rep Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      rewrite Henc_rep.
      wp_apply (wp_ReadInt with "Hrep_sl").
      iIntros (?) "_".
      wp_pures.
      iModIntro.
      iIntros "Hconf".
      iApply "Hupd".
      iFrame.
    }
    {
      iIntros "H1".
      iMod ("Hupd" with "H1") as "Hupd".
      iModIntro.
      iIntros (err Herr_nz reply Henc_rep) "Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      rewrite Henc_rep.
      wp_apply (wp_ReadInt with "Hrep_sl").
      iIntros (?) "_".
      wp_pures.
      iModIntro.
      iIntros.
      iApply "Hupd".
      { done. }
      { iFrame. }
    }
  }
  {
    iIntros (err) "%Herr_nz Hargssl Hrep".
    wp_pures.
    wp_if_destruct.
    {
      exfalso. done.
    }
    iModIntro.
    iIntros.
    iApply "Hfail".
    { done. }
    done.
  }
Qed.

Lemma wp_Clerk__GetLease (ck:loc) γ epoch Φ :
  is_Clerk ck γ -∗
  □ ((∀ (leaseExpiration:u64) γl,
      is_lease epochLeaseN γl (own_latest_epoch γ epoch) -∗
      is_lease_valid_lb γl leaseExpiration -∗ Φ (#0, #leaseExpiration)%V) ∧
    (∀ (err:u64), ⌜err ≠ 0⌝ -∗ Φ (#err, #0)%V)
  ) -∗
  WP config.Clerk__GetLease #ck #epoch {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.

  wp_pures.
  iNamed "Hck".
  wp_apply (wp_NewSliceWithCap).
  { word. }
  iIntros (?) "Hargs_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (args_ptr) "Hargs".
  wp_pures.

  wp_load.
  wp_apply (wp_WriteInt with "Hargs_sl").
  iIntros (args_sl) "Hargs_sl".
  wp_store.
  wp_load.
  wp_loadField.
  iDestruct (is_slice_to_small with "Hargs_sl") as "Hargs_sl".
  iNamed "Hhost".
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  {
    iDestruct "Hhost" as "[_ [_ [_ [$ _]]]]".
  }
  {
    iModIntro.
    iNext.
    iExists _.
    iSplitR; first done.
    iSplit.
    { (* case: got lease *)
      iLeft in "HΦ".
      iIntros.
      wp_pures.
      wp_load.
      subst.
      wp_apply (wp_ReadInt with "[$]").
      iIntros. wp_pures.
      wp_apply (wp_ReadInt with "[$]").
      iIntros. wp_pures.
      iModIntro.
      iApply ("HΦ" with "[$] [$]").
    }
    { (* case: didn't get lease *)
      iRight in "HΦ".
      iIntros.
      wp_pures.
      wp_load.
      subst.
      wp_apply (wp_ReadInt with "[$]").
      iIntros. wp_pures.
      wp_apply (wp_ReadInt with "[$]").
      iIntros. wp_pures.
      iModIntro.
      iApply ("HΦ" with "[% //]").
    }
  }
  {
    iIntros (err) "%Herr_nz Hargssl Hrep".
    wp_pures.
    wp_if_destruct.
    {
      exfalso. done.
    }
    wp_pures.
    iModIntro.
    iIntros.
    iRight in "HΦ".
    iApply "HΦ".
    { done. }
  }
Qed.

Definition makeConfigServer_pre γ conf : iProp Σ := own_latest_epoch γ 0 ∗ own_config γ conf.

Lemma wp_MakeServer γ conf_sl conf :
  {{{
        makeConfigServer_pre γ conf ∗
        is_slice_small conf_sl uint64T 1 conf
  }}}
    config.MakeServer (slice_val conf_sl)
  {{{
        (s:loc), RET #s; is_Server s γ
  }}}.
Proof.
  iIntros (Φ) "([Hepoch Hconf] & Hconf_sl) HΦ".
  wp_call.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
  iIntros (s) "Hs".
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".
  simpl.
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (mu) "Hmu_inv".
  wp_storeField.
  wp_storeField.
  wp_storeField.
  iMod (readonly_alloc_1 with "mu") as "#Hmu".
  iApply "HΦ".
  iExists _.
  iMod (alloc_lock with "Hmu_inv [Hepoch Hconf epoch config leaseExpiration Hconf_sl]") as "$".
  {
    iNext.
    repeat iExists _.
    iFrame.
  }
  iFrame "Hmu".
  done.
Qed.

Lemma wp_Server__Serve s γ host :
  is_host host γ -∗ is_Server s γ -∗
  {{{
        True
  }}}
    config.Server__Serve #s #host
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros "#Hhost #His_srv !#" (Φ) "_ HΦ".
  wp_call.

  wp_apply (map.wp_NewMap).
  iIntros (handlers) "Hhandlers".

  wp_pures.
  wp_apply (wp_Server__GetEpochAndConfig).
  { done. }
  iIntros (getEpochFn) "#HgetEpochSpec".
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (wp_Server__GetConfig).
  { done. }
  iIntros (getFn) "#HgetSpec".
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (wp_Server__WriteConfig).
  { done. }
  iIntros (writeConfigFn) "#HwriteSpec".
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (wp_Server__GetLease).
  { done. }
  iIntros (getLeaseFn) "#HgetLeaseSpec".
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_apply (urpc_proof.wp_MakeServer with "Hhandlers").
  iIntros (r) "Hr".
  wp_pures.

  iNamed "Hhost".
  wp_apply (wp_StartServer2 with "[$Hr]").
  {
    set_solver.
  }
  {
    iDestruct "Hhost" as "(H1&H2&H3&H4&Hhandlers)".
    unfold handlers_complete.
    repeat rewrite dom_insert_L.
    rewrite dom_empty_L.
    iSplitL "".
    {
      iExactEq "Hhandlers".
      f_equal.
      set_solver.
    }

    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
    }
    by iApply big_sepM_empty.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End config_proof.

(*
  handler_spec γ.(urpc_gn) host (U64 0) (GetEpochAndConfig_spec γ) ∗
  handler_spec γ.(urpc_gn) host (U64 1) (GetConfig_spec γ) ∗
  handler_spec γ.(urpc_gn) host (U64 2) (WriteConfig_spec γ) ∗
  handlers_dom γ.(urpc_gn) {[ (U64 0) ; (U64 1) ; (U64 2)]}
*)

Section config_init.

Context `{!configG Σ}.
Context `{!gooseGlobalGS Σ}.

Definition config_spec_list γ :=
  [ (U64 0, GetEpochAndConfig_spec γ) ;
    (U64 1, GetConfig_spec γ) ;
    (U64 2, WriteConfig_spec γ) ;
    (U64 3, GetLease_spec γ)].

Lemma config_ghost_init conf :
  ⊢ |==> ∃ γ,
    makeConfigServer_pre γ conf ∗
    own_latest_epoch γ 0 ∗ own_config γ conf.
Proof.
  iMod (mono_nat_own_alloc 0) as (γepoch) "[[Hepoch Hepoch2] _]".
  iMod (ghost_var_alloc conf) as (γconf) "[Hconf Hconf2]".
  iExists {| epoch_gn := _ ; config_val_gn:= _ |}.
  iModIntro.
  iFrame.
Qed.

Lemma config_server_init host γ :
  host c↦ ∅ ={⊤}=∗
  is_host host γ.
Proof.
  iIntros "Hchan".
  iMod (handler_is_init_list2 host (config_spec_list γ) with "Hchan") as (γrpc) "H".
  { simpl. set_solver. }
  iModIntro.
  iExists γrpc.
  simpl.
  iDestruct "H" as "(H1 & $ & $ & $ & $ & _)".
  iExactEq "H1".
  f_equal.
  set_solver.
Qed.

End config_init.
