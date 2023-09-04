From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export config.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof Require Import marshal_stateless_proof std_proof.
From Perennial.program_proof.simplepb Require Import config_marshal_proof renewable_lease.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From coqutil.Datatypes Require Import List.

Module Config.
Section Config.

Definition C := list u64.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = u64_le (length args) ++ concat (u64_le <$> args).

Context `{!heapGS Σ}.

Definition own conf_sl (conf:list u64) : iProp Σ :=
  "Hargs_state_sl" ∷ own_slice_small conf_sl uint64T 1 conf.

Lemma wp_Encode conf_sl (conf:C) :
  {{{
        own conf_sl conf
  }}}
    config.EncodeConfig (slice_val conf_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc conf⌝ ∗
        own conf_sl conf ∗
        own_slice enc_sl byteT 1 enc
  }}}.
Proof.
  iIntros (Φ) "Hconf HΦ".
  wp_call.
  iDestruct (own_slice_small_sz with "Hconf") as %Hsz.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (enc_ptr) "Henc_sl".
  simpl.
  replace (int.nat 0) with (0%nat) by word.
  simpl.

  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc) "Henc".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (enc_sl) "Henc_sl".
  wp_store.
  simpl.

  replace (conf_sl.(Slice.sz)) with (U64 (length conf)) by word.
  set (P:=(λ (i:u64),
      ∃ enc_sl,
      "Henc_sl" ∷ own_slice enc_sl byteT 1 ((u64_le (length conf)) ++ concat (u64_le <$> (take (int.nat i) conf))) ∗
      "Henc" ∷ enc ↦[slice.T byteT] (slice_val enc_sl)
    )%I)
  .
  wp_apply (wp_forSlice P with "[] [$Hconf Henc Henc_sl]").
  {
    iIntros (i srv).
    clear Φ.
    iIntros (Φ) "!# (HP & %Hi_bound & %Hlookup) HΦ".
    iNamed "HP".

    wp_pures.
    wp_load.
    wp_apply (wp_WriteInt with "Henc_sl").
    iIntros (enc_sl') "Henc_sl".
    wp_store.
    iModIntro.
    iApply "HΦ".
    unfold P.
    iExists _; iFrame "Henc".
    iApply to_named.
    iExactEq "Henc_sl".
    f_equal.

    (* Start pure proof *)
    (* prove that appending the encoded next entry results in a concatenation of
       the first (i+1) entries *)
    rewrite -app_assoc.
    f_equal.
    replace (u64_le srv) with (concat (u64_le <$> [srv])) by done.
    rewrite -concat_app.
    rewrite -fmap_app.
    replace (int.nat (word.add i 1%Z)) with (int.nat i + 1)%nat by word.
    f_equal.
    f_equal.
    (* TODO: list_solver *)
    rewrite take_more; last word.
    f_equal.
    apply list_eq.
    intros.
    destruct i0.
    {
      simpl.
      rewrite lookup_take; last lia.
      rewrite lookup_drop.
      rewrite -Hlookup.
      f_equal.
      word.
    }
    {
      simpl.
      rewrite lookup_nil.
      rewrite lookup_take_ge; last word.
      done.
    }
    (* End pure proof *)
  }
  {
    unfold P.
    iExists _; iFrame.
  }
  iIntros "[HP Hconf_sl]".
  iNamed "HP".
  wp_pures.
  wp_load.
  iApply "HΦ".
  iFrame.
  rewrite -Hsz.
  iPureIntro.
  unfold has_encoding.
  rewrite firstn_all.
  done.
Qed.

Lemma list_copy_one_more_element {A} (l:list A) i e d:
  l !! i = Some e →
  <[i := e]> (take i l ++ replicate (length (l) - i) d)
    =
  (take (i + 1) l) ++ replicate (length (l) - i - 1) d.
Proof.
  intros Hlookup.
  apply list_eq.
  intros j.
  destruct (decide (j = i)) as [Heq|Hneq].
  {
    rewrite Heq.
    rewrite list_lookup_insert; last first.
    {
      rewrite app_length.
      rewrite replicate_length.
      apply lookup_lt_Some in Hlookup.
      rewrite take_length_le.
      { lia. }
      lia.
    }
    {
      rewrite lookup_app_l; last first.
      {
        rewrite take_length_le.
        { word. }
        apply lookup_lt_Some in Hlookup.
        word.
      }
      rewrite lookup_take; last word.
      done.
    }
  }
  {
    apply lookup_lt_Some in Hlookup.
    rewrite list_lookup_insert_ne; last done.
    destruct (decide (j < i)).
    {
      rewrite ?lookup_app_l ?take_length //; try lia; [].
      rewrite ?lookup_take; auto; lia.
    }
    assert (i < j) by lia.
    rewrite ?lookup_app_r ?take_length //; try lia; [].
    destruct (decide (j - i `min` length l < length l - i)).
    { rewrite ?lookup_replicate_2 //; lia. }
    { transitivity (@None A); [ | symmetry]; apply lookup_replicate_None; lia. }
  }
Qed.

Lemma wp_Decode enc enc_sl (conf:C) :
  {{{
        ⌜has_encoding enc conf⌝ ∗
        own_slice_small enc_sl byteT 1 enc
  }}}
    config.DecodeConfig (slice_val enc_sl)
  {{{
        conf_sl, RET (slice_val conf_sl); own conf_sl conf
  }}}.
Proof.
  iIntros (Φ) "[%Henc Henc_sl] HΦ".
  wp_call.
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (configLen_ptr) "HconfigLen".
  wp_pures.
  wp_load.
  rewrite Henc.
  wp_apply (wp_ReadInt with "[$Henc_sl]").
  iIntros (enc_sl') "Henc_sl".
  wp_store.
  wp_store.

  wp_load.
  wp_apply (wp_NewSlice).
  iIntros (conf_sl) "Hconf_sl".
  wp_pures.

  iDestruct (own_slice_small_sz with "Henc_sl") as %Henc_sz.
  (* prove that conf's length is below U64_MAX *)
  assert (int.nat (length conf) = length conf) as Hlen_no_overflow.
  {
    assert (length (concat (u64_le <$> conf)) ≥ length conf).
    {
      rewrite (length_concat_same_length 8).
      {
        rewrite fmap_length.
        word.
      }
      rewrite Forall_fmap.
      apply Forall_true.
      intros.
      done.
    }
    word.
  }
  rewrite Hlen_no_overflow.

  iDestruct (own_slice_to_small with "Hconf_sl") as "Hconf_sl".
  set (P:=(λ (i:u64),
      ∃ enc_sl,
      "Henc_sl" ∷ own_slice_small enc_sl byteT 1 (concat (u64_le <$> (drop (int.nat i) conf))) ∗
      "Henc" ∷ enc_ptr ↦[slice.T byteT] (slice_val enc_sl) ∗
      "Hconf_sl" ∷ own_slice_small conf_sl uint64T 1 ((take (int.nat i) conf) ++
                                                replicate (length conf - int.nat i) (U64 0))
    )%I)
  .
  wp_apply (wp_ref_to).
  { repeat econstructor. }
  iIntros (i_ptr) "Hi".
  wp_pures.

  iAssert (∃ (i:u64),
              "Hi" ∷ i_ptr ↦[uint64T] #i ∗
              "%Hi_bound" ∷  ⌜int.nat i ≤ length conf⌝ ∗
              P i)%I with "[Henc Henc_sl Hi Hconf_sl]" as "HP".
  {
    iExists _.
    iFrame.
    iSplitR; first iPureIntro.
    { word. }
    iExists _; iFrame.
    replace (int.nat 0) with 0%nat by word.
    rewrite Nat.sub_0_r.
    iFrame.
  }

  wp_forBreak_cond.
  iNamed "HP".
  iNamed "HP".

  wp_pures.
  wp_load.
  iDestruct (own_slice_small_sz with "Hconf_sl") as %Hconf_sz.

  (* Show that int.nat conf_sl.(Slice.sz) == int.nat (length conf) *)
  rewrite app_length in Hconf_sz.
  rewrite replicate_length in Hconf_sz.
  rewrite take_length_le in Hconf_sz; last first.
  { word. }
  assert (int.nat conf_sl.(Slice.sz) = length conf) as Hconf_sz_eq.
  { word. }

  wp_apply (wp_slice_len).
  wp_pures.

  wp_if_destruct.
  { (* continue with the loop *)
    assert (int.nat i < length conf) as Hi_bound_lt.
    {
      assert (int.nat i < int.nat conf_sl.(Slice.sz)) as Heqb_nat by word.
      rewrite Hconf_sz_eq in Heqb_nat.
      done.
    }

    wp_pures.
    wp_load.
    destruct (drop (int.nat i) conf) as [|] eqn:Hdrop.
    { (* contradiction with i < length *)
      exfalso.
      apply (f_equal length) in Hdrop.
      simpl in Hdrop.
      rewrite drop_length in Hdrop.
      word.
    }
    rewrite fmap_cons.
    rewrite concat_cons.
    wp_apply (wp_ReadInt with "[$Henc_sl]").
    iIntros (enc_sl1) "Henc_sl".
    wp_pures.
    wp_load.
    wp_apply (wp_SliceSet with "[$Hconf_sl]").
    {
      iPureIntro.
      apply lookup_lt_is_Some_2.
      rewrite app_length.
      rewrite take_length_le; last word.
      rewrite replicate_length.
      word.
    }
    iIntros "Hconf_sl".
    wp_pures.
    wp_store.
    wp_load.
    wp_store.

    iLeft.
    iModIntro.
    iSplitR; first done.
    iFrame "∗".
    iExists _; iFrame "∗".
    iSplitR.
    {
      iPureIntro. word.
    }
    unfold P.
    iExists _; iFrame "∗".
    replace (int.nat (word.add i 1%Z)) with (int.nat i + 1)%nat by word.
    iSplitL "Henc_sl".
    {
      iApply to_named.
      iExactEq "Henc_sl".
      f_equal.
      rewrite -drop_drop.
      rewrite Hdrop.
      simpl.
      done.
    }
    {
      iApply to_named.
      iExactEq "Hconf_sl".
      f_equal.
      rewrite list_copy_one_more_element.
      {
        f_equal.
        f_equal.
        word.
      }
      replace (int.nat i) with (int.nat i + 0)%nat by word.
      rewrite -(lookup_drop _ _ 0).
      rewrite Hdrop.
      done.
    }
  }
  (* done with loop *)

  iRight.
  iModIntro.
  iSplitR; first done.
  wp_pures.
  iApply "HΦ".

  replace (length conf - int.nat i)%nat with (0)%nat by word.
  replace (int.nat i) with (length conf) by word.
  simpl.
  rewrite app_nil_r.
  rewrite firstn_all.
  iFrame.
  done.
Qed.

End Config.
End Config.

Section config_global.

Record config_names :=
{
  epoch_gn:gname ;
  repoch_gn:gname ;
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

Definition own_reserved_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(repoch_gn) (1/2) (int.nat epoch).

Definition is_reserved_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(repoch_gn) (int.nat epoch).

Definition own_config γ (conf:list u64) : iProp Σ :=
  ghost_var γ.(config_val_gn) (1/2) conf
.

Definition epochLeaseN := nroot .@ "epochLeaseN".

Program Definition ReserveEpochAndGetConfig_core_spec γ Φ :=
  (
    £ 1 -∗
    (|={⊤,∅}=> ∃ reservedEpoch conf, own_reserved_epoch γ reservedEpoch ∗ own_config γ conf ∗
    (⌜int.nat reservedEpoch < int.nat (word.add reservedEpoch (U64 1))⌝ -∗
      own_reserved_epoch γ (word.add reservedEpoch (U64 1)) -∗ own_config γ conf ={∅,⊤}=∗
      Φ (word.add reservedEpoch 1) conf
      ))
    )%I.

Program Definition GetConfig_core_spec γ Φ :=
  (£ 1 ={⊤,∅}=∗ ∃ conf, own_config γ conf ∗ (own_config γ conf ={∅,⊤}=∗ Φ conf))%I.

Program Definition TryWriteConfig_core_spec γ (epoch:u64) (new_conf:list u64) Φ : iProp Σ :=
  is_reserved_epoch_lb γ epoch ∗
  (£ 1 -∗ |={⊤,↑epochLeaseN}=> ∃ latest_epoch reserved_epoch,
   own_latest_epoch γ latest_epoch ∗
   own_reserved_epoch γ reserved_epoch ∗
   if (decide (reserved_epoch = epoch)) then
     ∃ conf, own_config γ conf ∗
                        (own_config γ new_conf -∗
                         own_reserved_epoch γ reserved_epoch -∗
                         own_latest_epoch γ epoch ={↑epochLeaseN,⊤}=∗ Φ (U64 0))
      else
        (own_latest_epoch γ latest_epoch -∗
         own_reserved_epoch γ reserved_epoch
         ={↑epochLeaseN,⊤}=∗ (∀ (err:u64), ⌜err ≠ 0⌝ → Φ err))
  ).

Program Definition GetLease_core_spec γ (epoch:u64) Φ : iProp Σ :=
  (∀ (leaseExpiration:u64) γl,
    is_lease epochLeaseN γl (own_latest_epoch γ epoch) -∗
    is_lease_valid_lb γl leaseExpiration -∗ Φ (U64 0) leaseExpiration
  ) ∧
  (∀ (err:u64), ⌜err ≠ 0⌝ → Φ err (U64 0))
.

Program Definition ReserveEpochAndGetConfig_spec γ :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( (* no args *)
    ReserveEpochAndGetConfig_core_spec γ (λ newEpoch conf,
                                  ∀ reply enc_conf,
                                   ⌜Config.has_encoding enc_conf conf⌝ -∗
                                   ⌜reply = u64_le newEpoch ++ enc_conf⌝ -∗
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

Program Definition TryWriteConfig_spec γ :=
  λ (enc_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( ∃ epoch new_conf enc_new_conf,
    ⌜enc_args = u64_le epoch ++ enc_new_conf⌝ ∗
    ⌜Config.has_encoding enc_new_conf new_conf⌝ ∗
    TryWriteConfig_core_spec γ epoch new_conf (λ err, ∀ reply,
                                   ⌜reply = u64_le err⌝ -∗
                                   Φ reply
                                  )
    )%I.
Next Obligation.
  unfold TryWriteConfig_core_spec.
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

Definition is_config_host (host:u64) γ : iProp Σ :=
  ∃ γrpc,
  is_urpc_spec_pred γrpc host (U64 0) (ReserveEpochAndGetConfig_spec γ) ∗
  is_urpc_spec_pred γrpc host (U64 1) (GetConfig_spec γ) ∗
  is_urpc_spec_pred γrpc host (U64 2) (TryWriteConfig_spec γ) ∗
  is_urpc_spec_pred γrpc host (U64 3) (GetLease_spec γ) ∗
  is_urpc_dom γrpc {[ (U64 0) ; (U64 1) ; (U64 2) ; (U64 3) ]}
.

End config_global.

Section config_proof.

Context `{!heapGS Σ}.
Context `{!configG Σ}.

Definition is_Clerk (ck:loc) γ : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[config.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_uRPCClient cl srv ∗
  "#Hhost" ∷ is_config_host srv γ
.

Lemma wp_MakeClerk configHost γ:
  {{{
      is_config_host configHost γ
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
  iMod (lease_expire with "Hexp Hpost_lease Htime_lb") as ">$"; done.
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
      { done. }
      replace (↑epochLeaseN ∖ ↑epochLeaseN) with (∅:coPset) by set_solver.
      iModIntro.
      iIntros "Hepoch".
      iMod ("HH" with "Hepoch") as "$".
      iModIntro.
      iLeft.
      iExists _; iFrame "∗#".
    }
    { (* case: lease is expired.  *)
      iDestruct (own_time_get_lb with "Ht") as "#Hlb".
      iMod (lease_expire with "Hexp Hpost [Hlb]") as ">Hepoch".
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
  ∃ (epoch reservedEpoch leaseExpiration:u64) (conf:list u64) conf_sl (wantLeaseToExpire:bool),
  "Hepoch" ∷ s ↦[config.Server :: "epoch"] #epoch ∗
  "HreservedEpoch" ∷ s ↦[config.Server :: "reservedEpoch"] #reservedEpoch ∗
  "HleaseExpiration" ∷ s ↦[config.Server :: "leaseExpiration"] #leaseExpiration ∗
  "HwantLeaseToExpire" ∷ s ↦[config.Server :: "wantLeaseToExpire"] #wantLeaseToExpire ∗
  "Hconf" ∷ s ↦[config.Server :: "config"] (slice_val conf_sl) ∗
  "Hconf_sl" ∷ own_slice_small conf_sl uint64T 1 conf ∗
  "Hepoch_lease" ∷ own_Config_ghost γ leaseExpiration epoch ∗
  "Hconf_ghost" ∷ own_config γ conf ∗
  "Hreserved_ghost" ∷ own_reserved_epoch γ reservedEpoch ∗
  "%HresIneq" ∷ ⌜int.nat epoch <= int.nat reservedEpoch⌝
.

Definition configN := nroot .@ "config".

Definition is_Server (s:loc) γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[config.Server :: "mu"] mu) ∗
  "#His_mu" ∷ is_lock configN mu (own_Server s γ).

Lemma wp_Server__ReserveEpochAndGetConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config.Server__ReserveEpochAndGetConfig #server
  {{{
        (f:val), RET f; is_urpc_handler_pred f (ReserveEpochAndGetConfig_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold is_urpc_handler_pred.
  clear Φ.
  iIntros (enc_args Ψ req_sl rep_ptr) "!# %Φ (Harg_sl & Hrep & HΨ) HΦ".
  wp_call.

  iNamed "His_srv".
  wp_loadField.
  wp_apply (acquire_spec with "[$His_mu]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pure1_credit "Hlc".
  wp_loadField.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (?). wp_storeField.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (ptr) "Hsl".
  wp_store.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (enc_sl) "Hrep_sl".
  wp_store.
  wp_loadField.
  wp_apply (Config.wp_Encode with "[Hconf_sl]").
  { iFrame. }
  iIntros (enc_conf enc_conf_sl) "(%Hconf_enc & Hconf_sl & Henc_conf_sl)".
  wp_load.
  wp_apply (wp_WriteBytes with "[$Hrep_sl Henc_conf_sl]").
  {
    iDestruct (own_slice_to_small with "Henc_conf_sl") as "$".
  }
  iIntros (rep_sl) "[Hrep_sl Henc_conf_sl]".
  replace (int.nat 0%Z) with 0%nat by word.
  wp_store.
  wp_loadField.

  iApply fupd_wp.
  iSpecialize ("HΨ" with "Hlc").
  iMod "HΨ".
  iDestruct "HΨ" as (??) "(Hreserved_ghost2 & Hconf_ghost2 & Hupd)".
  iDestruct (ghost_var_agree with "Hconf_ghost Hconf_ghost2") as %->.
  iDestruct (mono_nat_auth_own_agree with "Hreserved_ghost Hreserved_ghost2") as %[_ Heq].
  assert (reservedEpoch0 = reservedEpoch) by word; subst.
  iCombine "Hreserved_ghost Hreserved_ghost2" as "Hreserved_ghost".
  iMod (mono_nat_own_update (int.nat (word.add reservedEpoch 1)) with "Hreserved_ghost") as "[[Hreserved_ghost Hreserved_ghost2] _]".
  { word. }
  iSpecialize ("Hupd" with "[%] Hreserved_ghost2 Hconf_ghost2").
  { word. }
  iMod "Hupd".
  iModIntro.

  wp_apply (release_spec with "[- Hrep Hrep_sl Hupd HΦ]").
  {
    iFrame "His_mu Hlocked". iNext.
    repeat iExists _.
    iFrame "∗#%".
    iPureIntro. word.
  }
  wp_pures.
  iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
  iSpecialize ("Hupd" with "[% //] [% //]").
  iModIntro. iApply "HΦ".
  iFrame.
Qed.

Lemma wp_Server__GetConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config.Server__GetConfig #server
  {{{
        (f:val), RET f; is_urpc_handler_pred f (GetConfig_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold is_urpc_handler_pred.
  clear Φ.
  iIntros (enc_args Ψ req_sl rep_ptr) "!# %Φ (Harg_sl & Hrep & HΨ) HΦ".
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

  wp_apply (release_spec with "[- Hrep Hrep_sl Hupd HΦ]").
  {
    iFrame "His_mu Hlocked". iNext.
    repeat iExists _.
    iFrame "∗#%".
  }
  wp_pures.
  iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
  iSpecialize ("Hupd" with "[% //]").
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma wp_Server__TryWriteConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config.Server__TryWriteConfig #server
  {{{
        (f:val), RET f; is_urpc_handler_pred f (TryWriteConfig_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold is_urpc_handler_pred.
  clear Φ.
  iIntros (enc_args Ψ req_sl rep_ptr) "!# %Φ (Harg_sl & Hrep & HΨ) HΦ".
  wp_call.
  iDestruct "HΨ" as (new_epoch new_conf enc_new_conf) "(%Henc & %Henc_conf & HΨ)".
  rewrite Henc.
  wp_apply (wp_ReadInt with "Harg_sl").
  iIntros (args_sl) "Hargs_sl".
  wp_pure1_credit "Hlc".
  wp_pures.
  iNamed "His_srv".
  wp_forBreak.
  wp_pures.

  wp_loadField.
  wp_apply (acquire_spec with "[$His_mu]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  iDestruct "HΨ" as "(#Hepoch_lb & HΨ)".

  replace (slice.nil) with (slice_val Slice.nil) by done.
  wp_loadField.
  wp_if_destruct.
  { (* case: higher epoch is reserved *)
    wp_apply (wp_WriteInt with "[]").
    {
      iApply own_slice_zero.
    }
    iIntros (rep_sl) "Hrep_sl".
    wp_store.
    wp_loadField.

    unfold TryWriteConfig_core_spec.
    iApply fupd_wp.
    iMod ("HΨ" with "Hlc") as (??) "(Hlatest & Hreserved & HΨ)".
    iDestruct (mono_nat_auth_own_agree with "Hreserved Hreserved_ghost") as %[_ ?]; subst.
    rewrite decide_False.
    2: { destruct (decide (reserved_epoch = new_epoch)).
         { subst. exfalso. word. }
         done. }
    iMod ("HΨ" with "Hlatest Hreserved") as "HΨ".
    iModIntro.
    wp_apply (release_spec with "[-HΦ HΨ Hrep Hargs_sl Hrep_sl]").
    {
      iFrame "#∗". repeat iExists _; iFrame "∗#%".
    }
    wp_pures.
    iRight. iSplitR; first done.
    iModIntro. wp_pures.
    iDestruct ("HΨ" with "[%] [% //]") as "HΨ".
    { instantiate (1:=1). done. }
    rewrite app_nil_l.
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iModIntro. iApply "HΦ". iFrame.
  }
  iDestruct (mono_nat_lb_own_valid with "Hreserved_ghost Hepoch_lb") as %Hineq.
  assert (new_epoch = reservedEpoch); subst.
  { destruct Hineq as [_ ?]. word. }
  wp_loadField.
  wp_if_destruct.
  { (* case: wait for lease to expire, so we can enter the new epoch *)
    wp_apply wp_GetTimeRange.
    iIntros (?????) "Htime".
    iDestruct (own_time_get_lb with "Htime") as "#Htime_lb".
    iFrame "Htime".
    iModIntro.

    wp_loadField.
    wp_if_destruct.
    2:{ (* case: loop again *)
      wp_storeField.
      wp_loadField.
      wp_loadField.
      wp_apply (release_spec with "[-HΨ HΦ Hrep Hlc Hargs_sl]").
      { iFrame "#∗". repeat iExists _; iFrame "∗#%". }
      wp_pures.
      wp_apply wp_Sleep.
      wp_pures.
      iLeft.
      iModIntro. iSplitR; first done.
      iFrame "∗#".
    }
    (* eventually, lease expired *)
    wp_storeField.
    wp_storeField.

    wp_apply (Config.wp_Decode with "[$Hargs_sl]").
    { done. }
    iIntros (new_conf_sl) "Hnew_conf_sl".
    wp_storeField.
    wp_apply (wp_WriteInt with "[]").
    { iApply own_slice_zero. }
    iIntros (rep_sl) "Hrep_sl".
    wp_store.
    wp_loadField.

    iApply fupd_wp.
    iMod (fupd_mask_subseteq (↑epochLeaseN)) as "Hmask".
    { set_solver. }
    iMod (lease_expired_get_epoch with "[Htime_lb] Hepoch_lease") as "Hepoch_ghost".
    { iApply is_time_lb_mono; last done. word. }
    iMod "Hmask".
    iSpecialize ("HΨ" with "Hlc").
    iMod "HΨ".
    iDestruct "HΨ" as (??) "(Hepoch_ghost2 & Hres2 & HΨ)".
    iDestruct (mono_nat_auth_own_agree with "Hreserved_ghost Hres2") as %[_ ?].
    assert (reserved_epoch = reservedEpoch) by word; subst.
    rewrite decide_True.
    2: { word. }
    iDestruct "HΨ" as (?) "(Hconf_ghost2 & Hupd)".
    iDestruct (ghost_var_agree with "Hconf_ghost Hconf_ghost2") as %->.
    iDestruct (mono_nat_auth_own_agree with "Hepoch_ghost Hepoch_ghost2") as %[_ Heq].
    replace (latest_epoch) with (epoch) by word.
    iCombine "Hepoch_ghost Hepoch_ghost2" as "Hepoch_ghost".
    iMod (mono_nat_own_update (int.nat reservedEpoch) with "Hepoch_ghost") as "[[Hepoch_ghost Hepoch_ghost2] _]".
    { word. }
    iCombine "Hconf_ghost Hconf_ghost2" as "Hconf_ghost".
    iMod (ghost_var_update new_conf with "Hconf_ghost") as "[Hconf_ghost Hconf_ghost2]".
    iMod ("Hupd" with "Hconf_ghost2 Hres2 Hepoch_ghost2") as "HΨ".
    iModIntro.
    wp_apply (release_spec with "[- Hrep Hrep_sl HΨ HΦ]").
    {
      iFrame "#∗".
      repeat iExists _; iFrame "∗#%".
      done.
    }
    wp_pures.
    iRight.
    iModIntro; iSplitR; first done.
    wp_pures.
    iSpecialize ("HΨ" $!_ with "[//]").
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iModIntro. iApply "HΦ". iFrame.
  }
  { (* case: already in epoch *)
    wp_apply (Config.wp_Decode with "[$Hargs_sl]").
    { done. }
    iIntros (new_conf_sl) "Hnew_conf_sl".
    wp_storeField.

    wp_apply wp_time_acc.
    { done. }
    iIntros (t) "Htime".
    iMod ("HΨ" with "Hlc") as "HΨ".
    iDestruct "HΨ" as (??) "(Hepoch_ghost2 & Hres2 & HΨ)".
    iDestruct (mono_nat_auth_own_agree with "Hreserved_ghost Hres2") as %[_ ?].
    assert (reserved_epoch = reservedEpoch) by word; subst.
    rewrite decide_True.
    2: { word. }
    iDestruct "HΨ" as (?) "(Hconf_ghost2 & Hupd)".
    iDestruct (ghost_var_agree with "Hconf_ghost Hconf_ghost2") as %->.

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
    assert (latest_epoch = reservedEpoch) by word; subst.

    iCombine "Hconf_ghost Hconf_ghost2" as "Hconf_ghost".
    iMod (ghost_var_update new_conf with "Hconf_ghost") as "[Hconf_ghost Hconf_ghost2]".
    iMod ("Hupd" with "Hconf_ghost2 Hres2 Hepoch_ghost2") as "HΨ".
    iModIntro. iFrame "Htime".
    wp_loadField.
    wp_apply (release_spec with "[- Hrep HΨ HΦ]").
    {
      iFrame "#∗".
      repeat iExists _; iFrame "∗#%".
    }
    wp_apply (wp_WriteInt with "[]").
    { iApply own_slice_zero. }
    iIntros (rep_sl) "Hrep_sl".
    wp_store.
    iRight.
    iModIntro; iSplitR; first done.
    wp_pures.
    iSpecialize ("HΨ" $!_ with "[//]").
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iModIntro. iApply "HΦ". iFrame.
  }
Qed.

Lemma get_lease_step newLeaseExpiration γ epoch leaseExpiration :
  int.nat leaseExpiration <= int.nat newLeaseExpiration →
  own_Config_ghost γ leaseExpiration epoch
  ={↑epochLeaseN}=∗
  ∃ γl,
  is_lease epochLeaseN γl (own_latest_epoch γ epoch) ∗
  is_lease_valid_lb γl newLeaseExpiration ∗
  own_Config_ghost γ newLeaseExpiration epoch
.
Proof.
  iIntros (?) "Hghost".
  iDestruct "Hghost" as "[Hlease|Hepoch]".
  {(* renew the existing lease *)
    iDestruct "Hlease" as (?) "(#Hlease & Hexp & Hpost)".
    iMod (lease_renew newLeaseExpiration with "[$] [$]") as "[Hpost Hexp]".
    { done. }
    iModIntro.
    iDestruct (lease_get_lb with "Hexp") as "#?".
    iExists _; iFrame "∗#".
    iLeft. iExists _; iFrame "∗#".
  }
  { (* create a new lease *)
    iMod (lease_alloc newLeaseExpiration with "Hepoch") as (?) "(#Hlease & Hpost & Hexp)".
    iDestruct (lease_get_lb with "Hexp") as "#?".
    iModIntro.
    iExists _; iFrame "∗#".
    iLeft. iExists _; iFrame "∗#".
  }
Qed.

(* FIXME: move this somewhere else *)
Global Instance bool_eqdec : EqDecision bool.
Proof. solve_decision. Defined.

(* FIXME: move this somewhere else *)
Global Instance bool_eq_dec (b1 b2:bool) : Decision (b1 = b2).
Proof. solve_decision. Defined.

Lemma wp_Server__GetLease (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config.Server__GetLease #server
  {{{
        (f:val), RET f; is_urpc_handler_pred f (GetLease_spec γ)
  }}}.
Proof.
  iIntros (Φ) "#His_srv HΦ".
  wp_call.
  iApply "HΦ".
  iModIntro.
  unfold is_urpc_handler_pred.
  clear Φ.
  iIntros (enc_args Ψ req_sl rep_ptr) "!# %Φ (Harg_sl & Hrep & HΨ) HΦ".
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
  wp_apply (wp_or with "[HwantLeaseToExpire]").
  { iNamedAccu. }
  { wp_pures. iPureIntro. by rewrite -bool_decide_not. }
  { iIntros. wp_loadField. iFrame. iPureIntro.
    repeat f_equal.
    instantiate (2:=(wantLeaseToExpire = true)).
    Unshelve. 2:{ apply _. }
    by destruct wantLeaseToExpire.
  }
  iNamed 1.
  wp_if_destruct.
  { (* case: epoch number that the caller wants is not the latest epoch, or wantToExpireLease *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ Hrep]").
    {
      iFrame "His_mu Hlocked".
      iNext.
      repeat iExists _.
      iFrame "∗#%".
    }
    replace (slice.nil) with (slice_val Slice.nil) by done.
    wp_apply (wp_WriteInt with "[]").
    { iApply own_slice_zero. }
    iIntros (?) "Hsl".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "[$]").
    iIntros (?) "Hsl".
    wp_store.
    iRight in "HΨ".
    iDestruct (own_slice_to_small with "Hsl") as "Hsl".
    iApply "HΦ". iFrame.
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
  iIntros (?????) "$".
  iMod (fupd_mask_subseteq (↑epochLeaseN)) as "Hmask".
  { set_solver. }
  set (newLeaseExpiration:=(word.add l (U64 1000000000))).
  assert (epoch0 = epoch); last subst.
  {
    apply Decidable.not_or in Heqb.
    destruct Heqb as [? ?].
    apply dec_stable in H1.
    by injection H1.
  }
  destruct (decide (int.nat leaseExpiration < int.nat newLeaseExpiration)).
  { (* the newLeaseExpiration time is actually bigger *)
    iMod (get_lease_step newLeaseExpiration with "Hepoch_lease") as (?) "(#? & #? & Hghost)".
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
      iFrame "∗#%".
    }

    replace (slice.nil) with (slice_val Slice.nil) by done.
    wp_apply wp_WriteInt.
    { iApply own_slice_zero. }
    iIntros (?) "?".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "[$]").
    iIntros (?) "Hsl".
    wp_store.
    iModIntro.
    rewrite app_nil_l.
    iDestruct (own_slice_to_small with "Hsl") as "Hsl".
    iApply "HΦ". iFrame.
    iLeft in "HΨ".
    iApply "HΨ"; done.
  }
  { (* the newLeaseExpiration time is smaller than the old lease expiration time. *)
    iMod (get_lease_step leaseExpiration with "Hepoch_lease") as (?) "(#? & #Hlb2 & Hghost)".
    { word. }
    iDestruct (lease_lb_mono _ _ newLeaseExpiration with "Hlb2") as "#Hlb".
    { word. }
    iClear "Hlb2".
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
      iFrame "∗#%".
    }

    replace (slice.nil) with (slice_val Slice.nil) by done.
    wp_apply wp_WriteInt.
    { iApply own_slice_zero. }
    iIntros (?) "?".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "[$]").
    iIntros (?) "Hsl".
    wp_store.
    iModIntro.
    rewrite app_nil_l.
    iDestruct (own_slice_to_small with "Hsl") as "Hsl".
    iApply "HΦ". iFrame.
    iLeft in "HΨ".
    iApply "HΨ"; done.
  }
Qed.

Lemma wp_Clerk__ReserveEpochAndGetConfig (ck:loc) γ Φ :
  is_Clerk ck γ -∗
  □ (£ 1 -∗
      (|={⊤,∅}=> ∃ epoch conf, own_reserved_epoch γ epoch ∗ own_config γ conf ∗
       (⌜int.nat epoch < int.nat (word.add epoch (U64 1))⌝ -∗
        own_reserved_epoch γ (word.add epoch (U64 1)) -∗ own_config γ conf ={∅,⊤}=∗
         (∀ conf_sl, own_slice_small conf_sl uint64T 1 conf -∗
           Φ (#(LitInt $ word.add epoch (U64 1)), slice_val conf_sl)%V)))
  ) -∗
  WP config.Clerk__ReserveEpochAndGetConfig #ck {{ Φ }}
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
  iDestruct (own_slice_to_small with "Hargs") as "Hargs_sl".
  iNamed "Hhost".
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  {
    iDestruct "Hhost" as "[$ _]".
  }
  iSplit.
  {
    iModIntro.
    iNext.
    iIntros "Hlc".
    iDestruct ("HΦ" with "Hlc") as "Hupd".
    (* case: got a new epoch, no error *)
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

Lemma wp_Clerk__GetConfig (ck:loc) γ Φ :
  is_Clerk ck γ -∗
  □ (£ 1 ={⊤,∅}=∗ ∃ conf, own_config γ conf ∗ (own_config γ conf ={∅,⊤}=∗
      (∀ conf_sl, own_slice_small conf_sl uint64T 1 conf -∗ Φ (slice_val conf_sl)%V)
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
  iDestruct (own_slice_to_small with "Hargs") as "Hargs_sl".
  iNamed "Hhost".
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  {
    iDestruct "Hhost" as "[_ [$ _]]".
  }
  iSplit.
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

Lemma wp_Clerk__TryWriteConfig (ck:loc) new_conf new_conf_sl epoch γ Φ :
  is_Clerk ck γ -∗
  own_slice_small new_conf_sl uint64T 1 new_conf -∗
  is_reserved_epoch_lb γ epoch -∗
  □ (£ 1 -∗ |={⊤,↑epochLeaseN}=> ∃ latest_epoch reserved_epoch,
    own_latest_epoch γ latest_epoch ∗
    own_reserved_epoch γ reserved_epoch ∗
      if (decide (reserved_epoch = epoch)) then
        ∃ conf, own_config γ conf ∗ (own_config γ new_conf -∗
                                     own_reserved_epoch γ reserved_epoch -∗
                                     own_latest_epoch γ epoch
                                     ={↑epochLeaseN,⊤}=∗
                                      own_slice_small new_conf_sl uint64T 1 new_conf -∗
                                            Φ #0)
      else
        (own_latest_epoch γ latest_epoch -∗
         own_reserved_epoch γ reserved_epoch
         ={↑epochLeaseN,⊤}=∗ (∀ (err:u64), ⌜err ≠ 0⌝ →
                                own_slice_small new_conf_sl uint64T 1 new_conf -∗ Φ #err))
  ) -∗
  (∀ (err:u64) , ⌜err ≠ 0⌝ → own_slice_small new_conf_sl uint64T 1 new_conf -∗ Φ #err) -∗
  WP config.Clerk__TryWriteConfig #ck #epoch (slice_val new_conf_sl)
  {{ Φ }}
.
Proof.
  iIntros "#Hck Hconf_sl #Hlb #HΦ Hfail".
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
  iDestruct (own_slice_to_small with "Henc_conf_sl") as "Henc_conf_sl".
  wp_apply (wp_WriteBytes with "[$Hargs_sl $Henc_conf_sl]").
  iIntros (args_sl2) "[Hargs_sl Henc_conf_sl]".
  replace (int.nat 0%Z) with 0%nat by word.
  wp_store.

  wp_apply (wp_frame_wand with "Hconf").

  wp_load.
  wp_loadField.
  iDestruct (own_slice_to_small with "Hargs_sl") as "Hargs_sl".
  iNamed "Hhost".
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  {
    iDestruct "Hhost" as "[_ [_ [$ _]]]".
  }
  iSplit.
  {
    iModIntro.
    iNext.
    iExists _, _, _.
    iSplitR; first done.
    iSplitR; first done.
    iFrame "#".
    iIntros "Hlc".
    iMod ("HΦ" with "Hlc") as "Hupd".
    iModIntro.
    iDestruct "Hupd" as (??) "(H1 & H2 & Hupd)".
    iExists _, _; iFrame.
    destruct (decide (_)).
    {
      iDestruct "Hupd" as (?) "[H1 Hupd]".
      iExists _.
      iFrame "H1".
      iIntros "H1 H2 H3".
      iMod ("Hupd" with "H1 H2 H3") as "Hupd".
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
      iIntros "H1 H2".
      iMod ("Hupd" with "H1 H2") as "Hupd".
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
  iDestruct (own_slice_to_small with "Hargs_sl") as "Hargs_sl".
  iNamed "Hhost".
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  {
    iDestruct "Hhost" as "[_ [_ [_ [$ _]]]]".
  }
  iSplit.
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

Definition makeConfigServer_pre γ conf : iProp Σ :=
  own_latest_epoch γ 0 ∗ own_reserved_epoch γ 0 ∗ own_config γ conf.

Lemma wp_MakeServer γ conf_sl conf :
  {{{
        makeConfigServer_pre γ conf ∗
        own_slice_small conf_sl uint64T 1 conf
  }}}
    config.MakeServer (slice_val conf_sl)
  {{{
        (s:loc), RET #s; is_Server s γ
  }}}.
Proof.
  iIntros (Φ) "((Hepoch & Hres & Hconf) & Hconf_sl) HΦ".
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
  iMod (alloc_lock with "Hmu_inv [Hepoch Hres reservedEpoch Hconf epoch config leaseExpiration wantLeaseToExpire Hconf_sl]") as "$".
  {
    iNext.
    repeat iExists _.
    iFrame. done.
  }
  iFrame "Hmu".
  done.
Qed.

Lemma wp_Server__Serve s γ host :
  is_config_host host γ -∗ is_Server s γ -∗
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

  wp_apply (map.wp_NewMap u64).
  iIntros (handlers) "Hhandlers".

  wp_pures.
  wp_apply (wp_Server__ReserveEpochAndGetConfig).
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
  wp_apply (wp_Server__TryWriteConfig).
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
  wp_apply (wp_StartServer_pred with "[$Hr]").
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

Section config_init.

Context `{!configG Σ}.
Context `{!gooseGlobalGS Σ}.

Definition config_spec_list γ :=
  [ (U64 0, ReserveEpochAndGetConfig_spec γ) ;
    (U64 1, GetConfig_spec γ) ;
    (U64 2, TryWriteConfig_spec γ) ;
    (U64 3, GetLease_spec γ)].

Lemma config_ghost_init conf :
  ⊢ |==> ∃ γ,
    makeConfigServer_pre γ conf ∗
    own_reserved_epoch γ 0 ∗
    own_latest_epoch γ 0 ∗ own_config γ conf.
Proof.
  iMod (mono_nat_own_alloc 0) as (γepoch) "[[Hepoch Hepoch2] _]".
  iMod (mono_nat_own_alloc 0) as (γres) "[[Hres Hres2] _]".
  iMod (ghost_var_alloc conf) as (γconf) "[Hconf Hconf2]".
  iExists {| epoch_gn := γepoch ; config_val_gn:= _ ; repoch_gn := γres |}.
  iModIntro.
  iFrame.
Qed.

Lemma config_server_init host γ :
  host c↦ ∅ ={⊤}=∗
  is_config_host host γ.
Proof.
  iIntros "Hchan".
  iMod (alloc_is_urpc_list_pred host (config_spec_list γ) with "Hchan") as (γrpc) "H".
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
