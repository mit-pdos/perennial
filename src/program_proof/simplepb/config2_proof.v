From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export config2.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof Require Import marshal_stateless_proof std_proof.
From Perennial.program_proof.simplepb Require Import config_marshal_proof renewable_lease.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From Perennial.program_proof.mpaxos Require Import tryacquire_proof.

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
    config_mpG :> mpG Σ ;
    config_leaseG :> renewable_leaseG Σ ;
}.

Definition configΣ := #[mono_natΣ ; ghost_varΣ (list u64) ; urpcregΣ ; renewable_leaseΣ ].

Global Instance subG_configΣ {Σ} : subG configΣ Σ → configG Σ.
Proof. intros. (* solve_inG. Qed. *)
       Admitted. (* FIXME: mpΣ *)

Implicit Type γ : config_names.

Context `{!gooseGlobalGS Σ}.
Context `{!configG Σ}.
Context {N:namespace}.

Definition own_latest_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) (1/2) (int.nat epoch).

Definition own_reserved_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(repoch_gn) (1/2) (int.nat epoch).

Definition is_reserved_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(repoch_gn) (int.nat epoch).

Definition own_config γ (conf:list u64) : iProp Σ :=
  ghost_var γ.(config_val_gn) (1/2) conf
.

Definition epochLeaseN := N .@ "epochLeaseN".

Program Definition ReserveEpochAndGetConfig_core_spec γ Φ :=
  (
    £ 1 -∗
    (|={⊤∖↑N,∅}=> ∃ reservedEpoch conf, own_reserved_epoch γ reservedEpoch ∗ own_config γ conf ∗
    (⌜int.nat reservedEpoch < int.nat (word.add reservedEpoch (U64 1))⌝ -∗
      own_reserved_epoch γ (word.add reservedEpoch (U64 1)) -∗ own_config γ conf ={∅,⊤∖↑N}=∗
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
                                  ∀ enc_conf,
                                   ⌜Config.has_encoding enc_conf conf⌝ -∗
                                   Φ (u64_le 0 ++ u64_le newEpoch ++ enc_conf)
                                  ) ∗
    (∀ err, ⌜ err ≠ U64 0 ⌝ -∗ Φ (u64_le err))
    )%I.
Next Obligation.
  rewrite /ReserveEpochAndGetConfig_core_spec.
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

Module state.
Section state.
Record t :=
  mk {
      epoch : u64 ;
      reservedEpoch : u64 ;
      leaseExpiration : u64 ;
      wantLeaseToExpire : bool ;
      config : list u64 ;
    }.

Definition encode (x:t) : list u8.
Admitted.

Context `{!heapGS Σ}.
Definition own (l:loc) (x:t) : iProp Σ :=
  ∃ conf_sl,
  "Hepoch" ∷ l ↦[state :: "epoch"] #x.(epoch) ∗
  "HreservedEpoch" ∷ l ↦[state :: "reservedEpoch"] #x.(reservedEpoch) ∗
  "HleaseExpiration" ∷ l ↦[state :: "leaseExpiration"] #x.(leaseExpiration) ∗
  "HwantLeaseToExpire" ∷ l ↦[state :: "wantLeaseToExpire"] #x.(wantLeaseToExpire) ∗
  "Hconf" ∷ l ↦[state :: "config"] (slice_val conf_sl) ∗
  "#Hconf_sl" ∷ readonly (own_slice_small conf_sl uint64T 1 x.(config))
.

End state.
End state.

Section config_proof.

Context `{!heapGS Σ}.
Context `{!configG Σ}.
Context `{config:list mp_server_names}.
Context `{Pwf:state.t → iProp Σ}.
Context {N:namespace}.

Definition is_Clerk (ck:loc) γ : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[config.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_uRPCClient cl srv ∗
  "#Hhost" ∷ is_config_host (N:=N) srv γ
.

Lemma wp_MakeClerk configHost γ:
  {{{
      is_config_host (N:=N) configHost γ
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

Definition own_Config_ghost γ (st:state.t) : iProp Σ :=
  "Hconf_ghost" ∷ own_config γ st.(state.config) ∗
  "Hreserved_ghost" ∷ own_reserved_epoch γ st.(state.reservedEpoch) ∗
  "Hepoch_lease" ∷ ((∃ γl, own_lease_expiration γl st.(state.leaseExpiration) ∗
                          post_lease (epochLeaseN (N:=N)) γl (own_latest_epoch γ st.(state.epoch)))
                   ) ∗
   "%HresIneq" ∷ ⌜ int.nat st.(state.epoch) <= int.nat st.(state.reservedEpoch) ⌝
.

(*
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
Qed. *)

Definition configWf (a:list u8) : iProp Σ :=
  ∃ st, ⌜ a = state.encode st ⌝ ∗ Pwf st
.

Instance c : mpaxosParams.t Σ :=
  mpaxosParams.mk Σ config configWf N
.

Definition is_config_inv γ γst : iProp Σ :=
  inv N (∃ st,
        "Hst" ∷ own_state γst (state.encode st) ∗
        "Hghost" ∷ own_Config_ghost γ st
      )
.

Definition own_Server (s:loc) γ : iProp Σ :=
  ∃ (p:loc) γp γsrv γst,
  "Hs" ∷ s ↦[config.Server :: "p"] #p ∗
  "#Hsrv" ∷ is_Server p γp γsrv ∗
  "#Hst_inv" ∷ is_state_inv γst γp ∗
  "#Hconfig_inv" ∷ is_config_inv γ γst
.

Definition configN := nroot .@ "config".

Definition is_Server (s:loc) γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[config.Server :: "mu"] mu) ∗
  "#His_mu" ∷ is_lock configN mu (own_Server s γ).

Definition own_tryRelease (f:val) γ (st_ptr:loc) (oldst:state.t) : iProp Σ :=
  ∀ (newst:state.t) Φ,
  (
    "Hvol" ∷ state.own st_ptr newst ∗
    "Hwf" ∷ □ Pwf newst ∗
    "Hupd" ∷ (own_Config_ghost γ oldst ={⊤∖↑N}=∗ own_Config_ghost γ newst ∗ Φ #true)
  ) -∗
  (Φ #false) -∗
  WP f #() {{ Φ }}
.

Lemma wp_Server__tryAcquire s γ :
  {{{
        is_Server s γ
  }}}
    config2.Server__tryAcquire #s
  {{{
        (ok:bool) (st_ptr:loc) (f:val), RET (#ok, #st_ptr, f);
        if ok then
          ∃ st,
          state.own st_ptr st ∗
          own_tryRelease f γ st_ptr st
        else
          True
  }}}
.
Proof.
Admitted.

Lemma wp_Server__ReserveEpochAndGetConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    config2.Server__ReserveEpochAndGetConfig #server
  {{{
        (f:val), RET f; is_urpc_handler_pred f (ReserveEpochAndGetConfig_spec (N:=N) γ)
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

  replace (slice.nil) with (slice_val Slice.nil) by done.
  wp_apply (wp_WriteInt with "[]").
  { iApply own_slice_zero. }
  iIntros (rep_sl) "Hrep_sl".
  wp_store.
  wp_apply (wp_Server__tryAcquire with "[$]").
  iIntros (???) "Hpost".
  wp_pure1_credit "Hlc".
  wp_if_destruct.
  { (* if not ok from tryAcquire *)
    iApply "HΦ".
    iDestruct (own_slice_to_small with "Hrep_sl") as "$".
    iFrame.
    Opaque u64_le.
    rewrite /ReserveEpochAndGetConfig_spec /ReserveEpochAndGetConfig_core_spec /=.
    iRight in "HΨ".
    iApply "HΨ".
    done.
  }
  iDestruct "Hpost" as (?) "[Hvol Hwp]".
  iNamed "Hvol".
  wp_loadField.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros "%HnoOverflow".
  wp_storeField.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_pures.
  iDestruct "HΨ" as "[HΨ1 Hfail]".
  wp_bind (f #()).
  wp_apply (wp_frame_wand with "[HΦ Hrep Hrep_sl]").
  { iNamedAccu. }
  wp_apply ("Hwp" with "[-Hfail] [Hfail]").
  {
    iSplitL "Hepoch HreservedEpoch HleaseExpiration HwantLeaseToExpire Hconf Hconf_sl".
    {
      instantiate (1:=state.mk _ _ _ _ _).
      repeat iExists _; simpl; iFrame "∗#".
    }
    iSplitR.
    { admit. } (* FIXME: spec*)
    iIntros "Hghost".

    (* start ghost reasoning *)
    iNamed "Hghost".
    rewrite /ReserveEpochAndGetConfig_core_spec.
    iMod ("HΨ1" with "[$]") as (??) "(Hres & Hconf & Hupd)".
    iCombine "Hconf Hconf_ghost" gives %[_ H]. subst.

    rewrite /own_reserved_epoch.
    iDestruct (mono_nat_auth_own_agree with "Hres [$]") as %[? H].
    apply Z2Nat.inj in H; try word.
    eapply (inj (R:=eq)) in H.
    2:{ apply _. }
    subst.
    iCombine "Hres Hreserved_ghost" as "Hres".
    (* FIXME: combine instance for mono_nat_auth_own *)
    iMod (mono_nat_own_update with "Hres") as "[[Hres1 Hres2] _]".
    { shelve. }
    iMod ("Hupd" with "[%] [$] [$]") as "HΨ".
    { word. }
    Unshelve.
    2:{ word. }
    iModIntro.
    iFrame.
    iSplitR.
    { iPureIntro. simpl. word. }
    (* end ghost reasoning *)

    iNamed 1.

    wp_pures.

    iClear "Hrep_sl".
    wp_apply (wp_slice_len).
    wp_apply (wp_NewSliceWithCap).
    { apply encoding.unsigned_64_nonneg. }
    iIntros (ptr) "Hsl".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "[$]").
    iIntros (enc_sl) "Hrep_sl".
    wp_store.
    wp_load.
    wp_apply (wp_WriteInt with "[$]").
    iIntros (?) "Hrep_sl".
    wp_store.
    wp_apply (Config.wp_Encode with "[Hconf_sl]").
    { iFrame "#". }
    iIntros (enc_conf enc_conf_sl) "(%Hconf_enc & _ & Henc_conf_sl)".
    wp_load.
    wp_apply (wp_WriteBytes with "[$Hrep_sl Henc_conf_sl]").
    {
      iDestruct (own_slice_to_small with "Henc_conf_sl") as "$".
    }
    iIntros (?) "[Hrep_sl Henc_conf_sl]".
    replace (int.nat 0%Z) with 0%nat by word.
    wp_store.
    iApply "HΦ".
    iFrame "Hrep".
    iDestruct (own_slice_to_small with "Hrep_sl") as "?".
    iFrame.
    iModIntro.
    simpl.
    iApply "HΨ".
    done.
  }
  {
    simpl.
    iNamed 1.
    wp_pures.
    iApply "HΦ".
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iFrame.
    iApply "Hfail".
    done.
  }
Admitted. (* TODO: bubble up Pwf predicate into RPC spec *)

End config_proof.
