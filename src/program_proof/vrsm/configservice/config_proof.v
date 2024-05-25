From Perennial.program_proof Require Import grove_prelude.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof Require Import marshal_stateless_proof std_proof.
From Perennial Require Import config_marshal_proof vrsm.renewable_lease.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From iris.base_logic Require Import lib.ghost_var mono_nat.
From Perennial Require Import paxos.start_proof paxos.weakread_proof paxos.tryacquire_proof paxos.init_proof.
From Goose.github_com.mit_pdos.gokv.vrsm Require Export configservice.
From Perennial.goose_lang Require Import crash_borrow crash_modality.

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

Definition encode (x:t) : list u8 :=
  u64_le x.(epoch) ++
  u64_le x.(reservedEpoch) ++
  u64_le x.(leaseExpiration) ++
  u64_le (if x.(wantLeaseToExpire) then W64 1 else W64 0) ++
  (u64_le (length x.(config)) ++ concat (u64_le <$> x.(config))).


Lemma list_u64_to_byte_inj a b :
  concat (u64_le <$> a) = concat (u64_le <$> b) → a = b.
Proof.
  generalize b; clear b. induction a; intros b.
  { simpl. intros. by destruct b; done. }
  rewrite fmap_cons concat_cons.
  intros. destruct b.
  { by exfalso. }
  rewrite fmap_cons concat_cons in H.
  apply app_inj_1 in H as [? H]; last done.
  f_equal.
  {
    apply (f_equal le_to_u64) in H0.
    by repeat rewrite u64_le_to_word in H0.
  }
  by apply IHa.
Qed.

Global Instance encode_inj : Inj eq eq encode.
Proof.
  intros ???. destruct x, y.
  Opaque u64_le.
  apply app_inj_1 in H as [? H]; last done.
  apply app_inj_1 in H as [? H]; last done.
  apply app_inj_1 in H as [? H]; last done.
  apply app_inj_1 in H as [? H]; last done.
  simpl in *.
  apply (f_equal le_to_u64) in H0, H1, H2.
  repeat rewrite u64_le_to_word in H0, H1, H2.
  subst. f_equal.
  { by destruct wantLeaseToExpire0, wantLeaseToExpire1. }
  apply app_inj_1 in H as [? H]; last done.
  by apply list_u64_to_byte_inj.
Qed.

Context `{!heapGS Σ}.
Definition own (l:loc) (x:t) : iProp Σ :=
  ∃ conf_sl,
  "Hepoch" ∷ l ↦[state :: "epoch"] #x.(epoch) ∗
  "HreservedEpoch" ∷ l ↦[state :: "reservedEpoch"] #x.(reservedEpoch) ∗
  "HleaseExpiration" ∷ l ↦[state :: "leaseExpiration"] #x.(leaseExpiration) ∗
  "HwantLeaseToExpire" ∷ l ↦[state :: "wantLeaseToExpire"] #x.(wantLeaseToExpire) ∗
  "Hconf" ∷ l ↦[state :: "config"] (slice_val conf_sl) ∗
  "#Hconf_sl" ∷ readonly (own_slice_small conf_sl uint64T (DfracOwn 1) x.(config))
.

Lemma wp_decode (x:t) sl q :
  {{{
        own_slice_small sl byteT q (encode x)
  }}}
    decodeState (slice_val sl)
  {{{
        l, RET #l; own l x
  }}}
.
Proof.
  iIntros (?) "Hsl HΦ".
  wp_lam.
  wp_apply (wp_allocStruct); first by val_ty.
  iIntros (?) "Hl". iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_ref_to); first by val_ty.
  iIntros (?) "He2".
  wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "?".
  wp_pures. wp_storeField. wp_store.
  wp_load. wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "?".
  wp_pures. wp_storeField. wp_store.
  wp_load. wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "?".
  wp_pures. wp_storeField. wp_store.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (?) "HwantExp".
  wp_pures.
  wp_load. wp_apply (wp_ReadInt with "[$]").
  iIntros (?) "Hsl".
  wp_pures.
  wp_store. wp_store.
  wp_load.
  wp_storeField.
  wp_load.
  wp_apply (Config.wp_Decode with "[$Hsl]").
  { done. }
  iIntros (?) "Hconf".
  wp_storeField.
  iApply "HΦ".
  repeat iExists _.
  iFrame "∗#".
  by destruct x, wantLeaseToExpire; iFrame.
Qed.

Lemma wp_encode l (x:t) :
  {{{
        own l x
  }}}
    encodeState #l
  {{{
        sl, RET (slice_val sl);  own_slice_small sl byteT (DfracOwn 1) (encode x) ∗
        own l x
  }}}
.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_lam.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (?) "Hl".
  wp_pures.
  wp_loadField.
  change (slice.nil) with (slice_val Slice.nil).
  wp_apply (wp_WriteInt with "[]").
  { iApply own_slice_zero. }
  iIntros (?) "?". wp_store.
  wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "?". wp_store.
  wp_loadField. wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "?". wp_store.
  wp_loadField.
  wp_if_destruct.
  {
    wp_load. wp_apply (wp_WriteInt with "[$]").
    iIntros (?) "Hsl". wp_store.
    wp_loadField.
    wp_apply (Config.wp_Encode with "[]").
    { iFrame "#". }
    iIntros (??) "(%Henc & _ & HconfEnc)".
    wp_load.
    iDestruct (own_slice_to_small with "HconfEnc") as "HconfEnc".
    wp_apply (wp_WriteBytes with "[$Hsl $HconfEnc]").
    iIntros (?) "[Hsl _]".
    wp_store.
    wp_load.
    iApply "HΦ".
    iModIntro.
    iSplitL "Hsl".
    {
      iApply own_slice_to_small. simpl. rewrite /encode Heqb -app_assoc. rewrite Henc.
      iFrame.
    }
    repeat iExists _; iFrame "∗#".
    rewrite Heqb. iFrame.
  }
  {
    wp_load. wp_apply (wp_WriteInt with "[$]").
    iIntros (?) "Hsl". wp_store.
    wp_loadField.
    wp_apply (Config.wp_Encode with "[]").
    { iFrame "#". }
    iIntros (??) "(%Henc & _ & HconfEnc)".
    wp_load.
    iDestruct (own_slice_to_small with "HconfEnc") as "HconfEnc".
    wp_apply (wp_WriteBytes with "[$Hsl $HconfEnc]").
    iIntros (?) "[Hsl _]".
    wp_store.
    wp_load.
    iApply "HΦ".
    iModIntro.
    iSplitL "Hsl".
    {
      iApply own_slice_to_small. simpl. rewrite /encode Heqb -app_assoc. rewrite Henc.
      iFrame.
    }
    repeat iExists _; iFrame "∗#".
    rewrite Heqb. iFrame.
  }
Qed.

End state.
End state.

Definition config_server_names := mp_server_names.

Record config_names :=
{
  epoch_gn:gname ;
  repoch_gn:gname ;
  config_val_gn:gname ;
  paxos_gn:paxos_system_names ;
}.

Module configParams.
Class t Σ :=
  mk {
      Pwf : list u64 → iProp Σ ;
      Ntop: namespace ;
      initconfig : list u64 ;
      HPwf_into_crash : ∀ (hG: heapGS Σ), IntoCrash (□ Pwf initconfig)%I (λ hG', □ Pwf initconfig)%I ;
    }
.
End configParams.
Import configParams.

Section config_global.

Class configG Σ := {
    config_configG :> ghost_varG Σ (list u64) ;
    config_urpcG :> urpcregG Σ ;
    config_epochG :> mono_natG Σ ;
    config_paxosG :> paxosG Σ ;
    config_leaseG :> renewable_leaseG Σ ;
}.

Definition configΣ := #[mono_natΣ ; paxosΣ ; ghost_varΣ (list u64) ; urpcregΣ ; renewable_leaseΣ ].

Global Instance subG_configΣ {Σ} : subG configΣ Σ → configG Σ.
Proof. intros. solve_inG. Qed.

Implicit Type γ : config_names.

Context `{!gooseGlobalGS Σ}.
Context `{!configG Σ}.
Context `{params:configParams.t Σ}.
(*
Context `{!Pwf.t Σ}.
Context `{ppeers:!peers.t}.
Context `{pconf:!init.t}.
Context `{pNtop:!Ntop.t}. *)

Definition own_latest_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(epoch_gn) (1/2) (uint.nat epoch).

Definition own_reserved_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(repoch_gn) (1/2) (uint.nat epoch).

Definition is_reserved_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(repoch_gn) (uint.nat epoch).

Definition own_config γ (conf:list u64) : iProp Σ :=
  ghost_var γ.(config_val_gn) (1/2) conf
.

Definition N := Ntop .@ "sub".
Definition epochLeaseN := N .@ "epochLeaseN".

Program Definition ReserveEpochAndGetConfig_core_spec γ Φ :=
  (
    £ 1 -∗
    (|={⊤∖↑N,∅}=> ∃ reservedEpoch conf, own_reserved_epoch γ reservedEpoch ∗ own_config γ conf ∗
    (⌜uint.nat reservedEpoch < uint.nat (word.add reservedEpoch (W64 1))⌝ -∗
      own_reserved_epoch γ (word.add reservedEpoch (W64 1)) -∗ own_config γ conf ={∅,⊤∖↑N}=∗
      Φ (word.add reservedEpoch 1) conf
      ))
    )%I.

Program Definition GetConfig_core_spec γ Φ :=
  (∀ conf, Pwf conf -∗ Φ conf)%I.

Program Definition TryWriteConfig_core_spec γ (epoch:u64) (new_conf:list u64) Φ : iProp Σ :=
  is_reserved_epoch_lb γ epoch ∗
  (□ Pwf new_conf) ∗
  (£ 1 -∗ |={⊤∖↑N,∅}=> ∃ latest_epoch reserved_epoch conf,
   own_latest_epoch γ latest_epoch ∗
   own_reserved_epoch γ reserved_epoch ∗
   own_config γ conf ∗
   (⌜ reserved_epoch = epoch ⌝ -∗
    own_config γ new_conf -∗
    own_reserved_epoch γ reserved_epoch -∗
    own_latest_epoch γ epoch ={∅,⊤∖↑N}=∗ Φ (W64 0))
  ) ∗
  (∀ (err:u64), ⌜err ≠ 0⌝ → Φ err)
.

Program Definition GetLease_core_spec γ (epoch:u64) Φ : iProp Σ :=
  (∀ (leaseExpiration:u64) γl,
    is_lease epochLeaseN γl (own_latest_epoch γ epoch) -∗
    is_lease_valid_lb γl leaseExpiration -∗ Φ (W64 0) leaseExpiration
  ) ∧
  (∀ (err:u64), ⌜err ≠ 0⌝ → Φ err (W64 0))
.

Program Definition ReserveEpochAndGetConfig_spec γ :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  ( (* no args *)
    ReserveEpochAndGetConfig_core_spec γ (λ newEpoch conf,
                                  ∀ enc_conf,
                                   ⌜Config.has_encoding enc_conf conf⌝ -∗
                                   Φ (u64_le 0 ++ u64_le newEpoch ++ enc_conf)
                                  ) ∗
    (∀ err, ⌜ err ≠ W64 0 ⌝ -∗ Φ (u64_le err))
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
  "#H0" ∷ is_urpc_spec_pred γrpc host (W64 0) (ReserveEpochAndGetConfig_spec γ) ∗
  "#H1" ∷ is_urpc_spec_pred γrpc host (W64 1) (GetConfig_spec γ) ∗
  "#H2" ∷ is_urpc_spec_pred γrpc host (W64 2) (TryWriteConfig_spec γ) ∗
  "#H3" ∷ is_urpc_spec_pred γrpc host (W64 3) (GetLease_spec γ) ∗
  "#Hdom" ∷ is_urpc_dom γrpc {[ (W64 0) ; (W64 1) ; (W64 2) ; (W64 3) ]}
.

Definition configN := N .@ "paxos".
Definition configPaxosN := configN .@ "paxos".
Definition configInvN := configN .@ "inv".

Definition own_Config_ghost γ (st:state.t) : iProp Σ :=
  ∃ γl,
  "Hconf_ghost" ∷ own_config γ st.(state.config) ∗
  "Hreserved_ghost" ∷ own_reserved_epoch γ st.(state.reservedEpoch) ∗
  "Hlatest_epoch" ∷ post_lease epochLeaseN γl (own_latest_epoch γ st.(state.epoch)) ∗
  "HleaseExp" ∷ own_lease_expiration γl st.(state.leaseExpiration) ∗
  "%HresIneq" ∷ ⌜ uint.nat st.(state.epoch) <= uint.nat st.(state.reservedEpoch) ⌝
.

Definition is_config_inv γ : iProp Σ :=
  inv configInvN (∃ st,
        "Hst" ∷ own_state γ.(paxos_gn) (state.encode st) ∗
        "Hghost" ∷ own_Config_ghost γ st
      )
.

Definition configWf (a:list u8) : iProp Σ :=
  ∃ st, ⌜ a = state.encode st ⌝ ∗ □ Pwf st.(state.config)
.

Definition initstate : list u8 :=
  state.encode (state.mk 0 0 0 false initconfig ).

Local Instance pParams : paxosParams.t Σ :=
  paxosParams.mk Σ initstate configWf configPaxosN.

Definition config_crash_resources γ (γsrv:config_server_names) d : iProp Σ :=
  own_file_inv γ.(paxos_gn) γsrv d
.

Definition is_config_invs γ : iProp Σ :=
  "#Hconfig_inv" ∷ is_config_inv γ
.

Definition is_config_server_host me paxosMe γ γsrv : iProp Σ :=
  "#Hinvs" ∷ is_config_invs γ ∗
  "#HhostConf" ∷ is_config_host me γ ∗
  "#HhostPaxos" ∷ is_paxos_server_host paxosMe γ.(paxos_gn) γsrv
.

(* XXX: maybe use is_config_server_host? *)
Definition is_config_peers (paxosHosts: list u64) γ : iProp Σ :=
  is_paxos_hosts paxosHosts γ.(paxos_gn).

Definition is_config_hosts (hosts: list u64) γ : iProp Σ :=
  "#Hhosts" ∷ ([∗ list] host ∈ hosts, is_config_host host γ) ∗
  "%Hnonempty" ∷ ⌜ 0 < length hosts ⌝
.

End config_global.

Section config_proof.

Context `{!heapGS Σ}.
Context `{!configG Σ}.
Context `{params:configParams.t Σ}.

Existing Instance pParams.
Definition is_Server (s:loc) γ : iProp Σ :=
  ∃ (p:loc) γsrv,
  "#Hs" ∷ readonly (s ↦[Server :: "s"] #p) ∗
  "#Hsrv" ∷ is_Server p γ.(paxos_gn) γsrv ∗
  "#Hconfig_inv" ∷ is_config_inv γ
.

Definition own_tryRelease (f:val) γ (st_ptr:loc) (oldst:state.t) : iProp Σ :=
  ∀ (newst:state.t) Φ,
  (
    "Hvol" ∷ state.own st_ptr newst ∗
    "#Hwf" ∷ □ Pwf newst.(state.config) ∗
    "Hupd" ∷ (own_Config_ghost γ oldst ={⊤∖↑configN}=∗ own_Config_ghost γ newst ∗ Φ #true)
  ) -∗
  (Φ #false) -∗
  WP f #() {{ Φ }}
.

Lemma wp_Server__tryAcquire s γ :
  {{{
        is_Server s γ
  }}}
    Server__tryAcquire #s
  {{{
        (ok:bool) (st_ptr:loc) (f:val), RET (#ok, #st_ptr, f);
        if ok then
          ∃ st,
          □ Pwf st.(state.config) ∗
          state.own st_ptr st ∗
          own_tryRelease f γ st_ptr st
        else
          True
  }}}
.
Proof.
  iIntros (Φ) "Hsrv HΦ".
  wp_lam.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (wp_Server__TryAcquire with "[$]").
  iIntros "* Hpost".
  wp_pures.
  wp_if_destruct.
  {
    iClear "Hpost".
    wp_apply wp_ref_of_zero.
    { done. }
    iIntros (?) "Hl".
    wp_pures. wp_load.
    wp_pures.
    iApply "HΦ".
    done.
  }
  setoid_rewrite decide_True.
  2:{ done. }
  iDestruct "Hpost" as (??) "(Hsl_ptr & #Hsl & HP & Hwp)".
  wp_load.
  iMod (readonly_load with "Hsl") as (?) "Hsl2".
  iDestruct "HP" as (?) "[%Henc #HP]".
  subst.
  wp_apply (state.wp_decode with "[$Hsl2]").
  iIntros (?) "Hst".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iExists _; iFrame "∗#".
  clear.
  iIntros (??). iNamed 1.
  iIntros "HΦ".
  wp_pures.
  wp_apply (state.wp_encode with "[$]").
  iClear "Hsl".
  iIntros (?) "[Hsl _]".
  wp_pure1_credit "Hlc".
  wp_store.
  iMod (readonly_alloc_1 with "Hsl") as "Hsl".
  wp_apply ("Hwp" with "[-HΦ]").
  {
    iFrame "∗#".
    iSplitR; first done.
    iInv "Hconfig_inv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
    iNamed "Hi".
    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iExists _; iFrame.
    iIntros "%Heq".
    eapply inj in Heq.
    2:{ apply _. }
    subst.
    iIntros "Hst".
    iMod "Hmask" as "_".
    iMod (fupd_mask_subseteq _) as "Hmask".
    2: iMod ("Hupd" with "[$]") as "[Hghost Hupd]".
    { simpl. solve_ndisj. }
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hghost Hst]").
    { repeat iExists _; iFrame. }
    iModIntro.
    wp_pures.
    iApply "Hupd".
  }
  {
    iIntros.
    wp_pures.
    rewrite bool_decide_false.
    { iApply "HΦ". }
    naive_solver.
  }
Qed.

Lemma wp_Server__ReserveEpochAndGetConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    Server__ReserveEpochAndGetConfig #server
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
  iDestruct "Hpost" as (?) "(#HP & Hvol & Hwp)".
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
    { simpl.  iFrame "#". }
    iIntros "Hghost".

    (* start ghost reasoning *)
    iNamed "Hghost".
    rewrite /ReserveEpochAndGetConfig_core_spec.
    iMod (fupd_mask_subseteq _) as "Hmask".
    2: iMod ("HΨ1" with "[$]") as (??) "(Hres & Hconf & Hupd)".
    { solve_ndisj. }
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
    iMod "Hmask".
    iModIntro.
    rewrite sep_exist_r. iExists _.
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
    replace (uint.nat 0%Z) with 0%nat by word.
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
Qed.

Lemma wp_Server__GetConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    Server__GetConfig #server
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
  wp_apply (wp_Server__WeakRead with "[$]").
  iIntros (??) "[#Hsl HP]".
  cbn.
  iDestruct "HP" as (?) "[%H HP]".
  subst.
  iMod (readonly_load with "Hsl") as (?) "Hsl2".
  wp_apply (state.wp_decode with "[$]").
  iIntros (?) "Hvol".
  wp_pures.
  iNamed "Hvol".
  wp_loadField.
  wp_apply (Config.wp_Encode with "[$]").
  iIntros (??) "(%Henc & _ & Henc)".
  wp_store.
  iDestruct (own_slice_to_small with "Henc") as "Henc".
  iApply "HΦ".
  iFrame.
  iApply ("HΨ" with "HP [//]").
Qed.

Lemma wp_Server__TryWriteConfig (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    Server__TryWriteConfig #server
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
  change (slice.nil) with (slice_val Slice.nil).
  wp_apply (wp_WriteInt with "[]").
  { iApply own_slice_zero. }
  iIntros (?) "Hrep_sl".
  wp_store.
  wp_apply (wp_ReadInt with "Harg_sl").
  iIntros (args_sl) "Hargs_sl".
  wp_pure1_credit "Hlc".
  wp_pures.
  wp_apply (Config.wp_Decode with "[$Hargs_sl]").
  { done. }
  iIntros (?) "Hconf_own".
  wp_pures.
  wp_forBreak.
  wp_pures.

  wp_apply (wp_Server__tryAcquire with "[$]").
  iIntros (???) "Hpost".
  wp_pures.
  iDestruct "HΨ" as "(#Hepoch_lb & #HP_new & HΨ)".
  wp_if_destruct.
  {
    iModIntro.
    iRight. iSplitR; first done.
    wp_pures.
    iApply "HΦ".
    iFrame.
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iFrame.
    simpl.
    iRight in "HΨ".
    iApply "HΨ".
    2:{ done. }
    { done. }
  }
  iDestruct "Hpost" as (?) "(#HP & Hvol & Hwp)".
  iNamed "Hvol".
  wp_loadField.
  wp_if_destruct.
  { (* case: higher epoch is reserved *)
    wp_bind (f #()).
    wp_apply (wp_frame_wand with "[HΨ HΦ Hrep_sl Hrep]").
    { iNamedAccu. }
    wp_apply ("Hwp" with "[-]").
    { (* case: committed update, which was actually not even an update. *)
      iSplitL "Hepoch HreservedEpoch HleaseExpiration HwantLeaseToExpire Hconf".
      { repeat iExists _; iFrame "∗#". }
      iFrame "#".
      iIntros "$ !#".
      iNamed 1.
      wp_pures.
      wp_apply (wp_WriteInt with "[]").
      { iApply own_slice_zero. }
      iIntros (rep_sl) "Hrep_sl2".
      wp_store.
      iModIntro.
      iRight. iSplitR; first done.
      wp_pures.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl2") as "Hrep_sl2".
      iFrame. simpl.
      iRight in "HΨ".
      iApply "HΨ"; last done; done.
    }
    { (* case: (non-)update failed to be committed *)
      iNamed 1.
      wp_pures.
      iModIntro.
      iRight. iSplitR; first done.
      wp_pures.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame. simpl.
      iRight in "HΨ".
      iApply "HΨ"; last done; done.
    }
  }
  wp_loadField.
  wp_if_destruct.
  { (* case: try to enter new epoch *)
    wp_apply wp_GetTimeRange.
    iIntros "* % % Htime".
    iDestruct (own_time_get_lb with "Htime") as "#Hlb".
    iModIntro.
    iFrame "Htime".
    wp_pures.
    wp_loadField.
    wp_if_destruct.
    { (* case: lease is expired, so can activate new epoch right now *)
      wp_storeField.
      wp_storeField.
      wp_storeField.
      iClear "Hconf_sl".
      rewrite /Config.own.
      iNamed "Hconf_own".
      iDestruct "Hargs_state_sl" as "#Hconf_sl".
      iDestruct "HΨ" as "[HΨ Hfail]".
      wp_bind (f #()).
      wp_apply (wp_frame_wand with "[HΦ Hrep Hrep_sl]"); first iNamedAccu.
      wp_apply ("Hwp" with "[-Hfail]").
      { (* case: committed update. *)
        iSplitL "Hepoch HreservedEpoch HleaseExpiration HwantLeaseToExpire Hconf".
        {
          instantiate (1:=state.mk _ _ _ _ _).
          repeat iExists _; simpl; iFrame "∗#".
        }
        simpl.
        iFrame "#".

        (* start ghost reasoning *)
        iIntros "Hghost".
        iNamed "Hghost".
        iMod (fupd_mask_subseteq _) as "Hmask".
        2: iMod (lease_expire with "[$] [$] []") as ">Hepoch_ghost".
        { solve_ndisj. }
        { iApply (is_time_lb_mono with "[$]"). word. }
        iMod "Hmask" as "_".
        iMod (fupd_mask_subseteq _) as "Hmask".
        2: iMod ("HΨ" with "Hlc") as "HΨ".
        { solve_ndisj. }
        iDestruct "HΨ" as (???) "(Hepoch_ghost2 & Hres2 & Hconf_ghost2 & Hupd)".
        iDestruct (mono_nat_auth_own_agree with "Hreserved_ghost Hres2") as %[_ ?].
        assert (reserved_epoch = st.(state.reservedEpoch)) by word; subst.
        iDestruct (mono_nat_auth_own_agree with "Hepoch_ghost Hepoch_ghost2") as %[_ Heq].
        assert (latest_epoch = st.(state.epoch)) by word; subst.
        iCombine "Hepoch_ghost Hepoch_ghost2" as "Hepoch_ghost".
        iMod (mono_nat_own_update (uint.nat new_epoch) with "Hepoch_ghost") as "[[Hepoch_ghost Hepoch_ghost2] _]".
        { word. }
        iDestruct (ghost_var_agree with "Hconf_ghost Hconf_ghost2") as %->.
        iCombine "Hconf_ghost Hconf_ghost2" as "Hconf_ghost".
        iMod (ghost_var_update new_conf with "Hconf_ghost") as "[Hconf_ghost Hconf_ghost2]".
        iDestruct (mono_nat_lb_own_valid with "Hreserved_ghost Hepoch_lb") as %[_ Hineq].
        iMod ("Hupd" with "[] Hconf_ghost2 Hres2 Hepoch_ghost2") as "HΨ".
        { iPureIntro. word. }
        iMod "Hmask" as "_".
        clear γl.
        iMod (fupd_mask_subseteq _) as "Hmask".
        2: iMod (lease_alloc _ epochLeaseN with "Hepoch_ghost") as (?) "(_ & Hlatest_epoch & HleaseExp)".
        { solve_ndisj. }
        iMod "Hmask" as "_".
        iModIntro.
        repeat rewrite sep_exist_r.
        repeat iExists _.
        iFrame.
        iSplitR.
        { iPureIntro. simpl. word. }
        (* end ghost reasoning *)

        iNamed 1.
        wp_pures.
        wp_apply (wp_WriteInt with "[]").
        { iApply own_slice_zero. }
        iClear "Hrep_sl".
        iIntros (?) "Hrep_sl".
        wp_store. iModIntro.
        iRight. iSplitR; first done.
        wp_pures.
        iApply "HΦ".
        iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
        iFrame. iApply "HΨ". done.
      }
      { (* case: unable to commit update *)
        iNamed 1.
        wp_pures.
        iRight. iModIntro.
        iSplitR; first done.
        wp_pures.
        iApply "HΦ".
        iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
        iFrame.
        iApply "Hfail"; last done; done.
      }
    }
    { (* case: lease is not expired, so mark that we want to expire it and sleep *)
      wp_storeField.
      wp_loadField.
      wp_pures.
      iDestruct "HΨ" as "[HΨ Hfail]".
      wp_apply (wp_frame_wand with "[HΦ Hrep Hrep_sl Hfail]"); first iNamedAccu.
      wp_apply ("Hwp" with "[-]").
      { (* rsm update successful *)
        repeat rewrite sep_exist_r.
        instantiate (1:=state.mk _ _ _ _ _).
        iExists _; simpl; iFrame "∗#".
        iIntros "$ !#".
        wp_pures.
        wp_apply wp_Sleep.
        wp_pures.
        iModIntro.
        iNamed 1.
        iLeft.
        iSplitR; first done.
        iFrame.
      }
      { (* unable to update rsm *)
        wp_pures.
        iModIntro.
        iNamed 1.
        iRight. iSplitR; first done.
        wp_pures.
        iApply "HΦ".
        iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
        iFrame.
        iApply "Hfail"; last done; done.
      }
    }
  }
  { (* case: already entered the new epoch *)
    wp_storeField.
    iDestruct "HΨ" as "[HΨ Hfail]".
    wp_bind (f #()).
    wp_apply (wp_frame_wand with "[HΦ Hfail Hrep Hrep_sl]"); first iNamedAccu.
    wp_apply ("Hwp" with "[-]").
    { (* case: successful paxos write *)
      repeat rewrite sep_exist_r.
      instantiate (1:=state.mk _ _ _ _ _).
      iExists _; simpl; iFrame "∗#".
      iIntros "Hghost".
      iNamed "Hghost".
      iMod (post_lease_acc with "Hlatest_epoch") as "[>Hlatest_epoch Hclose]".
      { solve_ndisj. }
      iMod (fupd_mask_subseteq _) as "Hmask".
      2: iMod ("HΨ" with "[$]") as "HΨ".
      { solve_ndisj. }
      iDestruct "HΨ" as (???) "(Hepoch_ghost2 & Hres2 & Hconf_ghost2 & HΨ)".
      iDestruct (mono_nat_auth_own_agree with "Hreserved_ghost Hres2") as %[_ ?].
      assert (reserved_epoch = st.(state.reservedEpoch)) by word; subst.
      iDestruct (mono_nat_auth_own_agree with "Hlatest_epoch Hepoch_ghost2") as %[_ ?].
      assert (latest_epoch = st.(state.epoch)) by word; subst.
      iDestruct (ghost_var_agree with "Hconf_ghost Hconf_ghost2") as %->.
      iCombine "Hconf_ghost Hconf_ghost2" as "Hconf_ghost".
      iMod (ghost_var_update new_conf with "Hconf_ghost") as "[Hconf_ghost Hconf_ghost2]".
      replace (new_epoch) with (st.(state.epoch)) by word.
      iMod ("HΨ" with "[] Hconf_ghost2 Hres2 Hepoch_ghost2") as "HΨ".
      { iPureIntro. word. }
      iMod "Hmask".
      iMod ("Hclose" with "[$]") as "Hlatest_epoch".
      iModIntro.
      repeat rewrite sep_exist_r.
      iExists _; simpl; iFrame "∗#".
      iSplitR.
      { iPureIntro. word. }
      iNamed 1.
      wp_pures.
      iClear "Hrep_sl".
      wp_apply (wp_WriteInt with "[]").
      { iApply own_slice_zero. }
      iIntros (?) "Hrep_sl".
      wp_store.
      iModIntro. iRight.
      iSplitR; first done.
      wp_pures.
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply "HΦ".
      iFrame.
      iApply "HΨ". done.
    }
    { (* case: paxos write failed *)
      iNamed 1.
      wp_pures.
      iModIntro. iRight.
      iSplitR; first done.
      wp_pures.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
      iApply "Hfail"; last done; done.
    }
  }
Qed.

Lemma wp_Server__GetLease (server:loc) γ :
  {{{
        is_Server server γ
  }}}
    Server__GetLease #server
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
  iDestruct "HΨ" as (?) "[% HΨ]".
  subst.
  change (slice.nil) with (slice_val Slice.nil).
  wp_apply (wp_WriteInt with "[]").
  { iApply own_slice_zero. }
  iIntros (?) "Hrep_sl".
  wp_store.
  wp_load.
  wp_apply (wp_WriteInt with "[$Hrep_sl]").
  iIntros (?) "Hrep_sl".
  wp_store.
  wp_apply (wp_ReadInt with "Harg_sl").
  iIntros (?) "Hargs_sl".
  wp_pures.
  wp_apply (wp_Server__tryAcquire with "[$]").
  iIntros "* Hpost".
  wp_pures.
  wp_if_destruct.
  { (* case: not leader *)
    iApply "HΦ".
    iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
    iFrame.
    iRight in "HΨ".
    iApply "HΨ"; last done.
    done.
  }
  iDestruct "Hpost" as (?) "(#HP & Hvol & Hwp)".
  iNamed "Hvol".
  wp_loadField.
  wp_apply (wp_or with "[HwantLeaseToExpire]").
  { iNamedAccu. }
  { wp_pures. iPureIntro. by rewrite -bool_decide_not. }
  { iIntros. wp_loadField. iFrame. iPureIntro.
    repeat f_equal.
    instantiate (2:=(st.(state.wantLeaseToExpire) = true)).
    Unshelve. 2:{ apply _. }
    by destruct st, wantLeaseToExpire.
  }
  iNamed 1.
  wp_if_destruct.
  { (* case: epoch number that the caller wants is not the latest epoch, or wantToExpireLease *)
    wp_bind (f #()).
    wp_apply (wp_frame_wand with "[HΨ HΦ Hrep_sl Hrep]"); first iNamedAccu.
    wp_apply ("Hwp" with "[-]").
    { (* case: committed (non-)update *)
      repeat rewrite sep_exist_r.
      repeat iExists _. iFrame "∗#".
      iIntros "$ !#".
      wp_pures.
      iNamed 1.
      wp_apply (wp_WriteInt with "[]").
      { iApply own_slice_zero. }
      iClear "Hrep_sl".
      iIntros (?) "Hrep_sl".
      wp_store.
      wp_load.
      wp_apply (wp_WriteInt with "[$Hrep_sl]").
      iIntros (?) "Hrep_sl".
      wp_store.
      iModIntro.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
      iRight in "HΨ".
      iApply "HΨ"; last done; done.
    }
    {
      iNamed 1.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
      iRight in "HΨ".
      iApply "HΨ"; last done; done.
    }
  }
  { (* case: epoch matches *)

    assert (epoch = st.(state.epoch)); last subst.
    {
      apply Decidable.not_or in Heqb.
      destruct Heqb as [? ?].
      apply dec_stable in H.
      by injection H.
    }
    wp_apply wp_GetTimeRange.
    iIntros "* % % $".
    iModIntro.
    wp_pures.
    wp_loadField.
    wp_pures.
    wp_bind (if: #_ then _ else _)%E.
    wp_apply (wp_wand with "[HleaseExpiration]").
    {
      instantiate (1:=(λ _, ∃ (newLeaseExpiration:u64),
                        "%Hineq1" ∷ ⌜ uint.nat st.(state.leaseExpiration) <= uint.nat newLeaseExpiration⌝ ∗
                        "%Hineq2" ∷ ⌜ uint.nat (word.add l 1000000000%Z) <=
                          uint.nat newLeaseExpiration⌝ ∗
                        "HleaseExpiration" ∷ st_ptr ↦[state :: "leaseExpiration"] #newLeaseExpiration )%I).
      wp_if_destruct.
      {
        wp_storeField.
        iExists _; iFrame. iPureIntro.
        split.
        { apply Z2Nat.inj_le; try apply encoding.unsigned_64_nonneg. lia. }
        { apply Z2Nat.inj_le; try apply encoding.unsigned_64_nonneg. lia. }
      }
      { iExists _; iFrame. iPureIntro.
        split; first done.
        apply Z2Nat.inj_le; try apply encoding.unsigned_64_nonneg. lia.
      }
    }
    iIntros (?).
    iNamed 1.
    wp_pures.
    wp_bind (f #()).
    wp_apply (wp_frame_wand with "[HΨ HΦ Hrep Hrep_sl]"); first iNamedAccu.
    wp_apply ("Hwp" with "[-]").
    { (* successfully commit paxos write *)
      repeat rewrite sep_exist_r.
      instantiate (1:=state.mk _ _ _ _ _).
      Opaque u64_le.
      iExists _; simpl.
      iFrame "∗#".
      Transparent u64_le.

      (* start ghost reasoning *)
      iNamed 1.
      iMod (fupd_mask_subseteq _) as "Hmask".
      2: iMod (lease_renew newLeaseExpiration with "[$] [$]") as "[Hlatest_epoch HleaseExp]".
      { solve_ndisj. }
      { word. }
      iMod "Hmask" as "_".
      iDestruct (post_get_lease with "[$]") as "#Hlease".
      iDestruct (lease_get_lb with "[$]") as "#Hlb".
      iDestruct (lease_lb_mono with "[$]") as "#Hlb2".
      { exact Hineq2. }
      iClear "Hlb".
      repeat rewrite sep_exist_r.
      iExists _. iFrame.
      iSplitR.
      { iPureIntro. simpl. done. }
      iModIntro.
      (* end ghost reasoning *)

      iNamed 1.
      iLeft in "HΨ".
      iDestruct ("HΨ" with "[$] [$]") as "HΨ".
      wp_pures.
      wp_apply (wp_WriteInt with "[]").
      { iApply own_slice_zero. }
      iClear "Hrep_sl".
      iIntros (?) "Hrep_sl".
      wp_store.
      wp_load.
      wp_apply (wp_WriteInt with "[$Hrep_sl]").
      iIntros (?) "Hrep_sl".
      wp_store.
      iModIntro.
      iApply "HΦ".
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
      iApply "HΨ".
      iPureIntro. done.
    }
    { (* case: paxos write failed *)
      iNamed 1.
      wp_pures.
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply "HΦ".
      iFrame.
      iRight in "HΨ".
      iApply "HΨ"; last done; done.
    }
  }
Qed.

Definition own_Clerk_inv (ck:loc) l : iProp Σ :=
  ∃ (leader:u64),
  "Hleader" ∷ ck ↦[Clerk :: "leader"] #leader ∗
  "%HleaderBound" ∷ ⌜ uint.nat leader < l ⌝
.

Definition is_Clerk (ck:loc) γ : iProp Σ :=
  ∃ mu cls_sl (cls:list loc),
  "#Hmu" ∷ readonly (ck ↦[Clerk :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock N mu (own_Clerk_inv ck (length cls)) ∗
  "#Hcls" ∷ readonly (ck ↦[Clerk :: "cls"] (slice_val cls_sl)) ∗
  "#Hcls_sl" ∷ readonly (own_slice_small cls_sl ptrT (DfracOwn 1) cls) ∗
  "#Hrpc" ∷ ([∗ list] cl ∈ cls, ∃ srv, is_ReconnectingClient cl srv ∗ is_config_host srv γ) ∗
  "%HszNonzero" ∷ ⌜ length cls > 0 ⌝
.

Lemma wp_MakeClerk hosts hosts_sl γ:
  {{{
      "Hhosts_sl" ∷ readonly (own_slice_small hosts_sl uint64T (DfracOwn 1) hosts) ∗
      "#Hhosts" ∷ is_config_hosts hosts γ
  }}}
    MakeClerk (slice_val hosts_sl)
  {{{
      ck, RET #ck; is_Clerk ck γ
  }}}
.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H". iNamed "Hhosts".
  wp_lam.
  wp_apply wp_NewSlice.
  iIntros (?) "Hcls_sl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (cls_ptr) "Hcls".
  wp_pures.
  iMod (readonly_load with "Hhosts_sl") as (?) "Hhosts_sl".
  iDestruct (own_slice_small_sz with "Hhosts_sl") as %Hsz.
  wp_apply (wp_forSlice'
              (λ i,
               ∃ sl cls,
               "Hcls" ∷ cls_ptr ↦[slice.T ptrT] (slice_val sl) ∗
               "Hcls_sl" ∷ own_slice sl ptrT (DfracOwn 1) (cls) ∗
               "#Hrpc" ∷ ([∗ list] cl ∈ cls, ∃ srv : u64, is_ReconnectingClient cl srv ∗ is_config_host srv γ) ∗
               "%Hsz" ∷ ⌜ length cls = uint.nat i ⌝
               )%I
             with "[] [Hcls Hcls_sl $Hhosts_sl]").
  2:{
    iSplitL "Hhosts".
    { iExact "Hhosts". }
    repeat iExists _.
    iFrame.
    iSplitR; last done.
    by iApply big_sepL_nil.
  }
  {
    clear Φ.
    iIntros (???) "!# Hpre HΦ".
    wp_pures.
    iDestruct "Hpre" as "(%Hineq & %Hlookup & #Hhost & Hpre)".
    iNamed "Hpre".
    wp_apply wp_MakeReconnectingClient.
    iIntros (?) "#Hcl".
    wp_load.
    wp_bind (SliceAppend _ _ _).
    change (#cl_ptr) with (loc_IntoVal.(to_val) cl_ptr).
    wp_apply (wp_SliceAppend with "[$Hcls_sl]").
    iIntros (?) "Hcls_sl".
    wp_store.
    iApply "HΦ".
    iModIntro. repeat iExists _; iFrame.
    iSplitL.
    2:{ iPureIntro. rewrite app_length. simpl. word. }
    iApply (big_sepL_app with "[]").
    iFrame "Hrpc".
    iApply big_sepL_singleton.
    iExists _; iFrame "#".
  }
  iNamed 1.
  wp_pures.
  wp_apply wp_new_free_lock.
  iIntros (?) "HmuInv".
  wp_load.
  iApply wp_fupd.
  wp_apply wp_allocStruct.
  { eauto 20. }
  iIntros (?) "Hc".
  iDestruct (struct_fields_split with "Hc") as "HH".
  iNamed "HH".
  iApply "HΦ".
  repeat iExists _.
  iMod (readonly_alloc_1 with "mu") as "$".
  iMod (readonly_alloc_1 with "cls") as "$".
  iDestruct (own_slice_to_small with "Hcls_sl") as "Hcls_sl".
  iMod (readonly_alloc_1 with "Hcls_sl") as "$".
  iFrame "Hrpc".
  rewrite Hsz0.
  iMod (alloc_lock with "HmuInv [leader]") as "$".
  { iNext. repeat iExists _; iFrame. iPureIntro. word. }
  iPureIntro. word.
Qed.

Lemma wp_Clerk__ReserveEpochAndGetConfig (ck:loc) γ Φ :
  is_Clerk ck γ -∗
  □ (£ 1 -∗
      (|={⊤∖↑N,∅}=> ∃ epoch conf, own_reserved_epoch γ epoch ∗ own_config γ conf ∗
       (⌜uint.nat epoch < uint.nat (word.add epoch (W64 1))⌝ -∗
        own_reserved_epoch γ (word.add epoch (W64 1)) -∗ own_config γ conf ={∅,⊤∖↑N}=∗
         (∀ conf_sl, readonly (own_slice_small conf_sl uint64T (DfracOwn 1) conf) -∗
           Φ (#(LitInt $ word.add epoch (W64 1)), slice_val conf_sl)%V)))
  ) -∗
  WP Clerk__ReserveEpochAndGetConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  wp_lam.
  wp_apply wp_ref_of_zero.
  { eauto. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  iAssert ( ∃ sl,
      "Hreply" ∷ reply_ptr ↦[slice.T byteT] (slice_val sl)
    )%I with "[-]" as "HH".
  { rewrite zero_slice_val. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.

  iNamed "Hck".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hleader]").
  { iFrame "∗#". iNext. iExists _; iFrame "∗%". }
  wp_pures.
  wp_apply wp_NewSlice.
  iIntros (?) "Hargs_sl".
  iDestruct (own_slice_to_small with "Hargs_sl") as "Hargs_sl".
  wp_loadField.
  apply list_lookup_lt in HleaderBound as [? Hlookup].
  iMod (readonly_load with "Hcls_sl") as (?) "Hcls_sl2".
  iDestruct (own_slice_small_sz with "Hcls_sl2") as %Hsl_sz.
  wp_apply (wp_SliceGet with "[$Hcls_sl2]").
  { done. }
  iIntros "_".
  iDestruct (big_sepL_lookup with "Hrpc") as (?) "#[Hcl_rpc Hhost]".
  { exact Hlookup. }
  iNamed "Hhost".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  { iFrame "#". }
  { (* successful RPC *)
    iModIntro.
    iNext.
    Opaque u64_le.
    rewrite /ReserveEpochAndGetConfig_spec /ReserveEpochAndGetConfig_core_spec /=.
    Transparent u64_le.
    iSplitR.
    { (* case: successfully reserved epoch *)
      iIntros "Hlc".
      iDestruct ("HΦ" with "Hlc") as "Hupd".
      (* case: got a new epoch, no error *)
      iMod "Hupd".
      iModIntro.
      iDestruct "Hupd" as (??) "(Ha&Hb&Hupd)".
      iExists _, _.
      iFrame "Ha Hb".
      iIntros.
      iMod ("Hupd" with "[% //] [$] [$]") as "Hupd".
      iModIntro.
      iIntros (?) "%Hconf_enc Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_apply (wp_ref_of_zero).
      { done. }
      iIntros (?) "Herr".
      wp_pures.
      wp_load.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_pures.
      wp_load.
      wp_pures.
      iRight. iModIntro.
      iSplitR; first done.
      wp_pures.
      wp_apply (wp_ref_of_zero).
      { done. }
      iIntros (epoch_ptr) "Hepoch".
      wp_pures.
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
      wp_pures.
      iModIntro.
      iApply "Hupd".
      iFrame.
    }
    { (* case: RPC ran, but was not able to reserve an epoch *)
      iIntros (?) "%Herr _".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_apply wp_ref_of_zero.
      { done. }
      iIntros (?) "Herr".
      wp_pures.
      wp_load.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_if_destruct.
      { (* case: ErrNotLeader, so retry *)
        wp_loadField.
        wp_apply (acquire_spec with "[$]").
        iIntros "[Hlocked Hown]".
        wp_pures.
        iNamed "Hown".
        wp_loadField.
        wp_if_destruct.
        { (* case: increase leader idx *)
          wp_loadField.
          wp_loadField.
          wp_apply (wp_slice_len).
          wp_pures.
          wp_storeField.
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "∗#".
            iNext. repeat iExists _; iFrame.
            iPureIntro.
            rewrite Hsl_sz.
            rewrite word.unsigned_modu_nowrap; last lia.
            { apply Z2Nat.inj_lt; auto using encoding.unsigned_64_nonneg.
              { apply Z.mod_pos; lia. }
              { apply Z_mod_lt; lia. }
            }
          }
          wp_pures.
          iLeft.
          iModIntro. iSplitR; first done.
          repeat iExists _.
          iFrame.
        }
        { (* case: don't increase leader idx *)
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "∗#".
            iNext. repeat iExists _; iFrame "∗%".
          }
          wp_pures.
          iLeft.
          iModIntro. iSplitR; first done.
          repeat iExists _.
          iFrame.
        }
      }
      { (* case: some other error, still retry *)
        wp_load.
        wp_pures.
        wp_if_destruct.
        { exfalso. done. }
        iModIntro.
        iLeft. iSplitR; first done.
        iExists _; iFrame.
      }
    }
  }
  {
    iIntros (?) "%Herr Hreply_sl Hrep".
    wp_pures.
    wp_if_destruct.
    2:{ exfalso. done. }
    iModIntro. iLeft.
    iSplitR; first done.
    iExists _. iFrame.
  }
Qed.

Lemma wp_Clerk__GetConfig (ck:loc) γ Φ :
  is_Clerk ck γ -∗
  □ (∀ conf conf_sl, Pwf conf -∗ readonly (own_slice_small conf_sl uint64T (DfracOwn 1) conf)
                                 -∗ Φ (slice_val conf_sl)%V) -∗
  WP Clerk__GetConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  wp_lam.
  wp_apply wp_ref_of_zero.
  { eauto. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  iAssert ( ∃ sl,
      "Hreply" ∷ reply_ptr ↦[slice.T byteT] (slice_val sl)
    )%I with "[-]" as "HH".
  { rewrite zero_slice_val. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  iNamed "Hck".
  wp_apply (wp_RandomUint64).
  iIntros (?) "_".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  wp_apply wp_NewSlice.
  iIntros (?) "Hargs_sl".
  iDestruct (own_slice_to_small with "Hargs_sl") as "Hargs_sl".
  wp_loadField.

  iMod (readonly_load with "Hcls_sl") as (?) "Hcls_sl2".
  iDestruct (own_slice_small_sz with "Hcls_sl2") as %Hsl_sz.
  set (idx:=(word.modu r cls_sl.(Slice.sz))).
  assert (uint.nat idx < length cls) as Hlookup.
  {
    subst idx.
    rewrite Hsl_sz.
    rewrite word.unsigned_modu_nowrap; last lia.
    { apply Z2Nat.inj_lt; auto using encoding.unsigned_64_nonneg.
      { apply Z.mod_pos; lia. }
      { apply Z_mod_lt; lia. }
    }
  }
  apply list_lookup_lt in Hlookup as [? Hlookup].
  wp_apply (wp_SliceGet with "[$Hcls_sl2]").
  { done. }
  iIntros "_".
  iDestruct (big_sepL_lookup with "Hrpc") as (?) "#[Hcl_rpc Hhost]".
  { exact Hlookup. }
  iNamed "Hhost".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  { iFrame "#". }
  { (* successful RPC *)
    iModIntro.
    iNext.
    iIntros (?) "HP".
    iIntros (?) "%Henc _".
    iIntros (?) "Hrep Hreply_sl".
    wp_pures.
    iRight.
    iModIntro. iSplitR; first done.
    wp_pures.
    wp_load.
    wp_apply (Config.wp_Decode with "[$Hreply_sl //]").
    iIntros (?) "Hconf".
    wp_pures.
    iApply ("HΦ" with "[$]").
    iFrame.
    done.
  }
  {
    iIntros (?) "%Herr Hreply_sl Hrep".
    wp_pures.
    wp_if_destruct.
    { exfalso. done. }
    iModIntro. iLeft.
    iSplitR; first done.
    iExists _. iFrame.
  }
Qed.

Lemma wp_Clerk__TryWriteConfig (ck:loc) new_conf new_conf_sl epoch γ Φ :
  is_Clerk ck γ -∗
  readonly (own_slice_small new_conf_sl uint64T (DfracOwn 1) new_conf) -∗
  is_reserved_epoch_lb γ epoch -∗
  (□ Pwf new_conf) -∗
  □ (£ 1 -∗ |={⊤∖↑N,∅}=> ∃ latest_epoch reserved_epoch conf,
    own_latest_epoch γ latest_epoch ∗
    own_reserved_epoch γ reserved_epoch ∗
    own_config γ conf ∗ (⌜ epoch = reserved_epoch ⌝ -∗ own_config γ new_conf -∗
                         own_reserved_epoch γ reserved_epoch -∗
                         own_latest_epoch γ epoch
                         ={∅,⊤∖↑N}=∗
                         Φ #0)
  ) -∗
  (∀ (err:u64) , ⌜err ≠ 0⌝ -∗ Φ #err) -∗
  WP Clerk__TryWriteConfig #ck #epoch (slice_val new_conf_sl)
  {{ Φ }}
.
Proof.
  iIntros "#Hck #Hconf_sl #Hlb #HP_new #HΦ Hfail".
  wp_lam.
  wp_apply wp_ref_of_zero.
  { eauto. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hargs_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (args_ptr) "Hargs".
  wp_pures.
  wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hsl".
  wp_store.
  wp_apply (Config.wp_Encode with "[$]").
  iIntros (??) "(%HconfEnc & _ & Henc_sl)".
  iDestruct (own_slice_to_small with "Henc_sl") as "Henc_sl".
  wp_load.
  wp_apply (wp_WriteBytes with "[$Hsl $Henc_sl]").
  iIntros (?) "[Hargs_sl _]".
  wp_store.
  wp_pures.
  iDestruct (own_slice_to_small with "Hargs_sl") as "Hargs_sl".
  replace (uint.nat 0%Z) with (0%nat) by word.
  iAssert ( ∃ sl,
      "Hreply" ∷ reply_ptr ↦[slice.T byteT] (slice_val sl)
    )%I with "[Hreply]" as "HH".
  { rewrite zero_slice_val. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.

  iNamed "Hck".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hleader]").
  { iFrame "∗#". iNext. iExists _; iFrame "∗%". }
  wp_pures.
  wp_load.
  wp_loadField.
  apply list_lookup_lt in HleaderBound as [? Hlookup].
  iMod (readonly_load with "Hcls_sl") as (?) "Hcls_sl2".
  iDestruct (own_slice_small_sz with "Hcls_sl2") as %Hsl_sz.
  wp_apply (wp_SliceGet with "[$Hcls_sl2]").
  { done. }
  iIntros "_".
  iDestruct (big_sepL_lookup with "Hrpc") as (?) "#[Hcl_rpc Hhost]".
  { exact Hlookup. }
  iNamed "Hhost".
  wp_apply (wp_frame_wand with "[Hfail Hargs]"); first iNamedAccu.
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  { iFrame "#". }
  { (* successful RPC *)
    iModIntro.
    iNext.
    Opaque u64_le.
    rewrite /TryWriteConfig_spec /TryWriteConfig_core_spec /=.
    repeat iExists _.
    iSplitR.
    { iPureIntro. done. }
    iSplitR.
    { iPureIntro. done. }
    iFrame "#".
    Transparent u64_le.
    iSplitR.
    { (* case: successfully wrote new config and epoch *)
      iIntros "Hlc".
      iDestruct ("HΦ" with "Hlc") as "Hupd".
      (* case: got a new epoch, no error *)
      iMod "Hupd".
      iModIntro.
      iClear "H1 H2 H3".
      iDestruct "Hupd" as (???) "(H1&H2&H3&Hupd)".
      repeat iExists _.
      iFrame "H1 H2 H3".
      iIntros.
      iMod ("Hupd" with "[% //] [$] [$] [$]") as "Hupd".
      iModIntro.
      iIntros (?) "%Hconf_enc Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      subst.
      iDestruct ("Hrep_sl") as "[Hrep_sl1 Hrep_sl2]".
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_pures.
      iModIntro.
      iNamed 1.
      iRight. iSplitR; first done.
      wp_pures.
      wp_load.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_".
      wp_pures.
      iModIntro.
      iApply "Hupd".
    }
    { (* case: RPC ran, but was not able to write *)
      iIntros (?) "%Herr".
      iIntros (?) "%HrepEnc Harg_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      subst.
      iDestruct "Hrep_sl" as "[Hrep_sl Hrep_sl2]".
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_".
      wp_pures.
      wp_if_destruct.
      { (* case: ErrNotLeader, so retry *)
        wp_loadField.
        wp_apply (acquire_spec with "[$]").
        iIntros "[Hlocked Hown]".
        wp_pures.
        iNamed "Hown".
        wp_loadField.
        wp_if_destruct.
        { (* case: increase leader idx *)
          wp_loadField.
          wp_loadField.
          wp_apply (wp_slice_len).
          wp_pures.
          wp_storeField.
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "∗#".
            iNext. repeat iExists _; iFrame.
            iPureIntro.
            rewrite Hsl_sz.
            rewrite word.unsigned_modu_nowrap; last lia.
            { apply Z2Nat.inj_lt; auto using encoding.unsigned_64_nonneg.
              { apply Z.mod_pos; lia. }
              { apply Z_mod_lt; lia. }
            }
          }
          wp_pures.
          iModIntro. iNamed 1. iLeft.
          iSplitR; first done.
          iFrame.
        }
        { (* case: don't increase leader idx *)
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "∗#".
            iNext. repeat iExists _; iFrame "∗%".
          }
          wp_pures.
          iModIntro. iNamed 1.
          iLeft. iSplitR; first done.
          iFrame.
        }
      }
      { (* case: some other error, don't retry *)
        iModIntro. iNamed 1.
        iRight.
        iSplitR; first done.
        wp_pures.
        wp_load.
        wp_apply (wp_ReadInt with "[$]").
        iIntros (?) "_".
        wp_pures.
        iApply "Hfail".
        done.
      }
    }
  }
  {
    iIntros (?) "%Herr Hreply_sl Hrep".
    wp_pures.
    wp_if_destruct.
    2:{ exfalso. done. }
    iModIntro. iNamed 1. iLeft.
    iSplitR; first done.
    iFrame.
  }
Qed.

Lemma wp_Clerk__GetLease (ck:loc) γ epoch Φ :
  is_Clerk ck γ -∗
  □ ((∀ (leaseExpiration:u64) γl,
      is_lease epochLeaseN γl (own_latest_epoch γ epoch) -∗
      is_lease_valid_lb γl leaseExpiration -∗ Φ (#0, #leaseExpiration)%V) ∧
    (∀ (err:u64), ⌜err ≠ 0⌝ -∗ Φ (#err, #0)%V)
  ) -∗
  WP Clerk__GetLease #ck #epoch {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  wp_lam.
  wp_apply wp_ref_of_zero.
  { eauto. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (?) "Hargs_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (args_ptr) "Hargs".
  wp_pures.
  wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (?) "Hargs_sl".
  iDestruct (own_slice_to_small with "Hargs_sl") as "Hargs_sl".
  wp_store.
  wp_pures.
  iAssert ( ∃ sl,
      "Hreply" ∷ reply_ptr ↦[slice.T byteT] (slice_val sl)
    )%I with "[Hreply]" as "HH".
  { rewrite zero_slice_val. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.

  iNamed "Hck".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hleader]").
  { iFrame "∗#". iNext. iExists _; iFrame "∗%". }
  wp_pures.
  wp_load.
  wp_loadField.
  apply list_lookup_lt in HleaderBound as [? Hlookup].
  iMod (readonly_load with "Hcls_sl") as (?) "Hcls_sl2".
  iDestruct (own_slice_small_sz with "Hcls_sl2") as %Hsl_sz.
  wp_apply (wp_SliceGet with "[$Hcls_sl2]").
  { done. }
  iIntros "_".
  iDestruct (big_sepL_lookup with "Hrpc") as (?) "#[Hcl_rpc Hhost]".
  { exact Hlookup. }
  iNamed "Hhost".
  wp_apply (wp_frame_wand with "[Hargs]"); first iNamedAccu.
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hargs_sl Hreply").
  { iFrame "#". }
  { (* successful RPC *)
    iModIntro.
    iNext.
    Opaque u64_le.
    rewrite /GetLease_spec /GetLease_core_spec /=.
    repeat iExists _.
    iSplitR.
    { iPureIntro. done. }
    iSplit.
    { (* case: got a lease *)
      iClear "H1 H2".
      iIntros (??) "H1 H2".
      iIntros (?) "%Henc Hargs_sl".
      iIntros (?) "Hrep Hreply_sl".
      wp_pures.
      iLeft in "HΦ".
      iDestruct ("HΦ" with "[$] [$]") as "Hupd".
      wp_load.
      subst.
      iDestruct "Hreply_sl" as "[Hrep_sl Hrep_sl2]".
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_".
      wp_pures.
      iModIntro.
      iNamed 1.
      iRight.
      iSplitR; first done.
      wp_pures.
      wp_load.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "?".
      wp_pures.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_".
      wp_pures.
      iApply "Hupd".
    }
    { (* case: RPC ran, but server gave an error *)
      iIntros (?) "%Herr".
      iIntros (?) "%HrepEnc Harg_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      subst.
      iDestruct "Hrep_sl" as "[Hrep_sl Hrep_sl2]".
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_".
      wp_pures.
      wp_if_destruct.
      { (* case: ErrNotLeader, so retry *)
        wp_loadField.
        wp_apply (acquire_spec with "[$]").
        iIntros "[Hlocked Hown]".
        wp_pures.
        iNamed "Hown".
        wp_loadField.
        wp_if_destruct.
        { (* case: increase leader idx *)
          wp_loadField.
          wp_loadField.
          wp_apply (wp_slice_len).
          wp_pures.
          wp_storeField.
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "∗#".
            iNext. repeat iExists _; iFrame.
            iPureIntro.
            rewrite Hsl_sz.
            rewrite word.unsigned_modu_nowrap; last lia.
            { apply Z2Nat.inj_lt; auto using encoding.unsigned_64_nonneg.
              { apply Z.mod_pos; lia. }
              { apply Z_mod_lt; lia. }
            }
          }
          wp_pures.
          iModIntro. iNamed 1. iLeft.
          iSplitR; first done.
          iFrame.
        }
        { (* case: don't increase leader idx *)
          wp_loadField.
          wp_apply (release_spec with "[Hlocked Hleader]").
          {
            iFrame "∗#".
            iNext. repeat iExists _; iFrame "∗%".
          }
          wp_pures.
          iModIntro. iNamed 1.
          iLeft. iSplitR; first done.
          iFrame.
        }
      }
      { (* case: some other error, don't retry *)
        iModIntro. iNamed 1.
        iRight.
        iSplitR; first done.
        wp_pures.
        wp_load.
        wp_apply (wp_ReadInt with "[$]").
        iIntros (?) "?".
        wp_pures.
        wp_apply (wp_ReadInt with "[$]").
        iIntros (?) "_".
        wp_pures.
        iRight in "HΦ".
        iApply "HΦ".
        done.
      }
    }
  }
  {
    iIntros (?) "%Herr Hreply_sl Hrep".
    wp_pures.
    wp_if_destruct.
    2:{ exfalso. done. }
    iModIntro. iNamed 1. iLeft.
    iSplitR; first done.
    iFrame.
  }
Qed.

Lemma wp_makeServer γ γsrv fname data (paxosMe:u64) hosts_sl init_sl (hosts: list u64) :
  {{{
        "Hhosts_sl" ∷ (own_slice_small hosts_sl uint64T (DfracOwn 1) hosts) ∗
        "#Hinit" ∷ readonly (own_slice_small init_sl uint64T (DfracOwn 1) initconfig) ∗
        "#Hhost" ∷ is_paxos_server_host paxosMe γ.(paxos_gn) γsrv ∗
        "Hfile" ∷ crash_borrow (config_crash_resources γ γsrv data ∗ fname f↦ data)
                (∃ d, config_crash_resources γ γsrv d ∗ fname f↦ d) ∗
        "#Hpeers" ∷ is_config_peers hosts γ ∗
        "#Hconfig_inv" ∷ is_config_inv γ ∗
        "#Hwf" ∷ □ Pwf initconfig
  }}}
    makeServer #(str fname) #paxosMe (slice_val hosts_sl) (slice_val init_sl)
  {{{
        (s:loc), RET #s; is_Server s γ
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  iNamed "Hpeers".
  wp_call.
  wp_apply (wp_allocStruct); first by val_ty.
  iIntros (s) "Hs".
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".
  simpl.
  wp_pures.
  wp_apply wp_allocStruct; first by val_ty.
  iIntros (?) "Hs". iDestruct (struct_fields_split with "Hs") as "HH".
  wp_apply (state.wp_encode with "[HH]").
  {
    instantiate (1:=state.mk _ _ _ _ _).
    repeat iExists _. simpl. iNamed "HH". iFrame "∗#".
  }
  iIntros (?) "[Henc _]".
  wp_pures.
  iNamed "Hpeers".
  wp_apply (wp_StartServer with "[$Hfile $Hhosts_sl Henc]").
  {
    iFrame "∗#". simpl. iFrame.
    iModIntro. iExists _.
    iSplit; done.
  }
  iIntros (?) "#Hsrv".
  wp_storeField.
  iApply "HΦ".
  repeat iExists _.
  iMod (readonly_alloc_1 with "s") as "#s".
  by iFrame "Hsrv #".
Qed.

Lemma wp_StartServer γ γsrv fname me (paxosMe:u64) (data:list u8) hosts_sl init_sl (hosts: list u64) :
  {{{
        "Hhosts_sl" ∷ (own_slice_small hosts_sl uint64T (DfracOwn 1) hosts) ∗
        "#Hinit" ∷ readonly (own_slice_small init_sl uint64T (DfracOwn 1) initconfig) ∗
        "Hfile" ∷ crash_borrow (config_crash_resources γ γsrv data ∗ fname f↦ data)
                (∃ d, config_crash_resources γ γsrv d ∗ fname f↦ d) ∗

        "#Hhost" ∷ is_config_server_host me paxosMe γ γsrv ∗
        "#Hpeers" ∷ is_config_peers hosts γ ∗
        "#Hwf" ∷ □ Pwf initconfig

  }}}
    StartServer #(str fname) #me #paxosMe (slice_val hosts_sl) (slice_val init_sl)
  {{{
        (s:loc), RET #s; is_Server s γ
  }}}.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_call.
  wp_apply (wp_makeServer with "[-HΦ]").
  { iNamed "Hhost". iFrame "∗#". }
  iIntros (?) "#Hsrv".
  wp_pures.

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

  iNamed "Hhost". iNamed "HhostConf".
  iNamed "Hinvs".
  wp_apply (wp_StartServer_pred with "[$Hr]").
  { set_solver. }
  {
    unfold handlers_complete.
    repeat rewrite dom_insert_L.
    rewrite dom_empty_L.
    iSplitL "".
    { iExactEq "Hdom". f_equal. set_solver. }

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

Context `(params:configParams.t Σ).
Definition config_spec_list γ :=
  [ (W64 0, ReserveEpochAndGetConfig_spec γ) ;
    (W64 1, GetConfig_spec γ) ;
    (W64 2, TryWriteConfig_spec γ) ;
    (W64 3, GetLease_spec γ)].


Lemma alloc_config_rpc host γ :
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
  iApply to_named.
  iExactEq "H1".
  f_equal.
  set_solver.
Qed.

Definition own_config_res γ conf : iProp Σ :=
  own_latest_epoch γ 0 ∗ own_reserved_epoch γ 0 ∗ own_config γ conf.

Existing Instance pParams.
Lemma alloc_config_system (hostPairs: list (u64 * u64)) :
  length hostPairs > 0 →
  ([∗ list] h ∈ hostPairs, h.1 c↦ ∅ ∗ h.2 c↦ ∅) -∗
  □ (Pwf initconfig)
  ={⊤}=∗
  ∃ γ,
    ([∗ list] h ∈ hostPairs,
       ∃ γsrv,
         is_config_peers (hostPairs.*2) γ ∗
         is_config_server_host h.1 h.2 γ γsrv ∗
         config_crash_resources γ γsrv []) ∗
    is_config_hosts (hostPairs.*1) γ ∗
    own_config_res γ initconfig
.
Proof.
  intros ?.
  iIntros "Hchans #HP".
  iDestruct (big_sepL_sep with "Hchans") as "[Hc Hp]".
  iMod (alloc_paxos_system pParams (hostPairs.*2) with "[Hp] []") as "H".
  { rewrite fmap_length. lia. }
  { by rewrite big_sepL_fmap. }
  { simpl. iExists _.

    iSplitR.
    { done. }
    iModIntro.
    iFrame "HP".
  }
  iDestruct "H" as (?) "(Hsrvs & #Hhost & Hst)".

  (* allocate config-specific ghost state *)
  iMod (mono_nat_own_alloc 0) as (γepoch) "[[Hepoch Hepoch2] _]".
  iMod (mono_nat_own_alloc 0) as (γres) "[[Hres Hres2] _]".
  iMod (ghost_var_alloc initconfig) as (γconf) "[Hconf Hconf2]".

  iExists (Build_config_names _ _ _ _).
  iAssert (|={⊤}=> is_config_hosts hostPairs.*1 _)%I with "[Hc]" as ">#Hhosts".
  {
    rewrite /is_config_hosts.
    iSplitL.
    2:{ iPureIntro. by rewrite fmap_length. }
    iApply big_sepL_fupd.
    rewrite big_sepL_fmap.
    iApply (big_sepL_impl with "Hc").
    iModIntro. iIntros.
    by iMod (alloc_config_rpc with "[$]").
  }
  iMod fupd_mask_subseteq as "Hmask".
  2: iMod (lease_alloc _ epochLeaseN with "Hepoch") as (?) "(_ & Hepoch & Hexp)".
  { solve_ndisj. }
  iMod "Hmask".
  iAssert (|={⊤}=> is_config_invs _)%I with "[Hst Hepoch Hexp Hres Hconf]" as ">#Hinv".
  {
    iMod (inv_alloc with "[-]") as "$"; last done.
    iNext. repeat iExists _.
    simpl. rewrite /initstate.
    instantiate (2:=(Build_config_names _ _ _ _)).
    simpl. by iFrame "Hst ∗".
  }
  iFrame "Hhosts".
  iSplitL "Hsrvs".
  {
    iModIntro.
    rewrite big_sepL_fmap.
    iApply (big_sepL_impl with "Hsrvs").
    iModIntro. iIntros "* %Hlookup H".
    iDestruct "H" as (?) "[#Hmphost Hcrash]".
    iExists _; iFrame "Hmphost".
    iSplitR.
    { by rewrite /is_config_peers /=. }
    iSplitR.
    { iFrame "#".
      iNamed "Hhosts".
      iDestruct (big_sepL_lookup with "Hhosts") as "$".
      rewrite list_lookup_fmap.
      instantiate (1:=k). rewrite Hlookup. done.
    }
    iNamed "Hcrash".
    repeat iExists _. iFrame. done.
  }
  iModIntro. iFrame.
Qed.

End config_init.
