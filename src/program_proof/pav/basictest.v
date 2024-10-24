From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import advrpc auditor core client cryptoffi rpc serde server.
From Perennial.program_proof Require Import std_proof.

Module adtrPk.
Record t :=
  mk {
    pk: list w8;
    γ: gname;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : Slice.t) (obj : t) : iProp Σ :=
  own_slice_small ptr byteT DfracDiscarded obj.(pk).
End defs.
End adtrPk.

Module setupParams.
Record t :=
  mk {
    servAddr: w64;
    servSigPk: list w8;
    serv_γ: gname;
    servVrfPk: loc;
    adtrAddrs: list w64;
    adtrPks: list adtrPk.t;
  }.
Section defs.
Context `{!heapGS Σ, !pavG Σ}.
Definition valid (ptr : loc) (obj : t) (serv_good adtrs_good : bool) : iProp Σ :=
  ∃ sl_servSigPk sl_adtrAddrs sl_adtrPks dim0_adtrPks,
  "#Hptr_servAddr" ∷ ptr ↦[setupParams :: "servAddr"]□ #obj.(servAddr) ∗
  "#Hptr_servSigPk" ∷ ptr ↦[setupParams :: "servSigPk"]□ (slice_val sl_servSigPk) ∗
  "#Hsl_servSigPk" ∷ own_slice_small sl_servSigPk byteT DfracDiscarded obj.(servSigPk) ∗
  "#His_good_serv" ∷ (if serv_good then is_pk obj.(servSigPk) (serv_sigpred obj.(serv_γ)) else True) ∗
  "#Hptr_servVrfPk" ∷ ptr ↦[setupParams :: "servVrfPk"]□ #obj.(servVrfPk) ∗
  "#Hptr_adtrAddrs" ∷ ptr ↦[setupParams :: "adtrAddrs"]□ (slice_val sl_adtrAddrs) ∗
  "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded obj.(adtrAddrs) ∗
  "#Hptr_adtrPks" ∷ ptr ↦[setupParams :: "adtrPks"]□ (slice_val sl_adtrPks) ∗
  "#Hsl_adtrPks" ∷ own_slice_small sl_adtrPks (slice.T byteT) DfracDiscarded dim0_adtrPks ∗
  "#Hdim0_adtrPks" ∷ ([∗ list] p;o ∈ dim0_adtrPks;obj.(adtrPks), adtrPk.own p o) ∗
  "#His_good_adtrs" ∷ (if adtrs_good then
    ∃ i o, ⌜ obj.(adtrPks) !! i = Some o ⌝ ∗
      is_pk o.(adtrPk.pk) (adtr_sigpred o.(adtrPk.γ))
    else True) ∗
  "%Hlen_addr_pk" ∷ ⌜ length obj.(adtrAddrs) = length obj.(adtrPks) ⌝.
End defs.
End setupParams.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_setup (serv_good adtrs_good : bool) (servAddr : w64) sl_adtrAddrs (adtrAddrs : list w64) :
  {{{
    "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded adtrAddrs ∗
    "%Hlen_adtrs" ∷ ⌜ length adtrAddrs > 0 ⌝
  }}}
  setup #servAddr (slice_val sl_adtrAddrs)
  {{{
    ptr_setup setup, RET #ptr_setup;
    "#Hsetup" ∷ setupParams.valid ptr_setup setup serv_good adtrs_good
  }}}.
Proof.
  rewrite /setup. iIntros (Φ) "H HΦ". iNamed "H".
  wp_apply wp_newServer. iIntros (???? serv_γ ?). iNamed 1.
  wp_apply (wp_newRpcServer with "Hown_serv"). iIntros (??). iNamed 1.
  wp_apply (wp_Server__Serve with "Hown_rpcserv").
  wp_apply wp_ref_of_zero; [done|]. iIntros (?) "Hptr_adtrPks".
  wp_apply (wp_forSlicePrefix
    (λ doneV _, ∃ sl_adtrPks dim0_adtrPks adtrPks,
    "Hptr_adtrPks" ∷ l ↦[slice.T (slice.T byteT)] (slice_val sl_adtrPks) ∗
    "Hsl_adtrPks" ∷ own_slice sl_adtrPks (slice.T byteT) (DfracOwn 1) dim0_adtrPks ∗
    "#Hdim0_adtrPks" ∷ ([∗ list] p;o ∈ dim0_adtrPks;adtrPks, adtrPk.own p o) ∗
    "#His_adtrPks" ∷ ([∗ list] x ∈ adtrPks, is_pk x.(adtrPk.pk) (adtr_sigpred x.(adtrPk.γ))) ∗
    "%Hlen_adtrPks" ∷ ⌜ length doneV = length dim0_adtrPks ⌝)%I
    with "[] [$Hsl_adtrAddrs Hptr_adtrPks]").
  { clear. iIntros "* _". iIntros (Φ) "!>". iIntros "(%&%&%&H) HΦ". iNamed "H".
    wp_apply wp_newAuditor. iIntros "*". iNamed 1.
    wp_apply (wp_newRpcAuditor with "[$Hvalid_adtr]"). iIntros "*". iNamed 1.
    wp_apply (wp_Server__Serve with "Hown_rpcserv").
    wp_load. wp_apply (wp_SliceAppend with "Hsl_adtrPks"). iIntros "* Hsl_adtrPks".
    wp_store. iApply "HΦ". iFrame.
    iExists (adtrPks ++ [adtrPk.mk adtrPk adtr_γ]). iIntros "!>". iSplit; [|iSplit].
    - iApply big_sepL2_snoc. iFrame "#".
    - by iFrame "#".
    - iPureIntro. rewrite !length_app. solve_length. }
  { iExists Slice.nil, [], []. iFrame. iSplit; [|naive_solver].
    iApply own_slice_zero. }
  iIntros "[_ (%&%&%&H)]". iNamed "H".
  wp_apply wp_Sleep. wp_load. iApply wp_fupd.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iMod (struct_pointsto_persist with "H") as "H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  iDestruct (own_slice_to_small with "Hsl_adtrPks") as "Hsl_adtrPks".
  iMod (own_slice_small_persist with "Hsl_adtrPks") as "#Hsl_adtrPks".
  iIntros "!>". iApply ("HΦ" $! _ (setupParams.mk _ _ serv_γ _ _ _)).
  iFrame "∗#". simpl. iSplitL; [|iSplitL].
  - destruct serv_good; [iFrame "#"|done].
  - destruct adtrs_good; [|done].
    iDestruct (big_sepL2_length with "Hdim0_adtrPks") as %Hlen.
    list_elem adtrPks 0 as adtrPk.
    iDestruct (big_sepL_lookup with "His_adtrPks") as "His_adtrPk"; [exact HadtrPk_lookup|].
    iFrame "#%".
  - iDestruct (big_sepL2_length with "Hdim0_adtrPks") as %?. iPureIntro. lia.
Qed.

Lemma wp_mkRpcClients sl_addrs (addrs : list w64) :
  {{{
    "#Hsl_addrs" ∷ own_slice_small sl_addrs uint64T DfracDiscarded addrs
  }}}
  mkRpcClients (slice_val sl_addrs)
  {{{
    sl_rpcs dim0_rpcs rpcs, RET (slice_val sl_rpcs);
    "#Hsl_rpcs" ∷ own_slice_small sl_rpcs ptrT DfracDiscarded dim0_rpcs ∗
    "Hdim0_rpcs" ∷ ([∗ list] p;o ∈ dim0_rpcs;rpcs, advrpc.Client.own p o)
  }}}.
Proof.
  rewrite /mkRpcClients. iIntros (ϕ) "H HΦ". iNamed "H".
  wp_apply wp_ref_of_zero; [done|]. iIntros "* Hptr_c".
  wp_apply (wp_forSlicePrefix
    (λ doneV _, ∃ sl_c dim0_c c,
    "Hptr_c" ∷ l ↦[slice.T ptrT] (slice_val sl_c) ∗
    "Hsl_c" ∷ own_slice sl_c ptrT (DfracOwn 1) dim0_c ∗
    "Hdim0_c" ∷ ([∗ list] p;o ∈ dim0_c;c, advrpc.Client.own p o) ∗
    "%Hlen_c" ∷ ⌜ length doneV = length dim0_c ⌝)%I
    with "[] [$Hsl_addrs Hptr_c]").
  { clear. iIntros "* _". iIntros (ϕ) "!>". iIntros "(%&%&%&H) HΦ". iNamed "H".
    wp_apply wp_Dial. iIntros (??). iNamed 1. wp_load.
    wp_apply (wp_SliceAppend with "Hsl_c"). iIntros (?) "Hsl_c". wp_store.
    iApply "HΦ". iFrame. iExists (c ++ [cli]). iIntros "!>". iSplit.
    - iApply big_sepL2_snoc. iFrame.
    - iPureIntro. rewrite !length_app. solve_length. }
  { iExists Slice.nil, [], []. iFrame. iSplit; [|naive_solver].
    iApply own_slice_zero. }
  iIntros "[_ (%&%&%&H)]". iNamed "H". wp_load.
  iDestruct (own_slice_to_small with "Hsl_c") as "Hsl_c".
  iMod (own_slice_small_persist with "Hsl_c") as "#Hsl_c".
  iApply "HΦ". naive_solver.
Qed.

Lemma wp_updAdtrsOnce ptr_upd upd sl_rpcs dim0_rpcs rpcs :
  {{{
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd ∗
    "#Hsl_rpcs" ∷ own_slice_small sl_rpcs ptrT DfracDiscarded dim0_rpcs ∗
    "Hdim0_rpcs" ∷ ([∗ list] p;o ∈ dim0_rpcs;rpcs, advrpc.Client.own p o)
  }}}
  updAdtrsOnce #ptr_upd (slice_val sl_rpcs)
  {{{
    RET #();
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd ∗
    "Hdim0_rpcs" ∷ ([∗ list] p;o ∈ dim0_rpcs;rpcs, advrpc.Client.own p o)
  }}}.
Proof.
  rewrite /updAdtrsOnce. iIntros (Φ) "H HΦ". iNamed "H".
  wp_apply (wp_forSlicePrefix
    (λ _ _,
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd ∗
    "Hdim0_rpcs" ∷ ([∗ list] p;o ∈ dim0_rpcs;rpcs, advrpc.Client.own p o))%I
    with "[] [$Hsl_rpcs $Hown_upd $Hdim0_rpcs]").
  { clear. iIntros "* %Hin". iIntros (ϕ) "!>". iIntros "H HΦ". iNamed "H".
    (* TODO: would be better if lemma just gave lookup. *)
    assert (dim0_rpcs !! (length done) = Some x) as Hlook0.
    { simplify_eq/=. by rewrite list_lookup_middle. }
    iDestruct (big_sepL2_lookup_1_some with "Hdim0_rpcs") as %[? Hlook1]; [exact Hlook0|].
    iDestruct (big_sepL2_lookup_acc with "Hdim0_rpcs") as "[Hown_cli Hclose]"; [done..|].
    wp_apply (wp_callAdtrUpdate with "[$Hown_cli $Hown_upd]"). iIntros "*". iNamed 1.
    wp_apply wp_Assume. iIntros "_".
    iDestruct ("Hclose" with "Hown_cli") as "Hdim0_rpcs". iApply "HΦ". iFrame. }
  iIntros "[_ H]". iNamed "H". wp_pures. iApply "HΦ". by iFrame.
Qed.

Lemma wp_doAudits ptr_cli cli sl_addrs (addrs : list w64) sl_adtrPks dim0_adtrPks adtrPks :
  {{{
    "Hown_cli" ∷ client.Client.own ptr_cli cli ∗
    "#Hsl_addrs" ∷ own_slice_small sl_addrs uint64T DfracDiscarded addrs ∗
    "#Hsl_adtrPks" ∷ own_slice_small sl_adtrPks (slice.T byteT) DfracDiscarded dim0_adtrPks ∗
    "#Hdim0_adtrPks" ∷ ([∗ list] p;o ∈ dim0_adtrPks;adtrPks, adtrPk.own p o) ∗
    "%Hlen_addr_pk" ∷ ⌜ length addrs = length dim0_adtrPks ⌝
  }}}
  doAudits #ptr_cli (slice_val sl_addrs) (slice_val sl_adtrPks)
  {{{
    RET #();
    "Hown_cli" ∷ client.Client.own ptr_cli cli ∗
    "Haudits" ∷ ([∗ list] x ∈ adtrPks,
      is_pk x.(adtrPk.pk) (adtr_sigpred x.(adtrPk.γ)) -∗
      ("#His_audit" ∷ is_audit cli.(Client.γ) x.(adtrPk.γ) cli.(Client.next_epoch)))
  }}}.
Proof.
  rewrite /doAudits. iIntros "* H HΦ". iNamed "H".
  wp_apply wp_slice_len. wp_apply wp_ref_to; [val_ty|]. iIntros "* Hptr_idx".
  iDestruct (own_slice_small_sz with "Hsl_addrs") as %?.
  iDestruct (own_slice_small_sz with "Hsl_adtrPks") as %?.
  iDestruct (big_sepL2_length with "Hdim0_adtrPks") as %?.
  wp_apply (wp_forUpto'
    (λ i,
    "Hown_cli" ∷ client.Client.own ptr_cli cli ∗
    "Haudits" ∷ ([∗ list] x ∈ (take (uint.nat i) adtrPks),
      is_pk x.(adtrPk.pk) (adtr_sigpred x.(adtrPk.γ)) -∗
      ("#His_audit" ∷ is_audit cli.(Client.γ) x.(adtrPk.γ) cli.(Client.next_epoch))))%I
    with "[$Hptr_idx $Hown_cli]").
  { iSplit; [|naive_solver]. iPureIntro. word. }
  { iIntros "!> * (H&Hptr_idx&%Hinb) HΦ". iNamed "H".
    list_elem addrs (uint.nat i) as addr.
    wp_load. wp_apply (wp_SliceGet with "[$Hsl_addrs]"); [done|]. iIntros "_".
    list_elem dim0_adtrPks (uint.nat i) as ptr_adtrPk.
    wp_load. wp_apply (wp_SliceGet with "[$Hsl_adtrPks]"); [done|]. iIntros "_".
    list_elem adtrPks (uint.nat i) as adtrPk.
    iDestruct (big_sepL2_lookup _ _ _ (uint.nat i) with "Hdim0_adtrPks") as "Hadtr_pk"; [done..|].
    wp_apply (wp_Client__Audit with "[$Hown_cli $Hadtr_pk]").
    iIntros (? err) "Haud". iNamed "Haud". wp_loadField.
    destruct err.(clientErr.err).
    { wp_apply wp_Assume_false. }
    wp_apply wp_Assume. iIntros "_ /=". iNamed "Haud".
    wp_pures. iApply "HΦ". iFrame.
    replace (uint.nat (word.add i (W64 1))) with (S $ uint.nat i); [|word].
    rewrite (take_S_r _ _ _ HadtrPk_lookup).
    iSpecialize ("Hcan_audit" $! adtrPk.(adtrPk.γ)). iFrame. naive_solver. }
  iIntros "[H _]". iNamed "H".
  replace (uint.nat sl_addrs.(Slice.sz)) with (length adtrPks); [|lia].
  iEval (rewrite take_ge) in "Haudits". wp_pures. iApply "HΦ". by iFrame.
Qed.

Lemma wp_testBasic ptr_setup setup :
  {{{
    "#Hsetup" ∷ setupParams.valid ptr_setup setup false true
  }}}
  testBasic #ptr_setup
  {{{ RET #(); True }}}.
Proof using Type*.
  rewrite /testBasic. iIntros (Φ) "H HΦ". iNamed "H".
  iNamed "Hsetup". iClear "His_good_serv".

  (* alice put. *)
  do 3 wp_loadField. wp_apply (wp_newClient with "Hsl_servSigPk").
  iIntros (?????). iNamedSuffix 1 "_al".
  wp_apply wp_SliceSingleton; [val_ty|]. iIntros (?) "Hpk0".
  iDestruct (slice.own_slice_to_small with "Hpk0") as "Hpk0".
  wp_apply (wp_Client__Put with "[$Hown_cli_al Hpk0]").
  { instantiate (1:=[_]). iFrame "Hpk0". }
  iIntros (ep0 ? err0) "H /=". iNamedSuffix "H" "_al".
  wp_loadField. iClear "Herr_al". destruct err0.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_al".

  (* update auditors. *)
  wp_loadField. wp_apply wp_Dial. iIntros (??). iNamedSuffix 1 "_serv".
  wp_apply (wp_callServAudit with "Hown_cli_serv").
  iIntros (?? err1) "H". iNamedSuffix "H" "_serv". destruct err1.
  { wp_apply wp_Assume_false. }
  simpl. iNamedSuffix "H" "0". wp_apply wp_Assume. iIntros "_".
  wp_apply (wp_callServAudit with "Hown_cli_serv").
  iIntros (?? err2) "H". iNamedSuffix "H" "_serv". destruct err2.
  { wp_apply wp_Assume_false. }
  simpl. iNamedSuffix "H" "1". wp_apply wp_Assume. iIntros "_".

  wp_loadField. wp_apply (wp_mkRpcClients with "Hsl_adtrAddrs").
  iIntros "*". iNamed 1.
  wp_apply (wp_updAdtrsOnce with "[$Hown_upd0 $Hsl_rpcs $Hdim0_rpcs]").
  iNamedSuffix 1 "0".
  wp_apply (wp_updAdtrsOnce with "[$Hown_upd1 $Hsl_rpcs $Hdim0_rpcs0]").
  iNamedSuffix 1 "1".

  (* bob get. *)
  do 3 wp_loadField.
  wp_apply (wp_newClient with "Hsl_servSigPk"). iIntros (?????). iNamedSuffix 1 "_bob".
  wp_apply (wp_Client__Get with "Hown_cli_bob").
  iIntros (is_reg ?? ep1 ? err7) "H /=". iNamedSuffix "H" "_bob".
  wp_loadField. iClear "Herr_bob". destruct err7.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_". wp_apply wp_Assume. iIntros "%Heq_ep /=".
  iNamedSuffix "H" "_bob". iRename "H" into "Hreg".

  (* alice and bob audit. *)
  do 2 wp_loadField.
  iDestruct (big_sepL2_length with "Hdim0_adtrPks") as %?. 
  wp_apply (wp_doAudits with "[$Hown_cli_al $Hsl_adtrAddrs $Hsl_adtrPks $Hdim0_adtrPks]").
  { iPureIntro. lia. }
  simpl. iNamedSuffix 1 "_al". do 2 wp_loadField.
  wp_apply (wp_doAudits with "[$Hown_cli_bob $Hsl_adtrAddrs $Hsl_adtrPks $Hdim0_adtrPks]").
  { iPureIntro. lia. }
  simpl. iNamedSuffix 1 "_bob".

  (* main part: proving the pk's are equal. *)
  iDestruct "His_good_adtrs" as (??) "[%Hlook_pk His_pk]".
  iDestruct (big_sepL_lookup_acc with "Haudits_al") as "[Hcan_aud_al _]"; [exact Hlook_pk|].
  iDestruct ("Hcan_aud_al" with "His_pk") as "H". iNamedSuffix "H" "_al".
  iDestruct (big_sepL_lookup_acc with "Haudits_bob") as "[Hcan_aud_bob _]"; [exact Hlook_pk|].
  iDestruct ("Hcan_aud_bob" with "His_pk") as "H". iNamedSuffix "H" "_bob".
  case_bool_decide; [|done]. simplify_eq/=.
  iClear "Hsl_servSigPk Hsl_adtrAddrs Hsl_adtrPks Hdim0_adtrPks His_pk Hsl_rpcs
    Hptr_servAddr Hptr_servSigPk Hptr_servVrfPk Hptr_adtrAddrs Hptr_adtrPks
    Hown_cli_serv Hown_upd0 Hown_upd1 Hdim0_rpcs1 Hown_cli_al Hown_cli_bob".
  clear -Hnoof_ep_al.
  iDestruct (audit_is_my_key with "His_key_al His_audit_al") as "His_key_al_aud"; [word|].
  destruct is_reg; last first.
  { iNamed "Hreg".
    iDestruct (audit_is_no_other_key with "His_no_key His_audit_bob") as "His_no_key_aud"; [word|].
    iNamedSuffix "His_key_al_aud" "_al". iNamedSuffix "Haux_al" "_al".
    iNamedSuffix "His_no_key_aud" "_bob".
    iDestruct (mono_list_idx_agree with "Hadtr_map_al Hadtr_map_bob") as %->.
    iDestruct (is_vrf_func (W64 0, W64 0) with "Hhash0_al Hhash_bob") as %->.
    simplify_map_eq/=. }
  wp_apply wp_Assert_true. iNamedSuffix "Hreg" "_bob".
  wp_apply (wp_BytesEqual with "[$Hsl_pk_al $Hsl_pk_bob]"). iIntros "_".
  iDestruct (audit_is_other_key with "His_key_bob His_audit_bob") as "His_key_bob_aud"; [word|].
  iNamedSuffix "His_key_al_aud" "_al". iNamedSuffix "His_key_bob_aud" "_bob".
  iDestruct (mono_list_idx_agree with "Hadtr_map_al Hadtr_map_bob") as %->.
  iDestruct (msv_is_my_key with "Haux_al") as (vals0) "[Hmsv0 %Hvals0]".
  iDestruct (msv_is_other_key with "Haux_bob") as (? vals1) "[Hmsv1 %Hvals1]".
  iDestruct (msv_opaque_func (adtr_map0, W64 0) with "Hmsv0 Hmsv1") as %->.
  simplify_eq/=. iDestruct (is_comm_inj with "Hcomm_al Hcomm_bob") as %->.
  wp_apply wp_Assert; [by case_bool_decide|]. wp_pures. by iApply "HΦ".
Qed.

Lemma wp_testBasicFull (servAddr : w64) sl_adtrAddrs (adtrAddrs : list w64) :
  {{{
    "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded adtrAddrs ∗
    "%Hlen_adtrAddrs" ∷ ⌜ length adtrAddrs > 0 ⌝
  }}}
  testBasicFull #servAddr (slice_val sl_adtrAddrs)
  {{{ RET #(); True }}}.
Proof using Type*.
  rewrite /testBasicFull. iIntros (Φ) "H HΦ". iNamed "H".
  wp_apply (wp_setup false true with "[$Hsl_adtrAddrs]"); [done|]. iIntros "*". iNamed 1.
  wp_apply (wp_testBasic with "Hsetup"). wp_pures. by iApply "HΦ".
Qed.

End proof.
