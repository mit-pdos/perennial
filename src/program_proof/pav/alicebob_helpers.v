From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import alicebob.

From Perennial.program_proof.pav Require Import
  auditor advrpc core client cryptoffi logical_audit rpc serde server.

Module setupParams.
Record t :=
  mk {
    serv_good: bool;
    servAddr: w64;
    serv: Server.t;
    adtr_good: bool;
    adtrAddrs: list w64;
    adtr_pks: list (list w8);
  }.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_servSigPk sl_serv_vrf_pk sl_adtrAddrs sl_adtrPks dim0_adtrPks,
  "Hptr_serv_good" ∷ ptr ↦[setupParams :: "servGood"] #obj.(serv_good) ∗
  "#Hptr_servAddr" ∷ ptr ↦[setupParams :: "servAddr"]□ #obj.(servAddr) ∗
  "#Hptr_servSigPk" ∷ ptr ↦[setupParams :: "servSigPk"]□ (slice_val sl_servSigPk) ∗
  "#Hptr_serv_vrf_pk" ∷ ptr ↦[setupParams :: "servVrfPk"]□ (slice_val sl_serv_vrf_pk) ∗
  "Hptr_adtr_good" ∷ ptr ↦[setupParams :: "adtrGood"] #obj.(adtr_good) ∗
  "#Hptr_adtrAddrs" ∷ ptr ↦[setupParams :: "adtrAddrs"]□ (slice_val sl_adtrAddrs) ∗
  "#Hptr_adtrPks" ∷ ptr ↦[setupParams :: "adtrPks"]□ (slice_val sl_adtrPks) ∗

  "#Hsl_servSigPk" ∷ own_slice_small sl_servSigPk byteT DfracDiscarded obj.(serv).(Server.sig_pk) ∗
  "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded obj.(adtrAddrs) ∗
  "#Hsl_adtrPks" ∷ own_slice_small sl_adtrPks (slice.T byteT) DfracDiscarded dim0_adtrPks ∗
  "#Hsl_serv_vrf_pk" ∷ own_slice_small sl_serv_vrf_pk byteT DfracDiscarded obj.(serv).(Server.vrf_pk) ∗

  "#Hdim0_adtrPks" ∷ ([∗ list] p;o ∈ dim0_adtrPks;obj.(adtr_pks),
    own_slice_small p byteT DfracDiscarded o) ∗

  "#His_good_serv" ∷ (if negb obj.(serv_good) then True else
    is_sig_pk obj.(serv).(Server.sig_pk) (sigpred obj.(serv).(Server.γhist))) ∗
  "#His_good_adtrs" ∷ (if negb obj.(adtr_good) then True else
    ∃ i sig_pk γadtr,
    "%Hlook_adtr" ∷ ⌜ obj.(adtr_pks) !! i = Some sig_pk ⌝ ∗
    "#His_good_adtr" ∷ is_sig_pk sig_pk (sigpred γadtr)) ∗
  "%Hlen_addr_pk" ∷ ⌜ length obj.(adtrAddrs) = length obj.(adtr_pks) ⌝.

End defs.
End setupParams.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_setup (servAddr : w64) sl_adtrAddrs (adtrAddrs : list w64) (uids : gset w64) :
  {{{
    "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded adtrAddrs ∗
    "%Hlen_adtrs" ∷ ⌜ length adtrAddrs > 0 ⌝
  }}}
  setup #servAddr (slice_val sl_adtrAddrs)
  {{{
    ptr_setup serv adtr_pks, RET #ptr_setup;
    "Hsetup" ∷ setupParams.own ptr_setup (setupParams.mk true
      servAddr serv true adtrAddrs adtr_pks) ∗
    "Huids" ∷ [∗ set] u ∈ uids, u ↪[serv.(Server.γvers)] W64 0
  }}}.
Proof.
  rewrite /setup. iIntros (Φ) "H HΦ". iNamed "H".
  wp_apply (wp_NewServer uids).
  iIntros "*". iNamed 1.
  iPoseProof "Hserv" as "H". iNamed "H".
  wp_apply (wp_VrfPublicKeyEncode with "Hptr_vrf_pk").
  iIntros "*". iNamedSuffix 1 "_vrf".
  iPersist "Hsl_enc_vrf".
  wp_apply (wp_NewRpcServer with "Hserv"). iIntros (??). iNamed 1.
  wp_apply (wp_Server__Serve with "Hown_rpcserv").
  wp_apply wp_ref_of_zero; [done|]. iIntros (?) "Hptr_adtrPks".
  wp_apply (wp_forSlicePrefix
    (λ doneV _, ∃ sl_adtrPks dim0_adtrPks adtrPks,
    "Hptr_adtrPks" ∷ l ↦[slice.T (slice.T byteT)] (slice_val sl_adtrPks) ∗
    "Hsl_adtrPks" ∷ own_slice sl_adtrPks (slice.T byteT) (DfracOwn 1) dim0_adtrPks ∗
    "#Hdim0_adtrPks" ∷ ([∗ list] p;o ∈ dim0_adtrPks;adtrPks,
      own_slice_small p byteT DfracDiscarded o) ∗
    "#His_adtrPks" ∷ ([∗ list] x ∈ adtrPks,
      ∃ γadtr, is_sig_pk x (sigpred γadtr)) ∗
    "%Hlen_adtrPks" ∷ ⌜ length doneV = length dim0_adtrPks ⌝)%I
    with "[] [$Hsl_adtrAddrs Hptr_adtrPks]").
  { clear. iIntros "* _". iIntros (Φ) "!>". iIntros "(%&%&%&H) HΦ". iNamed "H".
    wp_apply wp_NewAuditor. iIntros "*". iNamed 1.
    wp_apply (wp_NewRpcAuditor with "Hvalid_adtr"). iIntros "*". iNamed 1.
    wp_apply (wp_Server__Serve with "Hown_rpcserv").
    wp_load. wp_apply (wp_SliceAppend with "Hsl_adtrPks"). iIntros "* Hsl_adtrPks".
    wp_store. iApply "HΦ". iFrame.
    iExists (adtrPks ++ [adtrPk]). iIntros "!>". iSplit; [|iSplit].
    - iApply big_sepL2_snoc. iFrame "#".
    - by iFrame "#".
    - iPureIntro. rewrite !length_app. solve_length. }
  { iExists Slice.nil, [], []. iFrame. iSplit; [|naive_solver].
    iApply own_slice_zero. }
  iIntros "[_ (%&%&%&H)]". iNamed "H".
  wp_apply wp_Sleep. wp_load. iApply wp_fupd.

  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  iPersist "servAddr servSigPk servVrfPk adtrAddrs adtrPks".
  iDestruct (own_slice_to_small with "Hsl_adtrPks") as "Hsl_adtrPks".
  iMod (own_slice_small_persist with "Hsl_adtrPks") as "#Hsl_adtrPks".

  iIntros "!>". iApply "HΦ".
  iFrame "∗#". simpl.
  do 2 try iSplit.
  - iDestruct (is_sig_sk_to_pk with "HsigSk") as "$".
  - iDestruct (big_sepL2_length with "Hdim0_adtrPks") as %Hlen.
    list_elem adtrPks 0 as adtrPk.
    iDestruct (big_sepL_lookup with "His_adtrPks") as "[% His_adtrPk]"; [exact HadtrPk_lookup|].
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
    "Hdim0_rpcs" ∷ ([∗ list] p;o ∈ dim0_rpcs;rpcs, own_Client p o false)
  }}}.
Proof.
  rewrite /mkRpcClients. iIntros (ϕ) "H HΦ". iNamed "H".
  wp_apply wp_ref_of_zero; [done|]. iIntros "* Hptr_c".
  wp_apply (wp_forSlicePrefix
    (λ doneV _, ∃ sl_c dim0_c c,
    "Hptr_c" ∷ l ↦[slice.T ptrT] (slice_val sl_c) ∗
    "Hsl_c" ∷ own_slice sl_c ptrT (DfracOwn 1) dim0_c ∗
    "Hdim0_c" ∷ ([∗ list] p;o ∈ dim0_c;c, own_Client p o false) ∗
    "%Hlen_c" ∷ ⌜ length doneV = length dim0_c ⌝)%I
    with "[] [$Hsl_addrs Hptr_c]").
  { clear. iIntros "* _". iIntros (ϕ) "!>". iIntros "(%&%&%&H) HΦ". iNamed "H".
    wp_apply (wp_Dial _ false). iIntros "*". iNamed 1. wp_load.
    wp_apply (wp_SliceAppend with "Hsl_c"). iIntros (?) "Hsl_c". wp_store.
    iApply "HΦ". iFrame. iExists (c ++ [x]). iIntros "!>". iSplit.
    - iApply big_sepL2_snoc. iFrame.
    - iPureIntro. rewrite !length_app. solve_length. }
  { iExists Slice.nil, [], []. iFrame. iSplit; [|naive_solver].
    iApply own_slice_zero. }
  iIntros "[_ (%&%&%&H)]". iNamed "H". wp_load.
  iDestruct (own_slice_to_small with "Hsl_c") as "Hsl_c".
  iMod (own_slice_small_persist with "Hsl_c") as "#Hsl_c".
  iApply "HΦ". naive_solver.
Qed.

Lemma wp_updAdtrsOnce ptr_upd upd d0 sl_rpcs dim0_rpcs rpcs :
  {{{
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd d0 ∗
    "#Hsl_rpcs" ∷ own_slice_small sl_rpcs ptrT DfracDiscarded dim0_rpcs ∗
    "Hdim0_rpcs" ∷ ([∗ list] p;o ∈ dim0_rpcs;rpcs, own_Client p o false)
  }}}
  updAdtrsOnce #ptr_upd (slice_val sl_rpcs)
  {{{
    RET #();
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd d0 ∗
    "Hdim0_rpcs" ∷ ([∗ list] p;o ∈ dim0_rpcs;rpcs, own_Client p o false)
  }}}.
Proof.
  rewrite /updAdtrsOnce. iIntros (Φ) "H HΦ". iNamed "H".
  wp_apply (wp_forSlicePrefix
    (λ _ _,
    "Hown_upd" ∷ UpdateProof.own ptr_upd upd d0 ∗
    "Hdim0_rpcs" ∷ ([∗ list] p;o ∈ dim0_rpcs;rpcs, own_Client p o false))%I
    with "[] [$Hsl_rpcs $Hown_upd $Hdim0_rpcs]").
  { clear. iIntros "* %Hin". iIntros (ϕ) "!>". iIntros "H HΦ". iNamed "H".
    (* TODO: would be better if lemma just gave lookup. *)
    assert (dim0_rpcs !! (length done) = Some x) as Hlook0.
    { simplify_eq/=. by rewrite list_lookup_middle. }
    iDestruct (big_sepL2_lookup_1_some with "Hdim0_rpcs") as %[? Hlook1]; [exact Hlook0|].
    iDestruct (big_sepL2_lookup_acc with "Hdim0_rpcs") as "[Hown_cli Hclose]"; [done..|].
    wp_apply (wp_CallAdtrUpdate with "[$Hown_cli $Hown_upd]"). iIntros "*". iNamed 1.
    wp_apply wp_Assume. iIntros "_".
    iDestruct ("Hclose" with "Hown_cli") as "Hdim0_rpcs". iApply "HΦ". iFrame. }
  iIntros "[_ H]". iNamed "H". wp_pures. iApply "HΦ". by iFrame.
Qed.

Lemma wp_doAudits ptr_cli cli sl_addrs (addrs : list w64) sl_adtrPks dim0_adtrPks adtrPks :
  {{{
    "Hown_cli" ∷ client.Client.own ptr_cli cli ∗
    "#Hsl_addrs" ∷ own_slice_small sl_addrs uint64T DfracDiscarded addrs ∗
    "#Hsl_adtrPks" ∷ own_slice_small sl_adtrPks (slice.T byteT) DfracDiscarded dim0_adtrPks ∗
    "#Hdim0_adtrPks" ∷ ([∗ list] p;o ∈ dim0_adtrPks;adtrPks,
      own_slice_small p byteT DfracDiscarded o) ∗
    "%Hlen_addr_pk" ∷ ⌜ length addrs = length dim0_adtrPks ⌝
  }}}
  doAudits #ptr_cli (slice_val sl_addrs) (slice_val sl_adtrPks)
  {{{
    RET #();
    "Hown_cli" ∷ client.Client.own ptr_cli cli ∗
    "Haudits" ∷ ([∗ list] x ∈ adtrPks,
      ∀ γadtr,
      |==>
      "#His_pk" ∷ is_sig_pk x (sigpred γadtr) -∗
      "#His_audit" ∷ logical_audit cli.(Client.γ) γadtr
        cli.(Client.serv).(Server.vrf_pk) cli.(Client.next_epoch))
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
      ∀ γadtr,
      |==>
      "#His_pk" ∷ is_sig_pk x (sigpred γadtr) -∗
      "#His_audit" ∷ logical_audit cli.(Client.γ) γadtr
        cli.(Client.serv).(Server.vrf_pk) cli.(Client.next_epoch)))%I
    with "[$Hptr_idx $Hown_cli]").
  3: { iIntros "[H _]". iNamed "H".
    replace (uint.nat sl_addrs.(Slice.sz)) with (length adtrPks); [|lia].
    iEval (rewrite take_ge) in "Haudits". wp_pures. iApply "HΦ". by iFrame. }
  { iSplit; [|naive_solver]. word. }
  iIntros "!> * (H&Hptr_idx&%Hinb) HΦ". iNamed "H".
  list_elem addrs (uint.nat i) as addr.
  wp_load. wp_apply (wp_SliceGet with "[$Hsl_addrs]"); [done|]. iIntros "_".
  list_elem dim0_adtrPks (uint.nat i) as ptr_adtrPk.
  wp_load. wp_apply (wp_SliceGet with "[$Hsl_adtrPks]"); [done|]. iIntros "_".
  list_elem adtrPks (uint.nat i) as adtrPk.
  iDestruct (big_sepL2_lookup _ _ _ (uint.nat i) with "Hdim0_adtrPks") as "Hadtr_pk"; [done..|].
  wp_apply (wp_Client__Audit with "[$Hown_cli $Hadtr_pk]").
  iIntros (? err) "Haud". iNamed "Haud". iNamed "Hown_err".
  wp_loadField.
  destruct err.(ClientErr.Err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=".
  wp_pures. iApply "HΦ". iFrame.
  replace (uint.nat (word.add i (W64 1))) with (S $ uint.nat i); [|word].
  rewrite (take_S_r _ _ _ HadtrPk_lookup).
  iFrame. naive_solver.
Qed.

Lemma wp_updAdtrsAll (servAddr : w64) sl_adtrAddrs (adtrAddrs : list w64) :
  {{{
    "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded adtrAddrs
  }}}
  updAdtrsAll #servAddr (slice_val sl_adtrAddrs)
  {{{ RET #(); True }}}.
Proof. Admitted.

End proof.
