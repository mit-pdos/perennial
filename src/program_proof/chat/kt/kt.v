From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat.kt Require Import shared kt_shim.
From Goose.github_com.mit_pdos.secure_chat Require Import kt.

From Perennial.program_proof.chat.kt Require Import shared shim.
From iris.unstable.base_logic Require Import mono_list.

Section common.
Context `{!heapGS Σ, !mono_listG UnameKey.t Σ}.

Lemma wp_injestNewLog ptr_currLog currLog sl_newLogB newLogB :
  {{{
    "HcurrLog" ∷ KeyLog.own ptr_currLog currLog ∗
    "HnewLogB" ∷ own_slice_small sl_newLogB byteT 1 newLogB
  }}}
  injestNewLog #ptr_currLog (slice_val sl_newLogB)
  {{{
    ptr_newLog newLog (err:u64), RET (#ptr_newLog, #err);
    "HcurrLog" ∷ KeyLog.own ptr_currLog currLog ∗
    "HnewLog" ∷ KeyLog.own ptr_newLog newLog ∗
    if bool_decide (#err = #0) then
      "%Henc" ∷ ⌜KeyLog.encodes newLogB newLog⌝ ∗
      "%Hprefix" ∷ ⌜currLog.(KeyLog.Log) `prefix_of` newLog.(KeyLog.Log)⌝
    else True%I
  }}}.
Proof. Admitted.

Definition lb_pred γ (log:KeyLog.t) : iProp Σ :=
  "Hlb_log" ∷ mono_list_lb_own γ log.(KeyLog.Log).

(* I think this implicitly assumes that for a particular list u8,
   there's only one log that could encode to it. *)
Definition lb_sig_pred γ : (list u8 → iProp Σ) :=
  λ logB, (∃ log, ⌜KeyLog.encodes logB log⌝ ∗ lb_pred γ log)%I.

End common.

Section keyServ.
Context `{!heapGS Σ}.

Lemma wp_keyServ_new :
  {{{ True }}}
  newKeyServ #()
  {{{ ptr_keyServ, RET #ptr_keyServ; True }}}.
Proof. Admitted.

Lemma wp_keyServ_start l (addr:u64) :
  {{{ True }}}
  keyServ__start #l #addr
  {{{ RET #(); True }}}.
Proof. Admitted.

End keyServ.

Section auditor.
Context `{!heapGS Σ, !mono_listG UnameKey.t Σ}.

Record adtrParam :=
  AdtrParam {
    γ : gname;
    Hon : bool
  }.

Definition lockR_adtr l param log : iProp Σ :=
  ∃ ptr_log sk,
  "Hlog" ∷ KeyLog.own ptr_log log ∗
  "Hauth_log" ∷ mono_list_auth_own param.(γ) 1 log.(KeyLog.Log) ∗
  "Hptr_log" ∷ l ↦[auditor :: "log"] #ptr_log ∗
  "Hsk" ∷ own_sk sk (lb_sig_pred param.(γ)) param.(Hon) ∗
  "Hptr_sk" ∷ l ↦[auditor :: "key"] #sk.

Definition is_adtr l param log : iProp Σ :=
  ∃ lk,
  "#HlkR" ∷ is_lock nroot #lk (lockR_adtr l param log) ∗
  "#Hlk" ∷ readonly (l ↦[auditor :: "mu"] #lk).

Lemma wp_auditor_new param sk :
  {{{
    "Hsk" ∷ own_sk sk (lb_sig_pred param.(γ)) param.(Hon) ∗
    "Hauth_log" ∷ mono_list_auth_own param.(γ) 1 []
  }}}
  newAuditor #sk
  {{{
    ptr_adtr, RET #ptr_adtr;
    "#Hadtr" ∷ is_adtr ptr_adtr param (KeyLog.mk [])
  }}}.
Proof. Admitted.

(* TODO: proving this will actually require proving true/true on all
   the handler funcs, but I'll save that for later. *)
Lemma wp_auditor_start l param log (addr:u64) :
  {{{
    "#Hadtr" ∷ is_adtr l param log
  }}}
  auditor__start #l #addr
  {{{ RET #(); True }}}.
Proof. Admitted.
End auditor.

Section keycli.
Context `{!heapGS Σ, !mono_listG UnameKey.t Σ}.

Definition own_keyCli l log adtrParams : iProp Σ :=
  ∃ ptr_log ptr_serv_rpc adtrs sl_adtrs vks sl_vks,
  "Hlog" ∷ KeyLog.own ptr_log log ∗
  "Hptr_log" ∷ l ↦[keyCli :: "log"] #ptr_log ∗
  "Hserv" ∷ own_rpc_cli ptr_serv_rpc ∗
  "Hptr_serv" ∷ l ↦[keyCli :: "serv"] #ptr_serv_rpc ∗
  "Hadtrs" ∷ ([∗ list] ptr_adtr ∈ adtrs, own_rpc_cli ptr_adtr) ∗
  "Hsl_adtrs" ∷ own_slice_small sl_adtrs ptrT 1 adtrs ∗
  "Hptr_adtrs" ∷ l ↦[keyCli :: "adtrs"] (slice_val sl_adtrs) ∗
  "#Hvks" ∷ ([∗ list] vk;param ∈ vks;adtrParams,
    is_vk vk (lb_sig_pred param.(γ)) param.(Hon)) ∗
  "Hsl_vks" ∷ own_slice_small sl_vks ptrT 1 vks ∗
  "Hptr_vks" ∷ l ↦[keyCli :: "adtrKeys"] (slice_val sl_vks).

Lemma wp_keyCli_new (serv:u64) sl_adtrAddrs (adtrAddrs:list u64) sl_vks vks adtrParams q1 q2 :
  {{{
    "HadtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T q1 adtrAddrs ∗
    "#Hvks" ∷ ([∗ list] vk;param ∈ vks;adtrParams,
      is_vk vk (lb_sig_pred param.(γ)) param.(Hon)) ∗
    "Hsl_vks" ∷ own_slice_small sl_vks ptrT q2 vks
  }}}
  newKeyCli #serv (slice_val sl_adtrAddrs) (slice_val sl_vks)
  {{{
    ptr_keyCli, RET #ptr_keyCli;
    "HadtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T q1 adtrAddrs ∗
    "HkeyCli" ∷ own_keyCli ptr_keyCli (KeyLog.mk []) adtrParams
  }}}.
Proof. Admitted.

Lemma wp_keyCli_reg ptr_keyCli ptr_entry entry log adtrParams :
  {{{
    "HkeyCli" ∷ own_keyCli ptr_keyCli log adtrParams ∗
    "Hentry" ∷ UnameKey.own ptr_entry entry
  }}}
  keyCli__register #ptr_keyCli #ptr_entry
  {{{
    (epoch err:u64) newLog, RET (#epoch, #err);
    "HkeyCli" ∷ own_keyCli ptr_keyCli newLog adtrParams ∗
    "Hentry" ∷ UnameKey.own ptr_entry entry ∗
    if bool_decide (#err = #0) then
      "%Hprefix" ∷ ⌜log.(KeyLog.Log) `prefix_of` newLog.(KeyLog.Log)⌝ ∗
      "%Helem_of" ∷ ⌜newLog.(KeyLog.Log) !! int.nat epoch = Some entry⌝
    else True%I
  }}}.
Proof. Admitted.

Lemma wp_keyCli_look ptr_keyCli (uname:u64) log adtrParams :
  {{{
    "HkeyCli" ∷ own_keyCli ptr_keyCli log adtrParams
  }}}
  keyCli__lookup #ptr_keyCli #uname
  {{{
    (epoch:u64) sl_key (key:list u8) (err:u64) newLog,
    RET (#epoch, slice_val sl_key, #err);
    "HkeyCli" ∷ own_keyCli ptr_keyCli newLog adtrParams ∗
    if bool_decide (#err = #0) then
      "Hkey" ∷ own_slice_small sl_key byteT 1 key ∗
      "%Hprefix" ∷ ⌜log.(KeyLog.Log) `prefix_of` newLog.(KeyLog.Log)⌝ ∗
      "%Helem_of" ∷ ⌜newLog.(KeyLog.Log) !! int.nat epoch = Some (UnameKey.mk uname key)⌝
    else True%I
  }}}.
Proof. Admitted.

Lemma wp_keyCli_audit ptr_keyCli (adtrId:u64) log adtrParams :
  {{{
    "HkeyCli" ∷ own_keyCli ptr_keyCli log adtrParams ∗
    "%HadtrId" ∷ ⌜int.nat adtrId < length adtrParams⌝
  }}}
  keyCli__audit #ptr_keyCli #adtrId
  {{{
    (epoch err:u64) param, RET (#epoch, #err);
    "HkeyCli" ∷ own_keyCli ptr_keyCli log adtrParams ∗
    "%Hparam" ∷ ⌜adtrParams !! int.nat adtrId = Some param⌝ ∗
    if bool_decide (#err = #0) && param.(Hon) then
      (* take is 1-idx'd, epoch is 0-idx'd. *)
      "#Hlb_log" ∷ mono_list_lb_own param.(γ) (take (int.nat epoch + 1) log.(KeyLog.Log))
    else True%I
  }}}.
Proof. Admitted.

End keycli.

Section tests.
Context `{!heapGS Σ, !mono_listG UnameKey.t Σ}.

Lemma wp_testAuditPass (servAddr:u64) sl_adtrAddrs (addr0 addr1 addr2:u64) :
  {{{
    "HadtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T 1 [addr0; addr1; addr2]
  }}}
  testAuditPass #servAddr (slice_val sl_adtrAddrs)
  {{{ RET #(); True }}}.
Proof using heapGS0 mono_listG0 Σ.
  iIntros (Φ) "H HΦ"; iNamed "H".
  rewrite /testAuditPass.

  (* Start key server. *)
  wp_apply wp_fork.
  {
    wp_apply wp_keyServ_new.
    iIntros (?) "_".
    by wp_apply wp_keyServ_start.
  }
  wp_apply wp_Sleep.

  (* Make auditor keys. *)
  iMod (mono_list_own_alloc []) as (γ0) "(Hauth0 & _)".
  iMod (mono_list_own_alloc []) as (γ1) "(Hauth1 & _)".
  iMod (mono_list_own_alloc []) as (γ2) "(Hauth2 & _)".
  wp_apply (wp_MakeKeys (lb_sig_pred γ0) false).
  { iPureIntro. apply _. }
  iIntros (badSk0 badVk0) "H"; iNamed "H";
    iRename "Hsk" into "HbadSk0"; iRename "Hvk" into "HbadVk0".
  wp_apply (wp_MakeKeys (lb_sig_pred γ1) true).
  { iPureIntro. apply _. }
  iIntros (goodSk0 goodVk0) "H"; iNamed "H";
    iRename "Hsk" into "HgoodSk0"; iRename "Hvk" into "HgoodVk0".
  wp_apply (wp_MakeKeys (lb_sig_pred γ2) false).
  { iPureIntro. apply _. }
  iIntros (badSk1 badVk1) "H"; iNamed "H";
    iRename "Hsk" into "HbadSk1"; iRename "Hvk" into "HbadVk1".

  wp_apply wp_ref_of_zero; [done|].
  iIntros (ptr_adtrVks) "Hptr_adtrVks".
  wp_load.
  wp_apply wp_SliceAppend_to_zero; [done|].
  iIntros (adtrVks') "HadtrVks'".
  wp_store.
  wp_load.
  wp_apply (wp_SliceAppend with "[$]").
  iIntros (adtrVks'') "HadtrVks''".
  wp_store.
  wp_load.
  wp_apply (wp_SliceAppend with "[$]").
  iIntros (adtrVks) "HadtrVks".
  wp_store.
  iDestruct (own_slice_to_small with "HadtrVks") as "HadtrVks".
  iSimpl in "HadtrVks".
  clear adtrVks' adtrVks''.

  (* Start auditors. *)
  iDestruct "HadtrAddrs" as "[HadtrAddrs3 [Haddrs0 [Haddrs1 Haddrs2]]]".
  pose (AdtrParam γ0 false) as param0.
  wp_apply (wp_fork with "[Hauth0 HbadSk0 Haddrs0]").
  {
    iIntros "!>".
    wp_apply (wp_auditor_new param0 with "[$]").
    iIntros (?) "H"; iNamed "H".
    wp_apply (wp_SliceGet with "[$Haddrs0]"); [done|].
    iIntros "_".
    by wp_apply (wp_auditor_start with "[$]").
  }
  pose (AdtrParam γ1 true) as param1.
  wp_apply (wp_fork with "[Hauth1 HgoodSk0 Haddrs1]").
  {
    iIntros "!>".
    wp_apply (wp_auditor_new param1 with "[$]").
    iIntros (?) "H"; iNamed "H".
    wp_apply (wp_SliceGet with "[$Haddrs1]"); [done|].
    iIntros "_".
    by wp_apply (wp_auditor_start with "[$]").
  }
  pose (AdtrParam γ2 false) as param2.
  wp_apply (wp_fork with "[Hauth2 HbadSk1 Haddrs2]").
  {
    iIntros "!>".
    wp_apply (wp_auditor_new param2 with "[$]").
    iIntros (?) "H"; iNamed "H".
    wp_apply (wp_SliceGet with "[$Haddrs2]"); [done|].
    iIntros "_".
    by wp_apply (wp_auditor_start with "[$]").
  }
  wp_apply wp_Sleep.

  (* Make keyCli's. *)
  remember ([badVk0; goodVk0; badVk1]) as vks.
  remember ([param0; param1; param2]) as params.
  iAssert ([∗ list] vk ; p ∈ vks ; params,
    is_vk vk (lb_sig_pred p.(kt.γ)) p.(kt.Hon))%I
    as "#His_vks"; [naive_solver|].
  iClear "HbadVk0 HgoodVk0 HbadVk1".
  iDestruct "HadtrVks" as "[HadtrVks0 [HadtrVks1 HadtrVks2]]".
  wp_load.
  wp_apply (wp_keyCli_new with "[$]").
  iIntros (cReg) "H"; iNamed "H"; iRename "HkeyCli" into "HcReg".
  wp_load.
  wp_apply (wp_keyCli_new with "[$]").
  iIntros (cLook0) "H"; iNamed "H"; iRename "HkeyCli" into "HcLook0".
  wp_load.
  wp_apply (wp_keyCli_new with "[$]").
  iIntros (cLook1) "H"; iNamed "H"; iRename "HkeyCli" into "HcLook1".

  (* Register a key. *)
  wp_apply wp_StringToBytes.
  iIntros (key0) "Hkey0".
  iDestruct (own_slice_to_small with "Hkey0") as "Hkey0".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (goodEntry) "HgoodEntry".
  iDestruct (struct_fields_split with "HgoodEntry") as "H".
  iNamed "H".
  wp_apply (wp_keyCli_reg with "[$HcReg Uname Key Hkey0]").
  {
    instantiate (1:=UnameKey.mk _ _).
    (* Note: iFrame could handle this without the rewrite, but it performs some weird
       unfolding that makes the context after the wp_apply verbose. *)
    rewrite /UnameKey.own /=.
    iFrame.
  }
  iIntros (epoch err0 newLog0) "H"; iNamed "H";
    iRename "HkeyCli" into "HcReg";
    iRename "Hentry" into "HgoodEntry".
  wp_apply wp_Assume.
  iIntros "_"; iClear (epoch err0) "H".

  (* Lookup that uname. *)
  wp_apply (wp_keyCli_look with "[$HcLook0]").
  iIntros (epoch0 sl_retKey0 retKey0 err1 newLog1) "H"; iNamed "H";
    iRename "HkeyCli" into "HcLook0".
  wp_apply wp_Assume.
  iIntros "%Herr".
  apply bool_decide_eq_true in Herr.
  rewrite Herr.
  iSimpl in "H".
  iNamed "H"; iRename "Hkey" into "HretKey0";
    move: {Herr err1 Hprefix} Helem_of => Helem_of1.

  wp_apply (wp_keyCli_look with "[$HcLook1]").
  iIntros (epoch1 sl_retKey1 retKey1 err2 newLog2) "H"; iNamed "H";
    iRename "HkeyCli" into "HcLook1".
  wp_apply wp_Assume.
  iIntros "%Herr".
  apply bool_decide_eq_true in Herr.
  rewrite Herr.
  iSimpl in "H".
  iNamed "H"; iRename "Hkey" into "HretKey1";
    move: {Herr err2 Hprefix} Helem_of => Helem_of2.

  (* Start auditor RPC clients. *)
  wp_apply (wp_SliceGet with "[$HadtrAddrs]"); [done|].
  iIntros "HadtrAddrs".
  wp_apply wp_rpc_MakeClient.
  iIntros (badAdtr0) "H"; iNamed "H"; iRename "Hurpc" into "HbadAdtr0".
  wp_apply (wp_SliceGet with "[$HadtrAddrs]"); [done|].
  iIntros "HadtrAddrs".
  wp_apply wp_rpc_MakeClient.
  iIntros (goodAdtr0) "H"; iNamed "H"; iRename "Hurpc" into "HgoodAdtr0".
  wp_apply (wp_SliceGet with "[$HadtrAddrs]"); [done|].
  iIntros "HadtrAddrs".
  wp_apply wp_rpc_MakeClient.
  iIntros (badAdtr1) "H"; iNamed "H"; iRename "Hurpc" into "HbadAdtr1".

  (* Update bad auditors with bad log. *)
  wp_apply wp_StringToBytes.
  iIntros (key1) "Hkey1".
  iDestruct (own_slice_to_small with "Hkey1") as "Hkey1".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (badEntry) "HbadEntry".
  iDestruct (struct_fields_split with "HbadEntry") as "H".
  iNamed "H".
  wp_apply KeyLog.wp_New.
  iIntros (ptr_badLog) "HbadLog".
  wp_apply (KeyLog.wp_Append with "[$HbadLog Uname Key Hkey1]").
  {
    instantiate (1:=UnameKey.mk _ _).
    rewrite /UnameKey.own /=.
    iFrame.
  }
  iIntros "H"; iNamed "H"; iRename "Harg" into "HbadLog".
  wp_apply (KeyLog.wp_Encode with "[$HbadLog]").
  iIntros (sl_badLogB badLogB) "H"; iNamed "H";
    iClear (badEntry ptr_badLog Henc key1) "Harg";
    iRename "HargB" into "HbadLogB".
  wp_apply wp_NewSlice.
  iIntros (emptyB) "_".
  wp_apply (wp_rpc_Call with "[$HbadAdtr0 $HbadLogB]").
  iIntros (err3 out) "H"; iNamed "H";
    iRename "Hrpc" into "HbadAdtr0";
    iRename "Hin" into "HbadLogB".
  wp_apply wp_Assume.
  iIntros "_"; iClear (err3 out) "H".
  wp_apply (wp_rpc_Call with "[$HbadAdtr1 $HbadLogB]").
  iIntros (err4 out) "H"; iNamed "H";
    iRename "Hrpc" into "HbadAdtr1".
  wp_apply wp_Assume.
  iIntros "_";
    iClear (err4 out sl_badLogB badLogB) "H Hin".

  (* Update good auditor with good log. *)
  wp_apply KeyLog.wp_New.
  iIntros (ptr_goodLog) "HgoodLog".
  wp_apply (KeyLog.wp_Append with "[$HgoodLog $HgoodEntry]").
  iIntros "H"; iNamed "H"; iRename "Harg" into "HgoodLog".
  wp_apply (KeyLog.wp_Encode with "[$HgoodLog]").
  iIntros (sl_goodLogB goodLogB) "H"; iNamed "H";
    iClear (goodEntry ptr_goodLog Henc) "Harg";
    iRename "HargB" into "HgoodLogB".
  wp_apply (wp_rpc_Call with "[$HgoodAdtr0 $HgoodLogB]").
  iIntros (err5 out) "H"; iNamed "H";
    iRename "Hrpc" into "HgoodAdtr0".
  wp_apply wp_Assume.
  iIntros "_";
    iClear (err5 out sl_goodLogB goodLogB emptyB) "H Hin".

  (* Run keyCli audits. *)
  wp_apply (wp_keyCli_audit with "[$HcLook0]"); [naive_solver|].
  iIntros (epoch err param) "H"; iNamed "H";
    iRename "HkeyCli" into "HcLook0";
    wp_pures;
    iClear (epoch err param Hparam) "H".
  wp_apply (wp_keyCli_audit with "[$HcLook0]"); [naive_solver|].
  iIntros (auditEpoch0 err6 param) "H"; iNamed "H";
    iRename "HkeyCli" into "HcLook0".
  wp_apply wp_Assume.
  iIntros "%Herr".
  apply bool_decide_eq_true in Herr.
  rewrite Herr.
  assert (int.nat 1%Z = 1) as H by word;
    rewrite H in Hparam;
    clear H.
  assert (param = param1) by naive_solver;
    subst param.
  iSimpl in "H"; iNamed "H";
    iRename "Hlb_log" into "Hlb_cLook0";
    clear err6 Herr Hparam.

  wp_apply (wp_keyCli_audit with "[$HcLook1]"); [naive_solver|].
  iIntros (epoch err param) "H"; iNamed "H";
    iRename "HkeyCli" into "HcLook1";
    wp_pures;
    iClear (epoch err param Hparam) "H".
  wp_apply (wp_keyCli_audit with "[$HcLook1]"); [naive_solver|].
  iIntros (auditEpoch1 err7 param) "H"; iNamed "H";
    iRename "HkeyCli" into "HcLook1".
  wp_apply wp_Assume.
  iIntros "%Herr".
  apply bool_decide_eq_true in Herr.
  rewrite Herr.
  assert (int.nat 1%Z = 1) as H by word;
    rewrite H in Hparam;
    clear H.
  assert (param = param1) by naive_solver;
    subst param.
  iSimpl in "H"; iNamed "H";
    iRename "Hlb_log" into "Hlb_cLook1";
    clear err7 Herr Hparam.

  (* Final assert. *)
  wp_apply (wp_and2 _ _ _ _ True%I); [by wp_pures..|].
  wp_if_destruct; move: Heqb => HifEq.
  2: by iApply "HΦ".
  move: HifEq => [HepochEq [Hepoch0Leq Hepoch1Leq]].
  wp_apply (wp_BytesEqual with "[$HretKey0 $HretKey1]").
  iIntros (keysEqb) "H"; iNamed "H";
    iRename "Hb0" into "HretKey0";
    iRename "Hb1" into "HretKey1";
    move: Heqb => HkeysEqb.
  (* Hard to touch the (take list) inside Hlb since we don't know
     the log len. Instead, try to reason about the lookup. *)
  iDestruct (mono_list_idx_own_get with "[$Hlb_cLook0]") as "Hidx0".
  {
    (* When we take some number of elements, if we take more
       than our lookup index, that reduces to a normal lookup. *)
    assert (int.nat epoch0 < int.nat auditEpoch0 + 1) as H by word.
    rewrite lookup_take; [apply Helem_of1|apply H].
  }
  iDestruct (mono_list_idx_own_get with "[$Hlb_cLook1]") as "Hidx1".
  {
    assert (int.nat epoch1 < int.nat auditEpoch1 + 1) as H by word.
    rewrite lookup_take; [apply Helem_of2|apply H].
  }
  (* TODO: not sure why word doesn't handle this. *)
  assert (epoch0 = epoch1) as H by naive_solver;
    iEval (rewrite H) in "Hidx0";
    clear H.
  iDestruct (mono_list_idx_agree with "Hidx0 Hidx1") as "%HkeysEq".
  wp_apply wp_Assert.
  1: destruct keysEqb; [done|naive_solver].
  wp_pures.
  by iApply "HΦ".
Qed.

End tests.
