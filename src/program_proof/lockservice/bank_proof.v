From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof.lockservice Require Import lockservice_nocrash nondet lockservice_proof kv_proof.

Record bank_names := BankNames {
  bank_ls_names : lockservice_names;
  bank_ks_names : kvservice_names;
  bank_logBalGN : gname (* Logical balances of accounts; must match the physical balance by the time you give up the lock *)
}.

Class bankG Σ := BankG {
  bank_ls :> lockserviceG Σ;
  bank_ks :> kvserviceG Σ;
  (* bank_logBalG :> mapG Σ u64 u64 *)
}.

Section bank_proof.
Context `{!heapGS Σ, !bankG Σ}.

Implicit Types (γ : bank_names).

Context `{acc1:u64, acc2:u64, bal_total:u64}. (* Account names and total balance for bank *)

Definition kv_gn γ := γ.(bank_ks_names).(ks_kvMapGN).
Definition log_gn γ := γ.(bank_logBalGN).

Definition bankPs γ := λ k, (∃v, k [[kv_gn γ]]↦v ∗ k [[log_gn γ]]↦v)%I.

(* TODO: consider making is_*server part of own_*clerk *)
Definition own_bank_clerk γ (bank_ck:loc) : iProp Σ :=
  ∃ (lck kck ls_srv ks_srv:loc), 
  "%" ∷ ⌜acc1 ≠ acc2⌝ ∗
  "#Hls" ∷ is_lockserver γ.(bank_ls_names) ls_srv (Ps:=bankPs γ) ∗
  "#Hks" ∷ is_kvserver γ.(bank_ks_names) ks_srv ∗
  "Hlck_own" ∷ own_lockclerk γ.(bank_ls_names) lck ls_srv ∗
  "Hkck_own" ∷ own_kvclerk γ.(bank_ks_names) kck ks_srv ∗

  "Hkck" ∷ bank_ck ↦[BankClerk :: "kvck"] #kck ∗
  "Hlck" ∷ bank_ck ↦[BankClerk :: "lck"] #lck ∗
  "Hacc1" ∷ bank_ck ↦[BankClerk :: "acc1"] #acc1 ∗
  "Hacc1" ∷ bank_ck ↦[BankClerk :: "acc2"] #acc2 ∗

  "Hacc1_is_lock" ∷ lockservice_is_lock γ.(bank_ls_names) acc1 ∗
  "Hacc2_is_lock" ∷ lockservice_is_lock γ.(bank_ls_names) acc2
.

Definition bank_inv γ : iProp Σ :=
  ∃ (bal1 bal2:u64),
  "HlogBalCtx" ∷ map_ctx (log_gn γ) 1 ({[ acc1:=bal1 ]} ∪ {[ acc2:=bal2 ]}) ∗
  "%" ∷ ⌜(word.add bal1 bal2 = bal_total)%Z⌝
  .

Definition bankN := nroot .@ "bank".

Lemma acquire_two_spec (lck lsrv :loc) (ln1 ln2:u64) γ:
{{{
     is_lockserver γ.(bank_ls_names) lsrv (Ps:=bankPs γ) ∗
     lockservice_is_lock γ.(bank_ls_names) ln1 ∗
     lockservice_is_lock γ.(bank_ls_names) ln2 ∗
     own_lockclerk γ.(bank_ls_names) lck lsrv
}}}
  acquire_two #lck #ln1 #ln2
{{{
     RET #(); own_lockclerk γ.(bank_ls_names) lck lsrv ∗
     bankPs γ ln1 ∗
     bankPs γ ln2
}}}.
Proof.
  iIntros (Φ) "(#Hls & #Hln1_islock & #Hln2_islock & Hlck) Hpost".
  wp_rec.
  wp_pures.
  destruct bool_decide; wp_pures.
  {
    wp_apply (Clerk__Lock_spec with "[$Hlck $Hls $Hln1_islock]").
    iIntros "[Hlck HP1]".
    wp_pures.
    wp_apply (Clerk__Lock_spec with "[$Hlck $Hls $Hln2_islock]").
    iIntros "[Hlck HP2]".
    wp_pures.
    iApply "Hpost". iFrame.
  }
  {
    wp_apply (Clerk__Lock_spec with "[$Hlck $Hls $Hln2_islock]").
    iIntros "[Hlck HP2]".
    wp_pures.
    wp_apply (Clerk__Lock_spec with "[$Hlck $Hls $Hln1_islock]").
    iIntros "[Hlck HP1]".
    wp_pures.
    iApply "Hpost". iFrame.
  }
Qed.

Lemma release_two_spec (lck lsrv :loc) (ln1 ln2:u64) γ:
{{{
     is_lockserver γ.(bank_ls_names) lsrv (Ps:=bankPs γ) ∗
     lockservice_is_lock γ.(bank_ls_names) ln1 ∗
     lockservice_is_lock γ.(bank_ls_names) ln2 ∗
     bankPs γ ln1 ∗
     bankPs γ ln2 ∗
     own_lockclerk γ.(bank_ls_names) lck lsrv
}}}
  release_two #lck #ln1 #ln2
{{{
     RET #(); own_lockclerk γ.(bank_ls_names) lck lsrv
}}}.
Proof.
  iIntros (Φ) "(#Hls & #Hln1_islock & #Hln2_islock & HP1 & HP2 & Hlck) Hpost".
  wp_rec.
  wp_pures.
  destruct bool_decide; wp_pures.
  {
    wp_apply (Clerk__Unlock_spec with "[$Hlck $Hls $Hln2_islock $HP2]").
    iIntros (v) "[Hlck _]".
    wp_pures.
    wp_apply (Clerk__Unlock_spec with "[$Hlck $Hls $Hln1_islock $HP1]").
    iIntros (b) "[Hlck _]".
    wp_pures.
    iApply "Hpost"; iFrame.
  }
  {
    wp_apply (Clerk__Unlock_spec with "[$Hlck $Hls $Hln1_islock $HP1]").
    iIntros (v) "[Hlck _]".
    wp_pures.
    wp_apply (Clerk__Unlock_spec with "[$Hlck $Hls $Hln2_islock $HP2]").
    iIntros (b) "[Hlck _]".
    wp_pures.
    iApply "Hpost"; iFrame.
  }
Qed.

Lemma Bank__SimpleTransfer_spec (bck:loc) (amount:u64) γ :
{{{
     inv bankN (bank_inv γ) ∗
     own_bank_clerk γ bck
}}}
  BankClerk__SimpleTransfer #bck #amount
{{{
     RET #();
     own_bank_clerk γ bck
}}}.
Proof.
  iIntros (Φ) "[#Hbinv Hpre] Hpost".
  iNamed "Hpre".
  (* FIXME: iNamed not working correctly? *)
  iDestruct "Hpre" as "(Hacc1 & Hacc2 & #Hacc_is_lock)".
  iNamed "Hacc_is_lock".
  wp_rec. wp_pures.
  wp_loadField.
  wp_loadField.
  wp_rec. (* We just use the helper function in-line *)
  wp_pures.
  wp_loadField.
  wp_apply (acquire_two_spec with "[$Hlck_own $Hls]"); first iFrame "#".
  iIntros "(Hlck_own & Hacc1_unlocked & Hacc2_unlocked)".
  iDestruct "Hacc1_unlocked" as (bal1) "(Hacc1_phys & Hacc1_log)".
  iDestruct "Hacc2_unlocked" as (bal2) "(Hacc2_phys & Hacc2_log)".
  wp_pures.
  wp_loadField.
  wp_apply (KVClerk__Get_spec with "Hks [$Hkck_own Hacc1_phys]"); first done.
  iIntros (v_bal1_g) "Hbal1_get".
  iDestruct "Hbal1_get" as (->) "[Hkck_own Hacc1_phys]".
  wp_pures.
  destruct bool_decide eqn:HenoughBalance; wp_pures.
  - (* Safe to do the transfer *)
    wp_loadField. wp_apply (KVClerk__Put_spec with "Hks [$Hkck_own Hacc1_phys]"); first by eauto.
    iIntros "[Hkck_own Hacc1_phys]".
    wp_pures.
    wp_loadField.
    wp_apply (KVClerk__Get_spec with "Hks [$Hkck_own Hacc2_phys]"); first by eauto.
    iIntros (v_bal2_g) "Hbal2_get".
    iDestruct "Hbal2_get" as (->) "[Hkck_own Hacc2_phys]".
    wp_loadField.
    wp_apply (KVClerk__Put_spec with "Hks [$Hkck_own Hacc2_phys]"); first by eauto.
    iIntros "[Hkck_own Hacc2_phys]".
    wp_pures.
    iApply fupd_wp.
    iInv bankN as ">HbankInv" "HbankInvClose".
    iNamed "HbankInv".
    iMod (map_update acc1 _ (word.sub bal1 amount) with "HlogBalCtx Hacc1_log") as "[HlogBalCtx Hacc1_log]".
    iMod (map_update acc2 _ (word.add bal2 amount) with "HlogBalCtx Hacc2_log") as "[HlogBalCtx Hacc2_log]".
    iMod ("HbankInvClose" with "[HlogBalCtx]") as "_".
    { iNext. iExists _, _. iSplitL "HlogBalCtx".
      - rewrite insert_union_l. rewrite insert_singleton. 
        rewrite insert_union_r; last by apply lookup_singleton_ne. rewrite insert_singleton. 
        iFrame.
      - admit. (* FIXME: add the necessary overflow checks and use them here... *)
    }
    iModIntro.
    wp_loadField.
    wp_apply (release_two_spec with "[$Hlck_own $Hls Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; iExists _; iFrame. }
    iIntros "Hlck_own".
    iApply "Hpost".
    iExists _, _, _, _; iFrame "∗ # %".
  - (* Don't do the transfer *)
    wp_loadField. wp_apply (release_two_spec with "[$Hlck_own $Hls Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; iExists _; iFrame. }
    iIntros "Hlck_own".
    iApply "Hpost".
    iExists _, _, _, _; iFrame "∗ # %".
Admitted.

Lemma Bank__SimpleAudit_spec (bck:loc) γ :
{{{
     inv bankN (bank_inv γ) ∗
     own_bank_clerk γ bck
}}}
  BankClerk__SimpleAudit #bck
{{{
     RET #bal_total;
     own_bank_clerk γ bck
}}}.
Proof.
  iIntros (Φ) "[#Hbinv Hpre] Hpost".
  iNamed "Hpre".
  iDestruct "Hpre" as "(Hacc1 & Hacc2 & #Hacc_is_lock)".
  iNamed "Hacc_is_lock".
  wp_rec.
  repeat wp_loadField.

  wp_apply (acquire_two_spec with "[$Hlck_own $Hls]"); first iFrame "#".
  iIntros "(Hlck_own & Hacc1_unlocked & Hacc2_unlocked)".
  iDestruct "Hacc1_unlocked" as (bal1) "(Hacc1_phys & Hacc1_log)".
  iDestruct "Hacc2_unlocked" as (bal2) "(Hacc2_phys & Hacc2_log)".

  wp_pures.
  repeat wp_loadField.
  wp_apply (KVClerk__Get_spec with "Hks [$Hkck_own Hacc1_phys]"); first by eauto.
  iIntros (v_bal1_g) "Hbal1_get".
  iDestruct "Hbal1_get" as (->) "[Hkck_own Hacc1_phys]".

  repeat wp_loadField.
  wp_apply (KVClerk__Get_spec with "Hks [$Hkck_own Hacc2_phys]"); first by eauto.
  iIntros (v_bal2_g) "Hbal2_get".
  iDestruct "Hbal2_get" as (->) "[Hkck_own Hacc2_phys]".
  wp_pures.

  (* Use inv to know that the sum is total_bal *)
  iApply fupd_wp.
  iInv bankN as ">HbankInv" "HbankInvClose".
  iNamed "HbankInv".
  iDestruct (map_valid with "HlogBalCtx Hacc1_log") as %Hacc1_logphys.
  assert (bal0 = bal1) as ->.
  {
    erewrite lookup_union_Some_l in Hacc1_logphys; last by apply lookup_singleton.
    by injection Hacc1_logphys.
  }

  iDestruct (map_valid with "HlogBalCtx Hacc2_log") as %Hacc2_logphys.
  assert (bal2 = bal3) as ->.
  {
    erewrite lookup_union_Some_r in Hacc2_logphys; last by apply lookup_singleton.
    { by injection Hacc2_logphys. }
    rewrite map_disjoint_singleton_l.
    by apply lookup_singleton_ne.
  }
  iMod ("HbankInvClose" with "[HlogBalCtx]") as "_".
  { iNext. iExists _, _. iFrame "∗ %". }
  iModIntro.
  repeat wp_loadField.
  wp_apply (release_two_spec with "[$Hlck_own $Hls Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]"); first iFrame "#".
  { iSplitL "Hacc1_phys Hacc1_log"; iExists _; iFrame. }
  iIntros "Hlck_own".
  wp_pures.
  rewrite H0.
  iApply "Hpost".
  iExists _, _, _, _; iFrame "∗ # %".
Qed.

End bank_proof.
