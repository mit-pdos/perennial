From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv lockservice bank.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_logic Require Import atomic_fupd.
From Perennial.program_proof.memkv Require Export common_proof memkv_clerk_proof lockservice_proof.

Section bank_proof.

Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !rpcG Σ ShardReplyC, !rpcregG Σ, !kvMapG Σ, mapG Σ u64 u64}.

Record bank_names := BankNames {
  bank_ls_names : gname;
  bank_ks_names : gname;
  bank_logBalGN : gname (* Logical balances of accounts; must match the physical balance by the time you give up the lock *)
}.

(*
Class bankG Σ := BankG {
  bank_ls :> lockserviceG Σ;
  bank_ks :> kvMapG Σ;
  bank_rpc :> rpcregG Σ;
  (* bank_logBalG :> mapG Σ u64 u64 *)
}.

Section bank_proof.
Context `{!heapGS Σ, !bankG Σ}.
*)

Implicit Types (γ : bank_names).

Context `{acc1:u64, acc2:u64, bal_total:u64}. (* Account names and total balance for bank *)

Definition kv_gn γ := γ.(bank_ks_names).
Definition log_gn γ := γ.(bank_logBalGN).

Definition bankPs γ := λ k, (∃ vd v, ⌜ has_encoding_Uint64 vd v ⌝ ∗ kvptsto (kv_gn γ) k vd ∗ k [[log_gn γ]]↦v)%I.

Definition N : namespace := nroot.@"grove_bank_of_boston".

Definition own_bank_clerk γ (bank_ck:loc) : iProp Σ :=
  ∃ (lck kck : loc),
  "%" ∷ ⌜acc1 ≠ acc2⌝ ∗
  "Hlck_own" ∷ own_LockClerk lck γ.(bank_ls_names) ∗
  "Hkck_own" ∷ own_MemKVClerk kck γ.(bank_ks_names) ∗

  "Hkck" ∷ bank_ck ↦[BankClerk :: "kvck"] #kck ∗
  "Hlck" ∷ bank_ck ↦[BankClerk :: "lck"] #lck ∗
  "Hacc1" ∷ bank_ck ↦[BankClerk :: "acc1"] #acc1 ∗
  "Hacc1" ∷ bank_ck ↦[BankClerk :: "acc2"] #acc2 ∗

  "Hacc1_is_lock" ∷ is_lock N γ.(bank_ls_names) acc1 (bankPs γ acc1) ∗
  "Hacc2_is_lock" ∷ is_lock N γ.(bank_ls_names) acc2 (bankPs γ acc2)
.

Definition bank_inv γ : iProp Σ :=
  ∃ (bal1 bal2:u64),
  "HlogBalCtx" ∷ map_ctx (log_gn γ) 1 ({[ acc1:=bal1 ]} ∪ {[ acc2:=bal2 ]}) ∗
  "%" ∷ ⌜(word.add bal1 bal2 = bal_total)%Z⌝
  .

Definition bankN := nroot .@ "bank".

Lemma acquire_two_spec (lck :loc) (ln1 ln2:u64) γ:
{{{
     own_LockClerk lck γ.(bank_ls_names) ∗
     is_lock N γ.(bank_ls_names) ln1 (bankPs γ acc1) ∗
     is_lock N γ.(bank_ls_names) ln2 (bankPs γ acc2)
}}}
  acquire_two #lck #ln1 #ln2
{{{
     RET #(); own_LockClerk lck γ.(bank_ls_names) ∗
     bankPs γ acc1 ∗
     bankPs γ acc2
}}}.
Proof.
  iIntros (Φ) "(Hlck & #Hln1_islock & #Hln2_islock) Hpost".
  wp_lam.
  wp_pures.
  destruct bool_decide; wp_pures.
  {
    wp_apply (wp_LockClerk__Lock with "[$Hlck $Hln1_islock]").
    iIntros "[Hlck HP1]".
    wp_pures.
    wp_apply (wp_LockClerk__Lock with "[$Hlck $Hln2_islock]").
    iIntros "[Hlck HP2]".
    wp_pures.
    iApply "Hpost". by iFrame.
  }
  {
    wp_apply (wp_LockClerk__Lock with "[$Hlck $Hln2_islock]").
    iIntros "[Hlck HP2]".
    wp_pures.
    wp_apply (wp_LockClerk__Lock with "[$Hlck $Hln1_islock]").
    iIntros "[Hlck HP1]".
    wp_pures.
    iApply "Hpost". by iFrame.
  }
Qed.

Lemma release_two_spec (lck :loc) (ln1 ln2:u64) γ:
{{{
     own_LockClerk lck γ.(bank_ls_names) ∗
     is_lock N γ.(bank_ls_names) ln1 (bankPs γ acc1) ∗
     is_lock N γ.(bank_ls_names) ln2 (bankPs γ acc2) ∗
     bankPs γ acc1 ∗
     bankPs γ acc2
}}}
  release_two #lck #ln1 #ln2
{{{
     RET #(); own_LockClerk lck γ.(bank_ls_names)
}}}.
Proof.
  iIntros (Φ) "(Hlck & #Hln1_islock & #Hln2_islock & HP1 & HP2) Hpost".
  wp_lam.
  wp_pures.
  destruct bool_decide; wp_pures.
  {
    wp_apply (wp_LockClerk__Unlock with "[$Hlck $Hln2_islock $HP2]").
    iIntros "Hlck".
    wp_pures.
    wp_apply (wp_LockClerk__Unlock with "[$Hlck $Hln1_islock $HP1]").
    iIntros "Hlck".
    wp_pures.
    iApply "Hpost"; by iFrame.
  }
  {
    wp_apply (wp_LockClerk__Unlock with "[$Hlck $Hln1_islock $HP1]").
    iIntros "Hlck".
    wp_pures.
    wp_apply (wp_LockClerk__Unlock with "[$Hlck $Hln2_islock $HP2]").
    iIntros "Hlck".
    wp_pures.
    iApply "Hpost"; by iFrame.
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
  wp_lam. wp_pures.
  wp_loadField.
  wp_loadField.
  wp_lam. (* We just use the helper function in-line *)
  wp_pures.
  wp_loadField.
  wp_apply (acquire_two_spec with "[$Hlck_own]"); first iFrame "#".
  iIntros "(Hlck_own & Hacc1_unlocked & Hacc2_unlocked)".
  iDestruct "Hacc1_unlocked" as (bytes1 bal1 Henc1) "(Hacc1_phys & Hacc1_log)".
  iDestruct "Hacc2_unlocked" as (bytes2 bal2 Henc2) "(Hacc2_phys & Hacc2_log)".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MemKVClerk__Get with "[$Hkck_own]").
  iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
  iExists _. iFrame "Hacc1_phys".
  iIntros "Hacc1_phys". iMod ("Hclo") as "_". iModIntro.
  iIntros (v_bal1_g qp) "(Hkck_own&Hbal1_get)".
  wp_apply (wp_DecodeUint64' with "[$Hbal1_get //]").
  wp_pures.
  destruct bool_decide eqn:HenoughBalance; wp_pures.
  - (* Safe to do the transfer *)
    wp_apply (wp_EncodeUint64).
    iIntros (v_bal1_g' bytes1') "(Hsl&%)".
    wp_loadField.
    iDestruct (is_slice_to_small with "Hsl") as "Hsl".
    iMod (readonly_alloc_1 with "Hsl") as "#Hsl".
    wp_apply (wp_MemKVClerk__Put with "[$Hkck_own]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc1_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkck_own".
    wp_pures.
    wp_loadField.

    wp_apply (wp_MemKVClerk__Get with "[$Hkck_own]").
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame "Hacc2_phys".
    iIntros "Hacc2_phys". iMod ("Hclo") as "_". iModIntro.
    iIntros (v_bal2_g qp') "(Hkck_own&Hbal2_get)".
    wp_apply (wp_DecodeUint64' with "[$Hbal2_get //]").
    wp_pures.

    wp_apply (wp_EncodeUint64).
    iIntros (v_bal2_g' bytes2') "(Hsl2&%)".

    wp_loadField.
    iDestruct (is_slice_to_small with "Hsl2") as "Hsl2".
    iMod (readonly_alloc_1 with "Hsl2") as "#Hsl2".
    wp_apply (wp_MemKVClerk__Put with "[$Hkck_own]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc2_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkck_own".
    wp_pures.
    wp_loadField.

    iApply fupd_wp.
    iInv bankN as ">HbankInv" "HbankInvClose".
    iNamed "HbankInv".
    iDestruct (map_valid with "[$] Hacc1_log") as "%Hval1".
    rewrite lookup_union_l lookup_singleton // in Hval1. inversion Hval1; subst.

    iDestruct (map_valid with "[$] Hacc2_log") as "%Hval2".
    rewrite lookup_union_r in Hval2; last first.
    { rewrite lookup_singleton_ne //. }
    rewrite lookup_singleton // in Hval2. inversion Hval2; subst.

    iMod (map_update acc1 _ (word.sub bal1 amount) with "HlogBalCtx Hacc1_log") as "[HlogBalCtx Hacc1_log]".
    iMod (map_update acc2 _ (word.add bal2 amount) with "HlogBalCtx Hacc2_log") as "[HlogBalCtx Hacc2_log]".
    iMod ("HbankInvClose" with "[HlogBalCtx]") as "_".
    { iNext. iExists _, _. iSplitL "HlogBalCtx".
      - rewrite insert_union_l. rewrite insert_singleton.
        rewrite insert_union_r; last by apply lookup_singleton_ne. rewrite insert_singleton.
        iFrame.
      - iPureIntro.
        admit. (* FIXME: add the necessary overflow checks and use them here... *)
        (* FIXME: but actually this should just be provable even without overflow by ring properties of u64 *)
    }
    iModIntro.
    wp_apply (release_two_spec with "[$Hlck_own Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; iExists _, _; iFrame; eauto. }
    iIntros "Hlck_own".
    iApply "Hpost".
    iExists _, _; iFrame "∗ # %".
  - (* Don't do the transfer *)
    wp_loadField. wp_apply (release_two_spec with "[$Hlck_own Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; iExists _, _; iFrame; eauto. }
    iIntros "Hlck_own".
    iApply "Hpost".
    iExists _, _; iFrame "∗ # %".
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
  wp_lam.
  repeat wp_loadField.

  wp_apply (acquire_two_spec with "[$Hlck_own]"); first iFrame "#".
  iIntros "(Hlck_own & Hacc1_unlocked & Hacc2_unlocked)".
  iDestruct "Hacc1_unlocked" as (bd1 bal1) "(%Henc1 & Hacc1_phys & Hacc1_log)".
  iDestruct "Hacc2_unlocked" as (bd2 bal2) "(%Henc2 & Hacc2_phys & Hacc2_log)".

  wp_pures.
  repeat wp_loadField.
  wp_apply (wp_MemKVClerk__Get with "[$Hkck_own]").
  iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
  iExists _. iFrame "Hacc1_phys".
  iIntros "Hacc1_phys". iMod ("Hclo") as "_". iModIntro.
  iIntros (v_bal1_g qp1) "(Hkck_own&Hbal1_get)".
  wp_apply (wp_DecodeUint64' with "[$Hbal1_get //]").

  wp_pures.
  repeat wp_loadField.
  wp_apply (wp_MemKVClerk__Get with "[$Hkck_own]").
  iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
  iExists _. iFrame "Hacc2_phys".
  iIntros "Hacc2_phys". iMod ("Hclo") as "_". iModIntro.
  iIntros (v_bal2_g qp2) "(Hkck_own&Hbal2_get)".
  wp_apply (wp_DecodeUint64' with "[$Hbal2_get //]").
  wp_pures.


  repeat wp_loadField.

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
  wp_apply (release_two_spec with "[$Hlck_own Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]"); first iFrame "#".
  { iSplitL "Hacc1_phys Hacc1_log"; iExists _, _; iFrame; eauto. }
  iIntros "Hlck_own".
  wp_pures.
  rewrite H2.
  iApply "Hpost".
  iExists _, _; iFrame "∗ # %"; eauto.
Qed.

End bank_proof.

