From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv lockservice bank.
From Perennial.program_logic Require Import atomic_fupd.
From Perennial.program_proof.memkv Require Export common_proof rpc_lib memkv_clerk_proof lockservice_proof.


Record bank_names := BankNames {
  bank_ls_names : gname;
  bank_ks_names : gname;
  bank_logBalGN : gname (* Logical balances of accounts; must match the physical balance by the time you give up the lock *)
}.

Definition kv_gn γ := γ.(bank_ks_names).
Definition lk_gn γ := γ.(bank_ls_names).
Definition log_gn γ := γ.(bank_logBalGN).

Section bank_defs.

Context `{!invGS Σ, !kvMapG Σ, mapG Σ u64 u64}.

Definition bankPs γ := λ k, (∃ vd v, ⌜ has_encoding_Uint64 vd v ⌝ ∗ kvptsto (kv_gn γ) k vd ∗ k [[log_gn γ]]↦v)%I.

Definition bankN := nroot .@ "grove_bank_of_boston".
Definition lockN : namespace := nroot.@"grove_bank_of_boston_vault".

Definition bal_total : u64 := 1000.

Context (init_flag: u64) (acc1:u64) (acc2:u64). (* Account names for bank *)

Definition bank_inv γ : iProp Σ :=
  ∃ (bal1 bal2:u64),
  "HlogBalCtx" ∷ map_ctx (log_gn γ) 1 ({[ acc1:=bal1 ]} ∪ {[ acc2:=bal2 ]}) ∗
  "%" ∷ ⌜(word.add bal1 bal2 = bal_total)%Z⌝
  .

Definition init_lock_inv γlock γkv : iProp Σ :=
  (* Uninit case *)
  (kvptsto γkv init_flag [] ∗
   kvptsto γkv acc1 [] ∗ kvptsto γkv acc2 [] ∗
   kvptsto γlock acc1 [] ∗ kvptsto γlock acc2 []
  ) ∨
  (* Already init case *)
  (∃ γlog,
   let γ := {| bank_ls_names := γlock; bank_ks_names := γkv; bank_logBalGN := γlog |} in
   kvptsto γkv init_flag [U8 0] ∗ inv bankN (bank_inv γ) ∗
   "#Hacc1_is_lock" ∷ is_lock lockN γlock acc1 (bankPs γ acc1) ∗
   "#Hacc2_is_lock" ∷ is_lock lockN γlock acc2 (bankPs γ acc2)).

End bank_defs.

Section bank_proof.
Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !rpcG Σ ShardReplyC, !rpcregG Σ, !kvMapG Σ, mapG Σ u64 u64}.

Context (init_flag: u64) (acc1:u64) (acc2:u64). (* Account names for bank *)


Definition own_bank_clerk γ (bank_ck:loc) : iProp Σ :=
  ∃ (lck kck : loc),
  "%" ∷ ⌜acc1 ≠ acc2⌝ ∗
  "Hlck_own" ∷ own_LockClerk lck γ.(bank_ls_names) ∗
  "Hkck_own" ∷ own_SeqKVClerk kck γ.(bank_ks_names) ∗

  "Hkck" ∷ bank_ck ↦[BankClerk :: "kvck"] #kck ∗
  "Hlck" ∷ bank_ck ↦[BankClerk :: "lck"] #lck ∗
  "Hacc1" ∷ bank_ck ↦[BankClerk :: "acc1"] #acc1 ∗
  "Hacc1" ∷ bank_ck ↦[BankClerk :: "acc2"] #acc2 ∗

  "Hacc1_is_lock" ∷ is_lock lockN γ.(bank_ls_names) acc1 (bankPs γ acc1) ∗
  "Hacc2_is_lock" ∷ is_lock lockN γ.(bank_ls_names) acc2 (bankPs γ acc2)
.


Lemma acquire_two_spec (lck :loc) (ln1 ln2:u64) γ:
{{{
     own_LockClerk lck γ.(bank_ls_names) ∗
     is_lock lockN γ.(bank_ls_names) ln1 (bankPs γ acc1) ∗
     is_lock lockN γ.(bank_ls_names) ln2 (bankPs γ acc2)
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
     is_lock lockN γ.(bank_ls_names) ln1 (bankPs γ acc1) ∗
     is_lock lockN γ.(bank_ls_names) ln2 (bankPs γ acc2) ∗
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

Add Ring u64ring : (word.ring_theory (word := u64_instance.u64)).

Lemma Bank__SimpleTransfer_spec (bck:loc) (amount:u64) γ :
{{{
     inv bankN (bank_inv acc1 acc2 γ) ∗
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
  wp_apply (wp_SeqKVClerk__Get with "[$Hkck_own]").
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
    wp_apply (wp_SeqKVClerk__Put with "[$Hkck_own]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc1_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkck_own".
    wp_pures.
    wp_loadField.

    wp_apply (wp_SeqKVClerk__Get with "[$Hkck_own]").
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
    wp_apply (wp_SeqKVClerk__Put with "[$Hkck_own]"); first by eauto.
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
      - iPureIntro. ring_simplify. eauto.
    }
    iModIntro.
    wp_apply (release_two_spec with "[$Hlck_own Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; iExists _, _; iFrame; eauto. }
    iIntros "Hlck_own".
    wp_pures. iApply "Hpost".
    iExists _, _; by iFrame "∗ # %".
  - (* Don't do the transfer *)
    wp_loadField. wp_apply (release_two_spec with "[$Hlck_own Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; iExists _, _; iFrame; eauto. }
    iIntros "Hlck_own".
    wp_pures. iApply "Hpost".
    iExists _, _; by iFrame "∗ # %".
Qed.

Lemma Bank__get_total_spec (bck:loc) γ :
{{{
     inv bankN (bank_inv acc1 acc2 γ) ∗
     own_bank_clerk γ bck
}}}
  BankClerk__get_total #bck
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
  wp_apply (wp_SeqKVClerk__Get with "[$Hkck_own]").
  iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
  iExists _. iFrame "Hacc1_phys".
  iIntros "Hacc1_phys". iMod ("Hclo") as "_". iModIntro.
  iIntros (v_bal1_g qp1) "(Hkck_own&Hbal1_get)".
  wp_apply (wp_DecodeUint64' with "[$Hbal1_get //]").

  wp_pures.
  repeat wp_loadField.
  wp_apply (wp_SeqKVClerk__Get with "[$Hkck_own]").
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

Lemma Bank__SimpleAudit_spec (bck:loc) γ :
{{{
     inv bankN (bank_inv acc1 acc2 γ) ∗
     own_bank_clerk γ bck
}}}
  BankClerk__SimpleAudit #bck
{{{
     RET #(); True
}}}.
Proof.
  iIntros (Φ) "[#Hbinv Hpre] Hpost".
  wp_lam.
  wp_pures.
  iCombine "Hpre Hpost" as "H".
  wp_apply (wp_forBreak' with "[-]").
  { iExact "H". }
  iModIntro. iIntros "[Hpre Hpost]".
  wp_pures.
  wp_apply (Bank__get_total_spec with "[$]").
  iIntros "Hpre". rewrite /bal_total.
  wp_pures.
  iModIntro. iLeft. iFrame. eauto.
Qed.

Lemma wp_MakeBankClerk (lockhost kvhost : u64) cm γ1 γ2 cid  (Hneq: acc1 ≠ acc2) :
  {{{
       is_coord_server lockhost γ1 ∗
       is_coord_server kvhost γ2 ∗
       is_ConnMan cm ∗
       is_lock lockN (γ1.(coord_kv_gn)) init_flag
         (init_lock_inv init_flag acc1 acc2 γ1.(coord_kv_gn) γ2.(coord_kv_gn))
  }}}
    MakeBankClerk #lockhost #kvhost #cm #init_flag #acc1 #acc2 #cid
  {{{
      γ (ck:loc), RET #ck; own_bank_clerk γ ck ∗ inv bankN (bank_inv acc1 acc2 γ)
  }}}
.
Proof.
  iIntros (Φ) "#(Hcoord_lock&Hcoord_kv&#Hcm&Hinit_lock) HΦ".
  rewrite /MakeBankClerk.
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_MakeLockClerk with "[$Hcoord_lock $Hcm]").
  iIntros (lkCk) "Hlk".
  wp_storeField.

  wp_apply (wp_MakeSeqKVClerk with "[$Hcoord_kv $Hcm]").
  iIntros (kvCk) "Hkv".
  do 3 wp_storeField.

  wp_loadField.
  wp_apply (wp_LockClerk__Lock with "[$]").
  iIntros "(Hlk&Hinit)".

  wp_pures.
  wp_apply (typed_slice.wp_NewSlice (V:=u8)).
  iIntros (s0) "Hsl0".
  wp_loadField.
  wp_apply (wp_SeqKVClerk__Get with "[$Hkv]").
  iDestruct "Hinit" as "[Huninit|Hinit]".
  - iDestruct "Huninit" as "(Hflag&Hacc1&Hacc2&Hacc_lk1&Hacc_lk2)".
    iApply (fupd_mask_weaken ∅); first by set_solver+. iIntros "Hclo'".
    iModIntro. iExists _. iFrame. iIntros "Hflag".
    iMod "Hclo'" as "_". iModIntro.
    iIntros (val_sl_flag q). iIntros "(Hkv&Hsl1)".
    iDestruct (is_slice_to_small with "Hsl0") as "Hsl0".
    wp_apply (wp_BytesEqual with "[Hsl0 Hsl1]").
    { by iFrame. }
    iIntros "(Hsl1&Hsl0)".
    wp_pures.

    wp_apply (wp_EncodeUint64).
    iIntros (??) "(Hacc1_val_slice&%)".
    wp_loadField.
    iDestruct (is_slice_to_small with "Hacc1_val_slice") as "Hacc1_val_slice".
    iMod (readonly_alloc_1 with "Hacc1_val_slice") as "#Hacc1_val_Slice".
    wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc1_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkv".
    wp_pures.

    wp_apply (wp_EncodeUint64).
    iIntros (??) "(Hacc2_val_slice&%)".
    wp_loadField.
    iDestruct (is_slice_to_small with "Hacc2_val_slice") as "Hacc2_val_slice".
    iMod (readonly_alloc_1 with "Hacc2_val_slice") as "#Hacc2_val_Slice".
    wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc2_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkv".
    wp_pures.

    wp_apply (typed_slice.wp_NewSlice (V:=u8)).
    iIntros (?) "Hflag_val_slice".
    wp_loadField.
    iDestruct (is_slice_to_small with "Hflag_val_slice") as "Hflag_val_slice".
    iMod (readonly_alloc_1 with "Hflag_val_slice") as "#Hflag_val_Slice".
    wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hflag_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkv".
    wp_pures.

    wp_loadField.
    iMod (map_init (∅ : gmap u64 u64)) as (γlog) "Hmap_ctx".
    iMod (map_alloc acc2 (U64 0) with "[$]") as "(Hmap_ctx&Hacc2)".
    { rewrite lookup_empty //. }
    iMod (map_alloc acc1 bal_total with "[$]") as "(Hmap_ctx&Hacc1)".
    { rewrite lookup_insert_ne //. }
    set γ := {| bank_ls_names := γ1.(coord_kv_gn);
                bank_ks_names := γ2.(coord_kv_gn);
                bank_logBalGN := γlog |}.
    iMod (lock_alloc lockN _ _ acc1 (bankPs γ acc1) with "[$] [Hacc1_phys Hacc1]") as "#Hlk1".
    { iExists _, _. by iFrame. }
    iMod (lock_alloc lockN _ _ acc2 (bankPs γ acc2) with "[$] [Hacc2_phys Hacc2]") as "#Hlk2".
    { iExists _, _. by iFrame. }
    iMod (inv_alloc bankN _ (bank_inv acc1 acc2 γ) with "[Hmap_ctx]") as "#Hinv".
    { iNext. iExists _, _. iSplitL "Hmap_ctx".
      { rewrite /named. iExactEq "Hmap_ctx". simpl.
        rewrite insert_union_singleton_l.
        rewrite insert_empty //=. }
      eauto.
    }
    wp_apply (wp_LockClerk__Unlock with "[$Hlk $Hinit_lock Hflag_phys]").
    { iRight. iExists γlog. iFrame "#". iFrame "Hflag_phys". }
    iIntros "H". wp_pures. iApply "HΦ". iModIntro. iFrame "Hinv".
    iExists _, _. iFrame. eauto.
  - iDestruct "Hinit" as (γlog) "(Hflag&#Hinv&H)". iNamed "H".
    iApply (fupd_mask_weaken ∅); first by set_solver+. iIntros "Hclo'".
    iModIntro. iExists _. iFrame. iIntros "Hflag".
    iMod "Hclo'" as "_". iModIntro.
    iIntros (val_sl_flag q). iIntros "(Hkv&Hsl1)".
    iDestruct (is_slice_to_small with "Hsl0") as "Hsl0".
    wp_apply (wp_BytesEqual with "[Hsl0 Hsl1]").
    { by iFrame. }
    iIntros "(Hsl1&Hsl0)".
    wp_pures.
    wp_loadField.
    wp_apply (wp_LockClerk__Unlock with "[$Hlk $Hinit_lock Hflag]").
    { iRight. iExists γlog. iFrame "#". eauto. }
    iIntros "H". wp_pures. iApply "HΦ". iModIntro. iFrame "Hinv".
    iExists _, _. iFrame. eauto.
Qed.

End bank_proof.

