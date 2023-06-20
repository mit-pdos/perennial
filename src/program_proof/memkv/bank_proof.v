From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv lockservice bank.
From Perennial.program_proof.memkv Require Export common_proof memkv_clerk_proof lockservice_proof.


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

Definition map_total (m : gmap u64 u64) : u64 :=
  map_fold (λ k v tot, word.add tot v) 0 m.

Add Ring u64ring : (word.ring_theory (word := u64_instance.u64)).

Lemma map_total_insert m k v :
  m !! k = None ->
  map_total (<[k := v]> m) = word.add (map_total m) v.
Proof.
  intro Hnone.
  rewrite /map_total map_fold_insert_L; eauto.
  intros; ring.
Qed.

Lemma map_total_insert_2 m k v :
  m !! k = Some v ->
  map_total m = word.add (map_total (delete k m)) v.
Proof.
  intro Hsome.
  erewrite <- (map_total_insert _ k).
  2: rewrite lookup_delete //.
  rewrite insert_delete //.
Qed.

Lemma map_total_empty :
  map_total ∅ = 0.
Proof.
  reflexivity.
Qed.

Lemma map_total_dom_empty m :
  dom m = ∅ ->
  map_total m = 0.
Proof.
  intros Hd.
  apply dom_empty_inv_L in Hd; subst.
  reflexivity.
Qed.

Lemma map_total_update : ∀ m k v v',
  m !! k = Some v ->
  map_total (<[k := v']> m) = word.add (word.sub (map_total m) v) v'.
Proof.
  induction m using map_ind.
  - intros k v v'. rewrite lookup_empty. congruence.
  - intros k v v' Hlookup.
    destruct (decide (k = i)); subst.
    + rewrite insert_insert.
      rewrite lookup_insert in Hlookup; inversion Hlookup; subst.
      rewrite map_total_insert //.
      rewrite map_total_insert //.
      ring_simplify.
      done.
    + rewrite insert_commute //.
      rewrite lookup_insert_ne // in Hlookup.
      rewrite (map_total_insert _ i).
      2: { rewrite lookup_insert_ne //. }
      rewrite (map_total_insert _ i) //.
      erewrite IHm; last by eauto.
      ring_simplify.
      done.
Qed.

Definition bank_inv γ (accts : gset u64) : iProp Σ :=
  ∃ (m:gmap u64 u64),
    "HlogBalCtx" ∷ map_ctx (log_gn γ) 1 m ∗
    "%" ∷ ⌜map_total m = bal_total⌝ ∗
    "%" ∷ ⌜dom m = accts⌝
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
   kvptsto γkv init_flag [U8 0] ∗ inv bankN (bank_inv γ {[acc1; acc2]}) ∗
   "#Hacc1_is_lock" ∷ is_lock lockN γlock acc1 (bankPs γ acc1) ∗
   "#Hacc2_is_lock" ∷ is_lock lockN γlock acc2 (bankPs γ acc2)).

End bank_defs.

Section bank_proof.
Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !erpcG Σ, !urpcregG Σ, !kvMapG Σ, mapG Σ u64 u64}.

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
  wp_apply (wp_LockClerk__Unlock with "[$Hlck $Hln1_islock $HP1]").
  iIntros "Hlck".
  wp_pures.
  wp_apply (wp_LockClerk__Unlock with "[$Hlck $Hln2_islock $HP2]").
  iIntros "Hlck".
  wp_pures.
  iApply "Hpost"; by iFrame.
Qed.

Add Ring u64ring : (word.ring_theory (word := u64_instance.u64)).

Lemma Bank__SimpleTransfer_spec (bck:loc) (amount:u64) γ accts :
{{{
     inv bankN (bank_inv γ accts) ∗
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
    iDestruct (own_slice_to_small with "Hsl") as "Hsl".
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
    iDestruct (own_slice_to_small with "Hsl2") as "Hsl2".
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
    iDestruct (map_valid with "[$] Hacc2_log") as "%Hval2".
    iMod (map_update acc1 _ (word.sub bal1 amount) with "HlogBalCtx Hacc1_log") as "[HlogBalCtx Hacc1_log]".
    iMod (map_update acc2 _ (word.add bal2 amount) with "HlogBalCtx Hacc2_log") as "[HlogBalCtx Hacc2_log]".
    iMod ("HbankInvClose" with "[HlogBalCtx]") as "_".
    { iNext. iExists _. iSplitL "HlogBalCtx"; first by iFrame.
      iSplit; iPureIntro.
      + erewrite map_total_update; last by rewrite lookup_insert_ne //.
        erewrite map_total_update; last by eauto.
        ring_simplify. eauto.
      + rewrite dom_insert_lookup_L.
        2: { rewrite lookup_insert_ne //. }
        rewrite dom_insert_lookup_L //.
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
     inv bankN (bank_inv γ {[ acc1; acc2 ]}) ∗
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
  iDestruct (map_valid with "HlogBalCtx Hacc2_log") as %Hacc2_logphys.
  iMod ("HbankInvClose" with "[HlogBalCtx]") as "_".
  { iNext. iExists _. iFrame "∗ %". }
  iModIntro.
  wp_apply (release_two_spec with "[$Hlck_own Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]"); first iFrame "#".
  { iSplitL "Hacc1_phys Hacc1_log"; iExists _, _; iFrame; eauto. }
  iIntros "Hlck_own".
  wp_pures.

  erewrite (map_total_insert_2 _ acc1) in H2; last by eauto.
  erewrite (map_total_insert_2 _ acc2) in H2; last by rewrite lookup_delete_ne //.
  rewrite map_total_dom_empty in H2.
  2: {
    rewrite dom_delete_L dom_delete_L H3. set_solver.
  }
  replace (word.add bal1 bal2) with (bal_total).
  2: {
    rewrite -H2 word.add_0_l. ring_simplify. done.
  }

  iApply "Hpost".
  iExists _, _; iFrame "∗ # %"; eauto.
Qed.

Lemma Bank__SimpleAudit_spec (bck:loc) γ :
{{{
     inv bankN (bank_inv γ {[acc1; acc2]}) ∗
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
      γ (ck:loc), RET #ck; own_bank_clerk γ ck ∗ inv bankN (bank_inv γ {[acc1; acc2]})
  }}}
.
Proof.
  iIntros (Φ) "#(Hcoord_lock&Hcoord_kv&#Hcm&Hinit_lock) HΦ".
  rewrite /MakeBankClerk.
  wp_lam.
  wp_pures.
  wp_apply wp_allocStruct; first val_ty.
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
    iDestruct (own_slice_to_small with "Hsl0") as "Hsl0".
    wp_apply (wp_BytesEqual with "[Hsl0 Hsl1]").
    { by iFrame. }
    iIntros "(Hsl1&Hsl0)".
    wp_pures.

    wp_apply (wp_EncodeUint64).
    iIntros (??) "(Hacc1_val_slice&%)".
    wp_loadField.
    iDestruct (own_slice_to_small with "Hacc1_val_slice") as "Hacc1_val_slice".
    iMod (readonly_alloc_1 with "Hacc1_val_slice") as "#Hacc1_val_Slice".
    wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc1_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkv".
    wp_pures.

    wp_apply (wp_EncodeUint64).
    iIntros (??) "(Hacc2_val_slice&%)".
    wp_loadField.
    iDestruct (own_slice_to_small with "Hacc2_val_slice") as "Hacc2_val_slice".
    iMod (readonly_alloc_1 with "Hacc2_val_slice") as "#Hacc2_val_Slice".
    wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc2_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkv".
    wp_pures.

    wp_apply (typed_slice.wp_NewSlice (V:=u8)).
    iIntros (?) "Hflag_val_slice".
    wp_loadField.
    iDestruct (own_slice_to_small with "Hflag_val_slice") as "Hflag_val_slice".
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
    iMod (inv_alloc bankN _ (bank_inv γ {[acc1; acc2]}) with "[Hmap_ctx]") as "#Hinv".
    { iNext. iExists _. iSplitL "Hmap_ctx".
      { rewrite /named. iFrame. }
      iPureIntro; split.
      { rewrite map_total_insert; last by rewrite lookup_insert_ne //.
        rewrite map_total_insert; last by eauto.
        rewrite map_total_empty. word. }
      { rewrite dom_insert_L dom_insert_L. set_solver. }
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
    iDestruct (own_slice_to_small with "Hsl0") as "Hsl0".
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

