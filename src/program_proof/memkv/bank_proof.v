From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv.memkv Require Import lockservice bank.
From Perennial.program_proof.memkv Require Export common_proof memkv_clerk_proof lockservice_proof.


Record bank_names := BankNames {
  bank_ls_names : gname;
  bank_ks_names : gname;
  bank_logBalGN : gname (* Logical balances of accounts; must match the physical balance by the time you give up the lock *)
}.

Definition kv_gn γ := γ.(bank_ks_names).
Definition lk_gn γ := γ.(bank_ls_names).
Definition log_gn γ := γ.(bank_logBalGN).

Add Ring u64ring : (word.ring_theory (word := w64_instance.w64)).


Section bank_defs.

Context `{!invGS Σ, !kvMapG Σ, mapG Σ u64 u64}.

Definition bankPs γ := λ k, (∃ vd v, ⌜ has_encoding_Uint64 vd v ⌝ ∗ kvptsto (kv_gn γ) k vd ∗ k [[log_gn γ]]↦v)%I.

Definition bankN := nroot .@ "grove_bank_of_boston".
Definition lockN : namespace := nroot.@"grove_bank_of_boston_vault".

Definition bal_total : u64 := 1000.

Context (init_flag: u64). (* Account names for bank *)

Definition map_total (m : gmap u64 u64) : u64 :=
  map_fold (λ k v tot, word.add tot v) 0 m.

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

Lemma map_total_zero m :
  map_Forall (λ _ x : u64, x = 0) m ->
  map_total m = 0.
Proof.
  induction m using map_ind.
  - intros Hz. reflexivity.
  - intros Hz. rewrite map_total_insert; last by eauto.
    apply map_Forall_insert in Hz; last by eauto.
    destruct Hz as [Hx Hz]; subst.
    rewrite IHm; last by eauto.
    done.
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

Definition init_lock_inv γlock γkv accts : iProp Σ :=
  (* Uninit case *)
  (kvptsto γkv init_flag [] ∗
   [∗ set] acc ∈ accts, kvptsto γkv acc [] ∗ kvptsto γlock acc []
  ) ∨
  (* Already init case *)
  (∃ γlog,
   let γ := {| bank_ls_names := γlock; bank_ks_names := γkv; bank_logBalGN := γlog |} in
   kvptsto γkv init_flag [W8 0] ∗ inv bankN (bank_inv γ accts) ∗
    [∗ set] acc ∈ accts, is_lock lockN γlock acc (bankPs γ acc)).

End bank_defs.

Section bank_proof.
Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !erpcG Σ, !urpcregG Σ, !kvMapG Σ, mapG Σ u64 u64}.

Context (init_flag: u64). (* Account names for bank *)


Definition own_bank_clerk γ (bank_ck:loc) (accts : gset u64) : iProp Σ :=
  ∃ (lck kck : loc) (accts_s : Slice.t) (accts_l : list u64),
  "%" ∷ ⌜Permutation (elements accts) (accts_l)⌝ ∗
  "Hlck_own" ∷ own_LockClerk lck γ.(bank_ls_names) ∗
  "Hkck_own" ∷ own_SeqKVClerk kck γ.(bank_ks_names) ∗

  "Hkck" ∷ bank_ck ↦[BankClerk :: "kvck"] #kck ∗
  "Hlck" ∷ bank_ck ↦[BankClerk :: "lck"] #lck ∗
  "Haccts" ∷ bank_ck ↦[BankClerk :: "accts"] (slice_val accts_s) ∗
  "Haccts_slice" ∷ own_slice_small accts_s uint64T (DfracOwn 1) accts_l ∗

  "#Haccts_is_lock" ∷ [∗ list] acc ∈ accts_l, is_lock lockN γ.(bank_ls_names) acc (bankPs γ acc)
.


Lemma acquire_two_spec (lck :loc) (ln1 ln2:u64) γ:
{{{
     own_LockClerk lck γ.(bank_ls_names) ∗
     is_lock lockN γ.(bank_ls_names) ln1 (bankPs γ ln1) ∗
     is_lock lockN γ.(bank_ls_names) ln2 (bankPs γ ln2)
}}}
  acquire_two #lck #ln1 #ln2
{{{
     RET #(); own_LockClerk lck γ.(bank_ls_names) ∗
     bankPs γ ln1 ∗
     bankPs γ ln2
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
     is_lock lockN γ.(bank_ls_names) ln1 (bankPs γ ln1) ∗
     is_lock lockN γ.(bank_ls_names) ln2 (bankPs γ ln2) ∗
     bankPs γ ln1 ∗
     bankPs γ ln2
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

Lemma Bank__transfer_internal_spec (bck:loc) src dst (amount:u64) γ accts :
{{{
     inv bankN (bank_inv γ accts) ∗
     own_bank_clerk γ bck accts ∗
     is_lock lockN γ.(bank_ls_names) src (bankPs γ src) ∗
     is_lock lockN γ.(bank_ls_names) dst (bankPs γ dst) ∗
     ⌜src ≠ dst⌝
}}}
  BankClerk__transfer_internal #bck #src #dst #amount
{{{
     RET #();
     own_bank_clerk γ bck accts
}}}.
Proof.
  iIntros (Φ) "(#Hbinv & Hpre & #Hsrc & #Hdst & %) Hpost".
  iNamed "Hpre".
  wp_lam. wp_pures.
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
    iMod (own_slice_small_persist with "Hsl") as "#Hsl".
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
    iMod (own_slice_small_persist with "Hsl2") as "#Hsl2".
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
    iMod (map_update src _ (word.sub bal1 amount) with "HlogBalCtx Hacc1_log") as "[HlogBalCtx Hacc1_log]".
    iMod (map_update dst _ (word.add bal2 amount) with "HlogBalCtx Hacc2_log") as "[HlogBalCtx Hacc2_log]".
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
    iExists _, _, _, _; by iFrame "∗ # %".
  - (* Don't do the transfer *)
    wp_loadField. wp_apply (release_two_spec with "[$Hlck_own Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; iExists _, _; iFrame; eauto. }
    iIntros "Hlck_own".
    wp_pures. iApply "Hpost".
    iExists _, _, _, _; by iFrame "∗ # %".
Qed.

Lemma Bank__SimpleTransfer_spec (bck:loc) γ accts :
{{{
     inv bankN (bank_inv γ accts) ∗
     own_bank_clerk γ bck accts
}}}
  BankClerk__SimpleTransfer #bck
{{{
     RET #();
     own_bank_clerk γ bck accts
}}}.
Proof.
  iIntros (Φ) "[#Hbinv Hpre] Hpost".
  wp_call.
  wp_forBreak_cond.
  wp_pures.
  wp_apply wp_RandomUint64. iIntros (src) "_".
  wp_apply wp_RandomUint64. iIntros (dst) "_".
  wp_apply wp_RandomUint64. iIntros (amount) "_".

  iNamed "Hpre".

  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  destruct (bool_decide (uint.Z src < uint.Z accts_s.(Slice.sz))) eqn:Hsrc.
  2: {
    wp_pures. iModIntro. iLeft. by iFrame "Hkck_own ∗#%".
  }

  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  destruct (bool_decide (uint.Z dst < uint.Z accts_s.(Slice.sz))) eqn:Hdst.
  2: {
    wp_pures. iModIntro. iLeft. by iFrame "Hkck_own ∗#%".
  }

  wp_if_destruct.
  2: {
    wp_pures. iModIntro. iLeft. by iFrame "Hkck_own ∗#%".
  }

  iDestruct (own_slice_small_sz with "Haccts_slice") as %Hslicelen.

  destruct (list_lookup_lt _ accts_l (uint.nat src)) as (asrc & Hasrc); first by word.
  destruct (list_lookup_lt _ accts_l (uint.nat dst)) as (adst & Hadst); first by word.

  wp_loadField.
  wp_apply (wp_SliceGet with "[$Haccts_slice]"); first by eauto.
  iIntros "Haccts_slice".

  wp_loadField.
  wp_apply (wp_SliceGet with "[$Haccts_slice]"); first by eauto.
  iIntros "Haccts_slice".

  iDestruct (big_sepL_lookup _ _ _ asrc with "Haccts_is_lock") as "#Hasrc_is_lock"; first by eauto.
  iDestruct (big_sepL_lookup _ _ _ adst with "Haccts_is_lock") as "#Hadst_is_lock"; first by eauto.

  wp_apply (Bank__transfer_internal_spec with "[-Hpost]").
  { iFrame "#". iSplitL.
    - iFrame "Hkck_own ∗%#".
    - iPureIntro.
      intro Hc; subst.
      assert (NoDup accts_l) as Hnodup.
      { rewrite -H1. apply NoDup_elements. }
      epose proof (NoDup_lookup _ _ _ _ Hnodup Hasrc Hadst).
      apply Heqb. f_equal. f_equal. word.
  }

  iIntros "Hpre".
  wp_pures.
  iModIntro.
  iLeft.
  iFrame. done.
Qed.

Lemma Bank__get_total_spec (bck:loc) γ accts :
{{{
     inv bankN (bank_inv γ accts) ∗
     own_bank_clerk γ bck accts
}}}
  BankClerk__get_total #bck
{{{
     RET #bal_total;
     own_bank_clerk γ bck accts
}}}.
Proof.
  iIntros (Φ) "[#Hbinv Hpre] Hpost".
  wp_call.
  wp_apply wp_ref_of_zero; first by done.
  iIntros (sum) "Hsum".

  iNamed "Hpre".
  wp_loadField.
  wp_apply (wp_forSlicePrefix (λ done todo,
    ∃ locked,
      "Hlck" ∷ bck ↦[BankClerk :: "lck"] #lck ∗
      "Hlck_own" ∷ own_LockClerk lck γ.(bank_ls_names) ∗
      "Hkck" ∷ bck ↦[BankClerk :: "kvck"] #kck ∗
      "Hkck_own" ∷ own_SeqKVClerk kck γ.(bank_ks_names) ∗
      "Hsum" ∷ sum ↦[uint64T] #(map_total locked) ∗
      "%Hlocked_dom" ∷ ⌜Permutation (elements (dom locked)) done⌝ ∗
      "Hml" ∷ [∗ map] acc ↦ bal ∈ locked,
        is_lock lockN γ.(bank_ls_names) acc (bankPs γ acc) ∗
        (∃ (vd : list u8), ⌜has_encoding_Uint64 vd bal⌝ ∗ kvptsto (kv_gn γ) acc vd ∗ acc [[log_gn γ]]↦ bal))%I
    with "[] [$Haccts_slice Hsum $Hlck $Hlck_own $Hkck $Hkck_own]").
  2: {
    iExists ∅. rewrite map_total_empty. iFrame.
    iSplitR; first done.
    iApply big_sepM_empty.
    done.
  }

  {
    iIntros (i x done todo) "%".
    iIntros (Ψ). iModIntro. iIntros "Hpre HΨ".
    iNamed "Hpre".

    wp_loadField.
    iDestruct (big_sepL_elem_of _ _ x with "Haccts_is_lock") as "#Hx_is_lock".
    { rewrite -H2. set_solver. }
    wp_apply (wp_LockClerk__Lock with "[$Hlck_own $Hx_is_lock]").
    iIntros "[Hlck_own Hx]".
    iDestruct "Hx" as (x_vd x_bal) "[%Hx_enc [Hx_kv Hx_log]]".

    wp_load.
    wp_loadField.
    wp_apply (wp_SeqKVClerk__Get with "[$Hkck_own]").

    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame "Hx_kv".
    iIntros "Hx_kv". iMod ("Hclo") as "_". iModIntro.
    iIntros (v_bal_x_g qp1) "(Hkck_own&Hbal_x_get)".
    wp_apply (wp_DecodeUint64' with "[$Hbal_x_get //]").

    wp_pures.
    wp_store.
    iModIntro.
    iApply "HΨ".
    iExists (<[x := x_bal]> locked).
    iFrame.

    destruct (decide (x ∈ dom locked)).
    {
      rewrite -H2 in H1.
      rewrite -Hlocked_dom in H1.
      exfalso.
      assert (NoDup (elements (dom locked) ++ x :: todo)) as Hnodup.
      { rewrite -H1. apply NoDup_elements. }
      apply NoDup_app in Hnodup.
      destruct Hnodup as (_ & Hnodup & _).
      specialize (Hnodup x).
      apply Hnodup; last by econstructor.
      apply elem_of_elements. eauto.
    }

    assert (locked !! x = None) as Hnone.
    { apply not_elem_of_dom_1. eauto. }

    rewrite map_total_insert //.
    iFrame.
    iSplit.
    { iPureIntro. rewrite dom_insert_L. rewrite elements_disj_union.
      - rewrite elements_singleton. rewrite Hlocked_dom. rewrite Permutation_app_comm. done.
      - set_solver.
    }
    iApply big_sepM_insert; first by auto.
    iFrame.
    iFrame "#". done.
  }

  iIntros "[Haccts_slice Hloop]".
  iNamed "Hloop".

  (* Use inv to know that the sum is total_bal *)
  iApply fupd_wp.
  iInv bankN as ">HbankInv" "HbankInvClose".
  iNamed "HbankInv".

  iDestruct (big_sepM_sep with "Hml") as "[#Hml_islock Hmlkv]".
  iDestruct (big_sepM_mono_wand _ (λ k v, ⌜m !! k = Some v⌝ ∗ ∃ vd : list u8, ⌜has_encoding_Uint64 vd v⌝ ∗ kvptsto (kv_gn γ) k vd ∗ k [[log_gn γ]]↦ v)%I _ (map_ctx (log_gn γ) 1 m)%I with "[] [$HlogBalCtx $Hmlkv]") as "[HlogBalCtx Hmlkv]".
  {
    iModIntro.
    iIntros (??) "%Hsome [HlogBalCtx HbankPs]".
    iDestruct "HbankPs" as (vd) "(%Henc & Hphys & Hlog)".
    iDestruct (map_valid with "HlogBalCtx Hlog") as %Hlogeq.
    iFrame "∗%".
  }

  iMod ("HbankInvClose" with "[HlogBalCtx]") as "_".
  { iNext. iExists _. iFrame "∗ %". }
  iModIntro.

  iDestruct (big_sepM_sep with "Hmlkv") as "[#Hmleq Hmlkv]".
  iDestruct (big_sepM_impl_subseteq with "Hmleq") as "%Hsubset".
  replace locked with m.
  2: {
    symmetry.
    apply subseteq_dom_eq; eauto.
    apply elem_of_subseteq.
    intros x Hx.
    apply elem_of_elements.
    rewrite Hlocked_dom. rewrite -H1. rewrite -H3.
    apply elem_of_elements.
    done.
  }

  iDestruct (big_sepM_sep with "[Hml_islock Hmlkv]") as "Hml".
  { iSplitR; [ iApply "Hml_islock" | iApply "Hmlkv" ]. }
  simpl.

  wp_loadField.
  wp_apply (wp_forSlicePrefix
    (λ done todo,
      ∃ mtodo,
      "Hlck" ∷ bck ↦[BankClerk :: "lck"] #lck ∗
      "Hlck_own" ∷ own_LockClerk lck γ.(bank_ls_names) ∗
      "%Hdom" ∷ ⌜Permutation (elements (dom mtodo)) todo⌝ ∗
      "Hml" ∷ [∗ map] k↦x ∈ mtodo, is_lock lockN γ.(bank_ls_names) k (bankPs γ k) ∗
        (∃ vd : list u8, ⌜has_encoding_Uint64 vd x⌝ ∗ kvptsto (kv_gn γ) k vd ∗ k [[log_gn γ]]↦ x))%I
    with "[] [$Haccts_slice $Hlck $Hlck_own Hml]").
  {
    iIntros (?? ??) "%Hx".
    iIntros (Ψ) "!> Hpre HΨ".
    iNamed "Hpre".
    wp_loadField.
    assert (x ∈ dom mtodo) as Helem.
    { apply elem_of_elements. rewrite Hdom. constructor. }
    apply elem_of_dom in Helem. destruct Helem.
    iDestruct (big_sepM_delete with "Hml") as "[Hx Hml]"; first by eauto.
    iDestruct "Hx" as "[Hacc_islock HbankPs]".
    wp_apply (wp_LockClerk__Unlock with "[$Hlck_own $Hacc_islock HbankPs]").
    { iDestruct "HbankPs" as (?) "(% & Hkv & Hlog)". iExists _, _. iFrame "∗%". }
    iIntros "Hlck_own".
    iApply "HΨ". iFrame. iPureIntro.
    replace (mtodo) with (<[x := x0]> (delete x mtodo)) in Hdom.
    2: rewrite insert_delete //.
    rewrite dom_insert_L in Hdom.
    rewrite elements_disj_union in Hdom.
    { rewrite elements_singleton in Hdom. simpl in Hdom.
      apply Permutation_cons_inv in Hdom. done. }
    set_solver.
  }
  {
    iExists _.
    iFrame. iPureIntro. set_solver.
  }

  iIntros "[Haccts_slice H]".
  iNamed "H".

  wp_load.
  replace (map_total m) with (bal_total) by auto.
  iApply "Hpost".
  iModIntro. iFrame "Hkck_own ∗#%".
Qed.

Lemma Bank__SimpleAudit_spec (bck:loc) γ accts :
{{{
     inv bankN (bank_inv γ accts) ∗
     own_bank_clerk γ bck accts
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

Lemma wp_MakeBankClerkSlice (lockhost kvhost : u64) cm γ1 γ2 cid accts (accts_s : Slice.t) acc0 (accts_l : list u64) :
  {{{
       is_coord_server lockhost γ1 ∗
       is_coord_server kvhost γ2 ∗
       is_ConnMan cm ∗
       is_lock lockN (γ1.(coord_kv_gn)) init_flag
         (init_lock_inv init_flag γ1.(coord_kv_gn) γ2.(coord_kv_gn) accts) ∗
       own_slice_small accts_s uint64T (DfracOwn 1) (acc0 :: accts_l) ∗
       ⌜Permutation (elements accts) (acc0 :: accts_l)⌝
  }}}
    MakeBankClerkSlice #lockhost #kvhost #cm #init_flag (slice_val accts_s) #cid
  {{{
      γ (ck:loc), RET #ck; own_bank_clerk γ ck accts ∗ inv bankN (bank_inv γ accts)
  }}}
.
Proof.
  iIntros (Φ) "(#Hcoord_lock&#Hcoord_kv&#Hcm&#Hinit_lock&Haccts_slice&%Hperm) HΦ".
  rewrite /MakeBankClerk.
  wp_call.
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
  do 2 wp_storeField.

  wp_loadField.
  wp_apply (wp_LockClerk__Lock with "[$]").
  iIntros "(Hlk&Hinit)".

  wp_pures.
  wp_apply (typed_slice.wp_NewSlice (V:=u8)).
  iIntros (s0) "Hsl0".
  wp_loadField.
  wp_apply (wp_SeqKVClerk__Get with "[$Hkv]").
  iDestruct "Hinit" as "[Huninit|Hinit]".
  - iDestruct "Huninit" as "(Hflag&Haccs)".
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
    iIntros (??) "(Hval_slice0&%)".
    wp_loadField.
    iDestruct (own_slice_to_small with "Hval_slice0") as "Hval_slice0".
    iMod (own_slice_small_persist with "Hval_slice0") as "#Hval_slice0".

    wp_apply (wp_SliceGet with "[$Haccts_slice]"); first by eauto.
    iIntros "Haccts_slice".
    wp_loadField.
    wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.

    iDestruct (big_sepS_elements with "Haccs") as "Haccs".
    rewrite Hperm.
    iDestruct (big_sepL_cons with "Haccs") as "[Hacc0 Haccs]".
    iDestruct "Hacc0" as "(Hacc0_2 & Hacc0_1)".

    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc0_2".
    iMod ("Hclo") as "_". iIntros "!> Hkv".
    wp_pures.

    wp_loadField.
    iDestruct (own_slice_small_sz with "Haccts_slice") as %Hslicelen. simpl in Hslicelen.
    wp_apply wp_SliceSkip; first by word.
    iDestruct (slice_small_split _ 1 with "Haccts_slice") as "[Haccts_slice0 Haccts_slice]".
    { simpl; word. }
    rewrite skipn_cons. replace (drop 0 accts_l) with (accts_l) by reflexivity.

    wp_apply (wp_forSlicePrefix
      (λ done todo, ∃ (mdone: gmap u64 u64),
        "kvck" ∷ l ↦[BankClerk :: "kvck"] #kvCk ∗
        "Hkv" ∷ own_SeqKVClerk kvCk γ2.(coord_kv_gn) ∗
        "Htodo" ∷ ([∗ list] acc ∈ todo,
          "Hkv2" ∷ kvptsto γ2.(coord_kv_gn) acc [] ∗
          "Hkv1" ∷ kvptsto γ1.(coord_kv_gn) acc []) ∗
        "%Hdone_dom" ∷ ⌜Permutation (elements (dom mdone)) done⌝ ∗
        "Hdone" ∷ [∗ map] acc ↦ bal ∈ mdone,
          ⌜bal = W64 0⌝ ∗
          ∃ data,
            kvptsto γ1.(coord_kv_gn) acc [] ∗
            kvptsto γ2.(coord_kv_gn) acc data ∗
            ⌜has_encoding_Uint64 data bal⌝)%I with "[] [$Haccts_slice $kvck $Hkv Haccs]").
    {
      iIntros (????) "%Hx".
      iIntros (Ψ) "!> Hpre HΨ".
      iNamed "Hpre".
      wp_apply (wp_EncodeUint64).
      iIntros (??) "(Hval_slice&%)".
      wp_loadField.
      iDestruct (own_slice_to_small with "Hval_slice") as "Hval_slice".
      iMod (own_slice_small_persist with "Hval_slice") as "#Hval_slice".
      wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.

      iDestruct "Htodo" as "[Hx Htodo]".
      iNamed "Hx".

      iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
      iExists _. iFrame. iIntros "Hacc1_phys".
      iMod ("Hclo") as "_". iIntros "!> Hkv".
      wp_pures.

      assert (x ∉ dom mdone) as Hnotelemof.
      {
        assert (NoDup (acc0 :: accts_l)) as Hnodup.
        { rewrite -Hperm. apply NoDup_elements. }
        apply NoDup_cons_1_2 in Hnodup.
        rewrite -Hx in Hnodup.
        intro Helem.
        apply elem_of_elements in Helem. rewrite Hdone_dom in Helem.
        rewrite Permutation_app_comm in Hnodup.
        apply NoDup_app in Hnodup.
        destruct Hnodup as (_&Hnodup&_).
        specialize (Hnodup x). apply Hnodup; eauto. constructor.
      }

      iApply "HΨ". iExists (<[x := W64 0]> mdone).
      iFrame. iSplitR.
      { iPureIntro. rewrite dom_insert_L. rewrite elements_disj_union; last by set_solver.
        rewrite elements_singleton. rewrite Hdone_dom. apply Permutation_app_comm.
      }
      iApply big_sepM_insert.
      { apply not_elem_of_dom_1. done. }
      iFrame. iSplit; done.
    }
    {
      iExists ∅. iFrame. iSplit.
      { rewrite dom_empty_L elements_empty //. }
      iApply big_sepM_empty. done.
    }
    iIntros "[Haccts_slice Hi]".
    iNamed "Hi".

    wp_apply (typed_slice.wp_NewSlice (V:=u8)).
    iIntros (?) "Hflag_val_slice".
    wp_loadField.
    iDestruct (own_slice_to_small with "Hflag_val_slice") as "Hflag_val_slice".
    iMod (own_slice_small_persist with "Hflag_val_slice") as "#Hflag_val_Slice".
    wp_apply (wp_SeqKVClerk__Put with "[$Hkv]"); first by eauto.
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hflag_phys".
    iMod ("Hclo") as "_". iIntros "!> Hkv".
    wp_pures.

    wp_loadField.
    iMod (map_init_many (<[acc0 := bal_total]> mdone)) as (γlog) "[Hmap_ctx Haccs]".
    set γ := {| bank_ls_names := γ1.(coord_kv_gn);
                bank_ks_names := γ2.(coord_kv_gn);
                bank_logBalGN := γlog |}.

    assert (acc0 ∉ dom mdone) as Hnotelemof.
    {
      assert (NoDup (acc0 :: accts_l)) as Hnodup.
      { rewrite -Hperm. apply NoDup_elements. }
      intro Helem.
      apply elem_of_elements in Helem. rewrite Hdone_dom in Helem.
      apply NoDup_cons in Hnodup. destruct Hnodup as [Hn0 Hn1]. done.
    }
    apply not_elem_of_dom_1 in Hnotelemof as Hnotelemof_none.

    iDestruct (big_sepM_sep with "Hdone") as "[#Hdone_zero Hdone]".
    iDestruct (big_sepM_insert with "[$Hdone Hacc0_1 Hacc0_2]") as "Hdone"; first by eassumption.
    { iExists _. iFrame. done. }

    iDestruct (big_sepM_sep with "[$Hdone $Haccs]") as "Haccs".

    iMod (big_sepM_mono_fupd _ (λ k v, is_lock lockN γ1.(coord_kv_gn) k (bankPs γ k)) _ True%I with "[] [$Haccs]") as "[_ #Haccs]".
    { iModIntro.
      iIntros (k v) "%Hkv [_ H]".
      iDestruct "H" as "[H Hlog]".
      iDestruct "H" as (data') "(Hk0 & Hk1 & %Henc)".
      iMod (lock_alloc lockN _ _ k (bankPs γ k) with "[$] [Hk1 Hlog]") as "#Hlk".
      { iExists _, _. simpl. iFrame. done. }
      iModIntro. iFrame "#".
    }

    iAssert (⌜map_total mdone = 0⌝)%I as %Hdone_zero_total.
    { iDestruct "Hdone_zero" as %Hdone_zero.
      iPureIntro. apply map_total_zero. eauto. }

    iMod (inv_alloc bankN _ (bank_inv γ accts) with "[Hmap_ctx]") as "#Hinv".
    { iNext. iExists _. iSplitL "Hmap_ctx".
      { rewrite /named. iFrame. }
      iPureIntro; split.
      { rewrite map_total_insert; last by done. rewrite Hdone_zero_total. word. }
      { rewrite -Hdone_dom in Hperm.
        rewrite dom_insert_L.
        rewrite -(list_to_set_elements_L accts). rewrite Hperm. set_solver.
      }
    }

    iDestruct (own_slice_combine with "Haccts_slice0 Haccts_slice") as "Haccts_slice".
    { word. }
    rewrite firstn_cons /take /=.

    iDestruct (big_sepM_dom with "Haccs") as "Haccs_set".

    iDestruct (big_sepS_elements with "Haccs_set") as "Haccs_list".
    rewrite dom_insert_L. rewrite elements_disj_union.
    2: { apply not_elem_of_dom_2 in Hnotelemof_none. set_solver. }
    rewrite elements_singleton Hdone_dom.

    wp_apply (wp_LockClerk__Unlock with "[$Hlk $Hinit_lock Hflag_phys]").
    { iRight. iExists γlog. iFrame "Hflag_phys". iFrame "#".
      iApply big_sepS_elements.
      rewrite Hperm. iFrame "Haccs_list".
    }
    iIntros "H". wp_pures. iApply "HΦ". iModIntro. iFrame "Hinv".
    iExists _, _, _, _. iFrame "lck accts".
    iFrame "Hkv ∗%#".

  - iDestruct "Hinit" as (γlog) "(Hflag&#Hinv&#H)".
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
    { iRight. iExists γlog. iFrame "∗#". }
    iIntros "Hlck_own". wp_pures. iApply "HΦ". iModIntro. iFrame "Hinv".
    iExists _, _, _, _. iFrame "∗#%".
    iDestruct (big_sepS_elements with "H") as "He". rewrite Hperm. iFrame "He".
Qed.

Lemma wp_MakeBankClerk (lockhost kvhost : u64) cm γ1 γ2 cid (acc0 acc1 : u64) :
  {{{
       is_coord_server lockhost γ1 ∗
       is_coord_server kvhost γ2 ∗
       is_ConnMan cm ∗
       is_lock lockN (γ1.(coord_kv_gn)) init_flag
         (init_lock_inv init_flag γ1.(coord_kv_gn) γ2.(coord_kv_gn) {[acc0; acc1]}) ∗
       ⌜ acc0 ≠ acc1 ⌝
  }}}
    MakeBankClerk #lockhost #kvhost #cm #init_flag #acc0 #acc1 #cid
  {{{
      γ (ck:loc), RET #ck; own_bank_clerk γ ck {[acc0; acc1]} ∗ inv bankN (bank_inv γ {[acc0; acc1]})
  }}}
.
Proof.
  iIntros (Φ) "(Ha & Hb & Hc & Hd & %He) HΦ".
  wp_call.
  wp_apply wp_ref_of_zero; first by eauto.
  iIntros (accts) "Haccts".
  wp_load.
  wp_apply (wp_SliceAppend_to_zero); first by eauto.
  iIntros (s) "Hs".
  wp_store.
  wp_load.
  wp_apply (wp_SliceAppend with "Hs").
  iIntros (s2) "Hs".
  wp_store.
  wp_load.
  iDestruct (own_slice_to_small with "Hs") as "Hs".
  wp_apply (wp_MakeBankClerkSlice with "[-HΦ]").
  { iFrame. iPureIntro.
    rewrite elements_disj_union; last by set_solver.
    rewrite ?elements_singleton. set_solver.
  }
  iIntros (γ ck) "[Hck Hinv]".
  iApply "HΦ".
  iFrame.
Qed.

End bank_proof.
