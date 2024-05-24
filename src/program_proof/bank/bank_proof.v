From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import grove_prelude std_proof marshal_stateless_proof.
From Perennial.program_proof.lock Require Import lock_proof.
From Goose.github_com.mit_pdos.gokv Require Import lockservice bank.

Class bankG Σ := {
    bank_mapG :> mapG Σ string u64 ;
  }.

Definition bankΣ :=
  #[mapΣ string u64].
Global Instance subG_pbΣ {Σ} : subG (bankΣ) Σ → (bankG Σ).
Proof. solve_inG. Qed.

Add Ring u64ring : (word.ring_theory (word := w64_instance.w64)).

Section bank_defs.

Context `{!invGS Σ, !bankG Σ}.

Record bank_names := BankNames {
  bank_ls_names: (lock_names (Σ:=Σ)) ; (* Logical balances of accounts; must match the physical balance by the time you give up the lock *)
  bank_kvptsto : string → string → iProp Σ ; (* Logical balances of accounts; must match the physical balance by the time you give up the lock *)
  bank_logBalGN : gname ; (* Logical balances of accounts; must match the physical balance by the time you give up the lock *)
}.

Definition log_gn γ := γ.(bank_logBalGN).
Definition lock_gn γ := γ.(bank_ls_names).

Definition bankPs γ := λ k, (∃ v, bank_kvptsto γ k (bytes_to_string $ u64_le v) ∗ k [[log_gn γ]]↦v)%I.

Definition bankN := nroot .@ "grove_bank_of_boston".
Definition lockN : namespace := nroot.@"grove_bank_of_boston_vault".

Definition bal_total : u64 := 1000.

Context (init_flag: string). (* Account names for bank *)

Definition map_total (m : gmap string u64) : u64 :=
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
  map_Forall (λ (_:string) (x : u64), x = 0) m ->
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

Definition bank_inv γ (accts : gset string) : iProp Σ :=
  ∃ (m:gmap string u64),
    "HlogBalCtx" ∷ map_ctx (log_gn γ) 1 m ∗
    "%" ∷ ⌜map_total m = bal_total⌝ ∗
    "%" ∷ ⌜dom m = accts⌝
.

Definition init_lock_inv γlk kvptsto (accts:gset string) : iProp Σ :=
  (* Uninit case *)
  (kvptsto init_flag "" ∗
   [∗ set] acc ∈ accts, kvptsto acc "" ∗ kvptsto_lock γlk acc ""
  ) ∨
  (* Already init case *)
  (∃ γlog,
      let γ := (BankNames γlk kvptsto γlog) in
   bank_kvptsto γ init_flag "1" ∗ inv bankN (bank_inv γ accts) ∗
    [∗ set] acc ∈ accts, is_lock lockN (lock_gn γ) acc (bankPs γ acc)).

Definition is_bank γlk kvptsto accs : iProp Σ :=
  is_lock lockN γlk init_flag
          (init_lock_inv γlk kvptsto accs).

End bank_defs.

Section bank_proof.
Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !bankG Σ}.

Context (init_flag: string). (* Account names for bank *)

Definition own_bank_clerk (bank_ck:loc) (accts : gset string) : iProp Σ :=
  ∃ (lck kck : loc) (accts_s : Slice.t) (accts_l : list string) γ E,
  "%" ∷ ⌜Permutation (elements accts) (accts_l)⌝ ∗
  "#Hlck_is" ∷ is_LockClerk lockN lck (lock_gn γ) ∗
  "#Hkck_is" ∷ is_Kv kck (bank_kvptsto γ) E ∗

  "#Hbinv" ∷ inv bankN (bank_inv γ accts) ∗

  "Hkck" ∷ bank_ck ↦[BankClerk :: "kvck"] #kck ∗
  "Hlck" ∷ bank_ck ↦[BankClerk :: "lck"] #lck ∗
  "Haccts" ∷ bank_ck ↦[BankClerk :: "accts"] (slice_val accts_s) ∗
  "Haccts_slice" ∷ own_slice_small accts_s stringT (DfracOwn 1) accts_l ∗

  "#Haccts_is_lock" ∷ [∗ list] acc ∈ accts_l, is_lock lockN (lock_gn γ) acc (bankPs γ acc)
.

Lemma acquire_two_spec (lck :loc) (ln1 ln2:string) γ:
{{{
     is_LockClerk lockN lck γ.(bank_ls_names) ∗
     is_lock lockN γ.(bank_ls_names) ln1 (bankPs γ ln1) ∗
     is_lock lockN γ.(bank_ls_names) ln2 (bankPs γ ln2)
}}}
  acquire_two #lck #(str ln1) #(str ln2)
{{{
     RET #();
      bankPs γ ln1 ∗
      bankPs γ ln2
}}}.
Proof.
  iIntros (Φ) "(#Hlck & #Hln1_islock & #Hln2_islock) Hpost".
  wp_lam.
  wp_pures.
  wp_apply (wp_LockClerk__Lock with "[$Hlck $Hln1_islock]").
  iIntros "HP1".
  wp_pures.
  wp_apply (wp_LockClerk__Lock with "[$Hlck $Hln2_islock]").
  iIntros "HP2".
  wp_pures.
  iApply "Hpost". by iFrame.
Qed.

Lemma release_two_spec (lck :loc) (ln1 ln2:string) γ:
{{{
     is_LockClerk lockN lck γ.(bank_ls_names) ∗
     is_lock lockN γ.(bank_ls_names) ln1 (bankPs γ ln1) ∗
     is_lock lockN γ.(bank_ls_names) ln2 (bankPs γ ln2) ∗
     bankPs γ ln1 ∗
     bankPs γ ln2
}}}
  release_two #lck #(str ln1) #(str ln2)
{{{
     RET #(); True
}}}.
Proof.
  iIntros (Φ) "(#Hlck & #Hln1_islock & #Hln2_islock & HP1 & HP2) Hpost".
  wp_lam.
  wp_pures.
  wp_apply (wp_LockClerk__Unlock with "[$Hlck $Hln1_islock $HP1]").
  wp_pures.
  wp_apply (wp_LockClerk__Unlock with "[$Hlck $Hln2_islock $HP2]").
  wp_pures.
  iApply "Hpost"; by iFrame.
Qed.

Lemma wp_decodeInt (x:u64) :
  {{{
        True
  }}}
    decodeInt #(str bytes_to_string (u64_le x))
  {{{
        RET #x; True
  }}}
.
Proof.
  iIntros (?) "_ HΦ".
  wp_lam.
  wp_pures.
  wp_apply wp_StringToBytes.
  iIntros (?) "Hsl".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  rewrite bytes_to_string_inj.
  wp_apply (wp_ReadInt with "[$]").
  iIntros. wp_pures. iModIntro. by iApply "HΦ".
Qed.

Lemma wp_encodeInt (x:u64) :
  {{{
        True
  }}}
    encodeInt #x
  {{{
        RET #(str bytes_to_string (u64_le x)); True
  }}}
.
Proof.
  iIntros (?) "_ HΦ".
  wp_lam.
  wp_pures.
  change (slice.nil) with (slice_val Slice.nil).
  wp_apply (wp_WriteInt with "[]").
  { iApply own_slice_zero. }
  iIntros (?) "Hsl".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_StringFromBytes with "[$]").
  iIntros "_".
  simpl. by iApply "HΦ".
Qed.

Lemma Bank__transfer_internal_spec (bck:loc) (src dst:string) (amount:u64) accts :
{{{
     own_bank_clerk bck accts ∗
     ⌜ src ∈ accts ⌝ ∗
     ⌜ dst ∈ accts ⌝ ∗
     ⌜ src ≠ dst ⌝
}}}
  BankClerk__transfer_internal #bck #(str src) #(str dst) #amount
{{{
     RET #();
     own_bank_clerk bck accts
}}}.
Proof.
  iIntros (Φ) "(Hpre & %Hsrc & %Hdst & %Hneq) Hpost".
  iNamed "Hpre".
  wp_lam. wp_pures.
  wp_loadField.

  rewrite -elem_of_elements H in Hsrc.
  apply elem_of_list_lookup_1 in Hsrc as [? Hsrc].
  rewrite -elem_of_elements H in Hdst.
  apply elem_of_list_lookup_1 in Hdst as [? Hdst].
  iDestruct (big_sepL_lookup _ _ _ src with "Haccts_is_lock") as "#Hasrc_is_lock"; first by eauto.
  iDestruct (big_sepL_lookup _ _ _ dst with "Haccts_is_lock") as "#Hadst_is_lock"; first by eauto.

  wp_apply (acquire_two_spec with "[$Hlck_is]"); first iFrame "#".
  iIntros "(Hacc1_unlocked & Hacc2_unlocked)".
  iDestruct "Hacc1_unlocked" as (bal1) "(Hacc1_phys & Hacc1_log)".
  iDestruct "Hacc2_unlocked" as (bal2) "(Hacc2_phys & Hacc2_log)".
  wp_pures.
  wp_loadField.
  iAssert (_) with "Hkck_is" as "Hkck_is2".
  iNamed "Hkck_is2".
  wp_loadField.
  wp_apply ("HgetSpec" with "[//]").
  iApply (fupd_mask_intro); first by solve_ndisj. iIntros "Hclo".
  iExists _. iFrame "Hacc1_phys".
  iIntros "Hacc1_phys". iMod ("Hclo") as "_". iModIntro.
  iIntros "_".
  wp_pures.
  wp_apply wp_decodeInt.
  wp_pures.
  destruct bool_decide eqn:HenoughBalance; wp_pures.
  - (* Safe to do the transfer *)
    wp_apply wp_encodeInt.
    wp_loadField.
    wp_loadField.
    wp_apply ("HputSpec" with "[//]").
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc1_phys".
    iMod ("Hclo") as "_". iIntros "!> _".
    wp_pures.
    wp_loadField.

    wp_loadField.
    wp_apply ("HgetSpec" with "[//]").
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame "Hacc2_phys".
    iIntros "Hacc2_phys". iMod ("Hclo") as "_". iModIntro.
    iIntros "_".
    wp_apply wp_decodeInt.
    wp_pures.
    wp_apply wp_encodeInt.
    wp_loadField.
    wp_loadField.

    wp_apply ("HputSpec" with "[//]").
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc2_phys".
    iMod ("Hclo") as "_". iIntros "!> _".
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
    wp_apply (release_two_spec with "[$Hlck_is Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; repeat iExists _; iFrame; eauto. }
    wp_pures. iApply "Hpost". iModIntro.
    repeat iExists _. iFrame "∗%".
    (* FIXME: Coq's conversion checker will hang when we try to frame the occurrence of Hkck_is 
        _within_ is_lockClerk. You can reproduce this with:

      iSplitL; last admit. iExists _, _. iSplitR; [ admit | iSplitL; [ | admit]]. 
      Timeout 10 iFrame "Hkck_is".

      Maybe [is_Kv] or [is_lockClerk] should be made Typeclasses Opaque..? *)
    iFrame "Hlck_is #".
  - (* Don't do the transfer *)
    wp_loadField.
    wp_apply (release_two_spec with "[$Hlck_is Hacc1_phys Hacc2_phys Hacc1_log Hacc2_log]").
    { iFrame "#". iSplitL "Hacc1_phys Hacc1_log"; repeat iExists _; iFrame; eauto. }
    wp_pures. iApply "Hpost". iModIntro.
    repeat iExists _. iClear "Hasrc_is_lock Hadst_is_lock". iFrame "∗%".
    iFrame "Hlck_is Hkck_is". iFrame "#".
Qed.

Lemma Bank__SimpleTransfer_spec (bck:loc) accts :
{{{
     own_bank_clerk bck accts
}}}
  BankClerk__SimpleTransfer #bck
{{{
     RET #();
     own_bank_clerk bck accts
}}}.
Proof.
  iIntros (Φ) "Hpre Hpost".
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
    wp_pures. iModIntro. iLeft. iFrame. iSplit; first by done.
    repeat iExists _. iFrame "∗% Hlck_is #".
  }

  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  destruct (bool_decide (uint.Z dst < uint.Z accts_s.(Slice.sz))) eqn:Hdst.
  2: {
    wp_pures. iModIntro. iLeft. iFrame. iSplit; first by done.
    repeat iExists _. iFrame "∗% Hlck_is #".
  }

  wp_if_destruct.
  2: {
    wp_pures. iModIntro. iLeft. iFrame. iSplit; first by done.
    repeat iExists _. iFrame "∗% Hlck_is #".
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

  wp_apply (Bank__transfer_internal_spec with "[-Hpost]").
  { iSplitL.
    - repeat iExists _. iFrame "∗% Hlck_is #".
    - iPureIntro.
      split.
      { rewrite -elem_of_elements H elem_of_list_lookup; by eauto. }
      split.
      { rewrite -elem_of_elements H elem_of_list_lookup; by eauto. }
      intro Hc; subst.
      assert (NoDup accts_l) as Hnodup.
      { rewrite -H. apply NoDup_elements. }
      epose proof (NoDup_lookup _ _ _ _ Hnodup Hasrc Hadst).
      apply Heqb. f_equal. f_equal. word.
  }

  iIntros "Hpre".
  wp_pures.
  iModIntro.
  iLeft.
  iFrame. done.
Qed.

Lemma Bank__get_total_spec (bck:loc) accts :
{{{
     own_bank_clerk bck accts
}}}
  BankClerk__get_total #bck
{{{
     RET #bal_total;
     own_bank_clerk bck accts
}}}.
Proof.
  iIntros (Φ) "Hpre Hpost".
  wp_call.
  wp_apply wp_ref_of_zero; first by done.
  iIntros (sum) "Hsum".

  iNamed "Hpre".
  wp_loadField.
  wp_apply (wp_forSlicePrefix (λ done todo,
    ∃ locked,
      "Hlck" ∷ bck ↦[BankClerk :: "lck"] #lck ∗
      "Hkck" ∷ bck ↦[BankClerk :: "kvck"] #kck ∗
      "Hsum" ∷ sum ↦[uint64T] #(map_total locked) ∗
      "%Hlocked_dom" ∷ ⌜Permutation (elements (dom locked)) done⌝ ∗
      "Hml" ∷ [∗ map] acc ↦ bal ∈ locked,
        is_lock lockN γ.(bank_ls_names) acc (bankPs γ acc) ∗
        (bank_kvptsto γ acc (bytes_to_string $ u64_le $ bal) ∗ acc [[log_gn γ]]↦ bal))%I
    with "[] [$Haccts_slice Hsum $Hlck $Hkck]").
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
    { rewrite -H0. set_solver. }
    wp_apply (wp_LockClerk__Lock with "[$Hlck_is $Hx_is_lock]").
    iIntros "Hx".
    iDestruct "Hx" as (x_bal) "[Hx_kv Hx_log]".

    wp_load.
    wp_loadField.
    iAssert (_) with "Hkck_is" as "Hkck_is2".
    iNamed "Hkck_is2".
    wp_loadField.
    wp_apply ("HgetSpec" with "[//]").

    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame "Hx_kv".
    iIntros "Hx_kv". iMod ("Hclo") as "_". iModIntro.
    iIntros "_".
    wp_apply wp_decodeInt.

    wp_pures.
    wp_store.
    iModIntro.
    iApply "HΨ".
    iExists (<[x := x_bal]> locked).
    iFrame.

    destruct (decide (x ∈ dom locked)).
    {
      rewrite -H0 in H.
      rewrite -Hlocked_dom in H.
      exfalso.
      assert (NoDup (elements (dom locked) ++ x :: todo)) as Hnodup.
      { rewrite -H. apply NoDup_elements. }
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
    iFrame "#".
  }

  iIntros "[Haccts_slice Hloop]".
  iNamed "Hloop".

  (* Use inv to know that the sum is total_bal *)
  iApply fupd_wp.
  iInv bankN as ">HbankInv" "HbankInvClose".
  iNamed "HbankInv".

  iDestruct (big_sepM_sep with "Hml") as "[#Hml_islock Hmlkv]".
  iDestruct (big_sepM_mono_wand _ (λ k v, ⌜m !! k = Some v⌝ ∗ bank_kvptsto γ k (bytes_to_string $ u64_le v) ∗ k [[log_gn γ]]↦ v)%I _ (map_ctx (log_gn γ) 1 m)%I with "[] [$HlogBalCtx $Hmlkv]") as "[HlogBalCtx Hmlkv]".
  {
    iModIntro.
    iIntros (??) "%Hsome [HlogBalCtx HbankPs]".
    iDestruct "HbankPs" as "(Hphys & Hlog)".
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
    rewrite Hlocked_dom. rewrite -H. rewrite -H1.
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
      "%Hdom" ∷ ⌜Permutation (elements (dom mtodo)) todo⌝ ∗
      "Hml" ∷ [∗ map] k↦x ∈ mtodo, is_lock lockN γ.(bank_ls_names) k (bankPs γ k) ∗
        (bank_kvptsto γ k (bytes_to_string $ u64_le x) ∗ k [[log_gn γ]]↦ x))%I
    with "[] [$Haccts_slice $Hlck Hml]").
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
    wp_apply (wp_LockClerk__Unlock with "[$Hlck_is $Hacc_islock HbankPs]").
    { iDestruct "HbankPs" as "(Hkv & Hlog)". repeat iExists _. iFrame. }
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
  iModIntro. repeat iExists _. iFrame "∗ Hlck_is #%".
Qed.

Lemma Bank__SimpleAudit_spec (bck:loc) accts :
{{{
     own_bank_clerk bck accts
}}}
  BankClerk__SimpleAudit #bck
{{{
     RET #(); own_bank_clerk bck accts
}}}.
Proof.
  iIntros (Φ) "Hpre Hpost".
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

Lemma wp_MakeBankClerkSlice (lck kck : loc) γlk kvptsto E accts (accts_s : Slice.t) acc0 (accts_l : list string) :
  {{{
       is_LockClerk lockN lck γlk ∗
       is_Kv kck kvptsto E ∗
       is_lock lockN γlk init_flag
         (init_lock_inv init_flag γlk kvptsto accts) ∗
       own_slice_small accts_s stringT (DfracOwn 1) (acc0 :: accts_l) ∗
       ⌜Permutation (elements accts) (acc0 :: accts_l)⌝
  }}}
    MakeBankClerkSlice #lck #kck #(str init_flag) (slice_val accts_s)
  {{{
      (ck:loc), RET #ck; own_bank_clerk ck accts
  }}}
.
Proof.
  iIntros (Φ) "(#Hlck_is & #Hkck_is & #Hinit_lock & Haccts_slice & %Hperm) HΦ".
  rewrite /MakeBankClerk.
  wp_call.
  wp_apply wp_allocStruct; first val_ty.
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_pures.
  wp_storeField.
  wp_storeField.
  wp_storeField.
  wp_loadField.
  wp_apply (wp_LockClerk__Lock with "[$Hlck_is $Hinit_lock]").
  iIntros "Hinit".

  wp_pures.
  wp_loadField.
  iAssert (_) with "Hkck_is" as "Hkck_is2".
  iNamed "Hkck_is2".
  wp_loadField.
  wp_apply ("HgetSpec" with "[//]").
  iDestruct "Hinit" as "[Huninit|Hinit]".
  - iDestruct "Huninit" as "(Hflag&Haccs)".
    iApply fupd_mask_intro; first by set_solver+. iIntros "Hclo'".
    iExists _. iFrame. iIntros "Hflag".
    iMod "Hclo'" as "_". iIntros "!> _".
    wp_pures.
    wp_apply wp_encodeInt.
    wp_loadField.
    wp_apply (wp_SliceGet with "[$Haccts_slice]"); first by eauto.
    iIntros "Haccts_slice".
    wp_loadField.
    wp_loadField.
    wp_apply ("HputSpec" with "[//]").

    iDestruct (big_sepS_elements with "Haccs") as "Haccs".
    rewrite Hperm.
    iDestruct (big_sepL_cons with "Haccs") as "[Hacc0 Haccs]".
    iDestruct "Hacc0" as "(Hacc0_2 & Hacc0_1)".

    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hacc0_2".
    iMod ("Hclo") as "_". iIntros "!> _".
    wp_pures.

    wp_loadField.
    iDestruct (own_slice_small_sz with "Haccts_slice") as %Hslicelen. simpl in Hslicelen.
    wp_apply wp_SliceSkip; first by word.
    iDestruct (slice_small_split _ 1 with "Haccts_slice") as "[Haccts_slice0 Haccts_slice]".
    { simpl; word. }
    rewrite skipn_cons. replace (drop 0 accts_l) with (accts_l) by reflexivity.

    wp_apply (wp_forSlicePrefix
      (λ done todo, ∃ (sdone: gset string),
        "kvck" ∷ l ↦[BankClerk :: "kvck"] #kck ∗
        "Htodo" ∷ ([∗ list] acc ∈ todo,
          "Hkv2" ∷ kvptsto_lock γlk acc "" ∗
          "Hkv1" ∷ kvptsto acc "") ∗
        "%Hdone_dom" ∷ ⌜Permutation (elements sdone) done⌝ ∗
        "Hdone" ∷ [∗ map] acc ↦ bal ∈ (gset_to_gmap (W64 0) sdone),
            kvptsto_lock γlk acc "" ∗
            kvptsto acc (bytes_to_string $ u64_le bal)
            )%I with "[] [$Haccts_slice $kvck Haccs]").
    {
      iIntros (????) "%Hx".
      iIntros (Ψ) "!> Hpre HΨ".
      iNamed "Hpre".
      wp_apply wp_encodeInt.
      wp_loadField.
      wp_loadField.
      wp_apply ("HputSpec" with "[//]").

      iDestruct "Htodo" as "[Hx Htodo]".
      iNamed "Hx".

      iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
      iExists _. iFrame. iIntros "Hacc1_phys".
      iMod ("Hclo") as "_". iIntros "!> _".
      wp_pures.

      assert (x ∉ sdone) as Hnotelemof.
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

      iApply "HΨ". iExists ({[ x ]} ∪ sdone).
      iFrame. iSplitR.
      { iPureIntro. rewrite elements_disj_union; last by set_solver.
        rewrite elements_singleton. rewrite Hdone_dom. apply Permutation_app_comm.
      }
      rewrite gset_to_gmap_union_singleton.
      iApply big_sepM_insert.
      { apply not_elem_of_dom_1. rewrite dom_gset_to_gmap. done. }
      iFrame.
    }
    {
      iExists ∅. iFrame. iSplitL.
      {
        iApply (big_sepL_impl with "Haccs").
        iModIntro. iIntros "* ? [$$]".
      }
      iSplit.
      { done. }
      rewrite gset_to_gmap_empty.
      iApply big_sepM_empty. done.
    }
    iIntros "[Haccts_slice Hi]".
    iNamed "Hi".
    wp_loadField.
    wp_loadField.

    wp_apply ("HputSpec" with "[//]").
    iApply (fupd_mask_intro); first by set_solver. iIntros "Hclo".
    iExists _. iFrame. iIntros "Hflag_phys".
    iMod ("Hclo") as "_". iIntros "!> _".
    wp_pures.

    wp_loadField.
    iMod (map_init_many (<[acc0 := bal_total]> (gset_to_gmap (W64 0) sdone))) as (γlog) "[Hmap_ctx Haccs]".
    set γ := {| bank_ls_names := γlk;
                bank_kvptsto := kvptsto;
                bank_logBalGN := γlog |}.

    assert (acc0 ∉ sdone) as Hnotelemof.
    {
      assert (NoDup (acc0 :: accts_l)) as Hnodup.
      { rewrite -Hperm. apply NoDup_elements. }
      intro Helem.
      apply elem_of_elements in Helem. rewrite Hdone_dom in Helem.
      apply NoDup_cons in Hnodup. destruct Hnodup as [Hn0 Hn1]. done.
    }

    (* iDestruct (big_sepM_sep with "Hdone") as "[Hlocks Hdone]". *)
    iDestruct (big_sepM_insert with "[$Hdone Hacc0_1 Hacc0_2]") as "Hdone".
    { by apply lookup_gset_to_gmap_None. }
    { iFrame. }

    unfold bal_total.
    iDestruct (big_sepM_sep with "[$Hdone $Haccs]") as "Haccs".

    iMod (big_sepM_mono_fupd _ (λ k v, is_lock lockN γlk k (bankPs γ k)) _ True%I with "[] [$Haccs]") as "[_ #Haccs]".
    { iModIntro.
      iIntros (k v) "%Hkv [_ H]".
      iDestruct "H" as "[H Hlog]".
      iDestruct "H" as "(Hk0 & Hk1)".
      iMod (lock_alloc lockN _ _ k (bankPs γ k) with "[$] [Hk1 Hlog]") as "#Hlk".
      { repeat iExists _. simpl. iFrame. }
      iModIntro. iFrame "#".
    }

    iAssert (⌜map_total (gset_to_gmap (W64 0) sdone) = 0⌝)%I as %Hdone_zero_total.
    { iPureIntro. apply map_total_zero.
      intros ?? H.
      rewrite lookup_gset_to_gmap_Some in H.
      naive_solver.
    }

    iMod (inv_alloc bankN _ (bank_inv γ accts) with "[Hmap_ctx]") as "#Hinv".
    { iNext. iExists _. iSplitL "Hmap_ctx".
      { rewrite /named. iFrame. }
      iPureIntro; split.
      { rewrite map_total_insert.
        2:{ by apply lookup_gset_to_gmap_None. }
        rewrite Hdone_zero_total. unfold bal_total. word. }
      { rewrite -Hdone_dom in Hperm.
        rewrite dom_insert_L dom_gset_to_gmap.
        rewrite -(list_to_set_elements_L accts). rewrite Hperm. set_solver.
      }
    }

    iDestruct (own_slice_combine with "Haccts_slice0 Haccts_slice") as "Haccts_slice".
    { word. }
    rewrite firstn_cons /take /=.

    iDestruct (big_sepM_dom with "Haccs") as "Haccs_set".

    iDestruct (big_sepS_elements with "Haccs_set") as "Haccs_list".
    rewrite dom_insert_L. rewrite elements_disj_union.
    2: { rewrite dom_gset_to_gmap. set_solver. }
    rewrite elements_singleton dom_gset_to_gmap Hdone_dom.

    wp_apply (wp_LockClerk__Unlock with "[$Hlck_is $Hinit_lock Hflag_phys]").
    { iRight. iExists γlog. iFrame "Hflag_phys". iFrame "#".
      iApply big_sepS_elements.
      rewrite Hperm. iFrame "Haccs_list".
    }
    wp_pures. iApply "HΦ". iModIntro.
    repeat iExists _. iFrame "lck accts Haccts_slice".
    iSplitR; first done.
    instantiate (1:=γ).
    iFrame "Hlck_is Hkck_is Haccs_list ∗#%".

  - iDestruct "Hinit" as (γlog) "(Hflag&#Hinv&#H)".
    iApply fupd_mask_intro; first by set_solver+. iIntros "Hclo'".
    iExists _. simpl. iFrame. iIntros "Hflag".
    iMod "Hclo'" as "_". iIntros "!> _".
    wp_pures.
    wp_loadField.
    wp_apply (wp_LockClerk__Unlock with "[$Hlck_is $Hinit_lock Hflag]").
    { iRight. iExists γlog. iFrame "∗#". }
    wp_pures. iApply "HΦ". iModIntro.
    repeat iExists _. instantiate (2:=BankNames _ _ _). simpl.
    iFrame "∗ Hlck_is Hkck_is # %".
    iDestruct (big_sepS_elements with "H") as "He". rewrite Hperm. iFrame "He".
Qed.

Lemma wp_MakeBankClerk (lck kck : loc) γlk kvptsto (acc0 acc1 : string ) E :
  {{{
       is_LockClerk lockN lck γlk ∗
       is_Kv kck kvptsto E ∗
       is_bank init_flag γlk kvptsto {[ acc0; acc1 ]}∗
       ⌜ acc0 ≠ acc1 ⌝
  }}}
    MakeBankClerk #lck #kck #(str init_flag) #(str acc0) #(str acc1)
  {{{
      (ck:loc), RET #ck; own_bank_clerk ck {[acc0; acc1]}
  }}}
.
Proof.
  iIntros (Φ) "(Ha & Hb & Hc & %Hd) HΦ".
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
  { iFrame "Ha ∗". iPureIntro.
    rewrite elements_disj_union; last by set_solver.
    rewrite ?elements_singleton. set_solver.
  }
  iIntros (ck) "Hck". iApply "HΦ". iFrame "Hck".
Qed.

End bank_proof.
