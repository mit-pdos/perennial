From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import
  core cryptoffi logical_audit merkle serde.
From Perennial.Helpers Require Import Map.

Module Auditor.
Section defs.
Context `{!heapGS Σ, !pavG Σ}.
Definition own (ptr : loc) : iProp Σ :=
  ∃  ptrs_hist hist gs γ pk (ptr_keys : loc) (ptr_sk : loc) sl_hist,
  (* Physical ownership. *)
  "Hptr_keys" ∷ ptr ↦[Auditor :: "keyMap"] #ptr_keys ∗
  "Hptr_hist" ∷ ptr ↦[Auditor :: "histInfo"] (slice_val sl_hist) ∗
  "#Hptr_sk" ∷ ptr ↦[Auditor :: "sk"]□ #ptr_sk ∗
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) ptrs_hist ∗
  "#Hown_hist" ∷ ([∗ list] ptr_hist;info ∈ ptrs_hist;hist,
    AdtrEpochInfo.own ptr_hist info DfracDiscarded) ∗
  "#His_sk" ∷ is_sig_sk ptr_sk pk (sigpred γ) ∗

  (* Ghost ownership. *)
  "Hown_gs" ∷ mono_list_auth_own γ 1 gs ∗
  "#Hinv_gs" ∷ audit_gs_inv gs ∗

  (* Physical-ghost relation. *)
  "Hown_keys" ∷ own_Tree ptr_keys (default ∅ (last gs.*1)) (DfracOwn 1) ∗
  "%Hdigs_gs" ∷ ⌜ gs.*2 = AdtrEpochInfo.Dig <$> hist ⌝.

Definition valid (ptr : loc) : iProp Σ :=
  ∃ (mu : loc),
  "#Hptr_mu" ∷ ptr ↦[Auditor :: "mu"]□ #mu ∗
  "#HmuR" ∷ is_lock nroot #mu (own ptr).
End defs.
End Auditor.

Section specs.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_NewAuditor :
  {{{ True }}}
  NewAuditor #()
  {{{
    ptr_adtr sl_adtrPk adtrPk adtr_γ, RET (#ptr_adtr, slice_val sl_adtrPk);
    "Hvalid_adtr" ∷ Auditor.valid ptr_adtr ∗
    "#Hsl_adtrPk" ∷ own_slice_small sl_adtrPk byteT DfracDiscarded adtrPk ∗
    "#His_adtrPk" ∷ is_sig_pk adtrPk (sigpred adtr_γ)
  }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_rec.
  wp_apply wp_new_free_lock.
  iIntros (?) "Hl".
  iMod (mono_list_own_alloc ([] : list (merkle_map_ty * dig_ty))) as (γ) "[Hown_gs _]".
  wp_apply (wp_SigGenerateKey (sigpred γ)).
  iIntros "*". iNamed 1.
  wp_apply wp_NewTree.
  iIntros "* Hm".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros "* Ha".
  iDestruct (struct_fields_split with "Ha") as "Ha".
  iNamed "Ha".

  wp_pures. iApply "HΦ".
  iMod (own_slice_small_persist with "Hsl_sig_pk") as "#$".
  iMod (struct_field_pointsto_persist with "mu") as "#$".
  iMod (struct_field_pointsto_persist with "sk") as "#sk".
  iFrame "#".
  iMod (alloc_lock _ _ _ (Auditor.own _) with "Hl [-]") as "$"; [|done].
  rewrite zero_slice_val.
  iExists [], []. iFrame "Hown_gs ∗#".
  iDestruct own_slice_nil as "$"; [done..|].
  repeat try iSplit; try naive_solver.
Qed.

Lemma wp_Auditor__Get a (epoch : u64) :
  {{{
    "#Hvalid" ∷ Auditor.valid a
  }}}
  Auditor__Get #a #epoch
  {{{
    o (err : bool) (p : loc), RET (#p, #err);
    "#Hown_info" ∷ AdtrEpochInfo.own p o DfracDiscarded
  }}}.
Proof.
  iIntros (?) "H HΦ". iNamed "H".
  iNamed "Hvalid".
  wp_rec. wp_pures.
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlock Hown]".
  iNamed "Hown".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_if_destruct.
  - wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "HmuR ∗#%". }
    wp_pures.
    wp_apply wp_allocStruct.
    { val_ty. }
    iIntros (?) "H".
    wp_pures.
    iApply ("HΦ" $! (AdtrEpochInfo.mk _ _ _)).
    iPersist "H".
    iDestruct (struct_fields_split with "H") as "{H} H".
    iNamed "H".
    rewrite zero_slice_val.
    iFrame "#".
    by iDestruct own_slice_small_nil as "$".
  - wp_loadField.
    iDestruct (own_slice_sz with "Hsl_hist") as %Hsz.
    unshelve epose proof (list_lookup_lt ptrs_hist (uint.nat epoch) ltac:(word)) as [? Hlookup].
    iDestruct (own_slice_small_read with "Hsl_hist") as "[Hsl_hist Hread]".
    wp_apply (wp_SliceGet with "[$Hsl_hist //]").
    iIntros "Hsl_hist".
    iDestruct ("Hread" with "Hsl_hist") as "Hsl_hist".
    wp_pures.
    wp_loadField.
    iDestruct (big_sepL2_lookup_1_some with "[$]") as %[??].
    { done. }
    iDestruct (big_sepL2_lookup with "Hown_hist") as "H"; try done.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "HmuR ∗#%". }
    wp_pures.
    iApply "HΦ".
    by iFrame "#".
Qed.

Lemma wp_checkOneUpd ptr_keys keys d0 sl_label d1 label :
  {{{
    "Hown_keys" ∷ own_Tree ptr_keys keys d0 ∗
    "Hsl_label" ∷ own_slice_small sl_label byteT d1 label
  }}}
  checkOneUpd #ptr_keys (slice_val sl_label)
  {{{
    (err : bool), RET #err;
    "Hown_keys" ∷ own_Tree ptr_keys keys d0 ∗
    "Hsl_label" ∷ own_slice_small sl_label byteT d1 label ∗
    "Herr" ∷ (if err then True else
      "%Hlen_label" ∷ ⌜ Z.of_nat $ length label = hash_len ⌝ ∗
      "%Hlook_keys" ∷ ⌜ keys !! label = None ⌝)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_slice_len.
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  iDestruct (own_slice_small_sz with "Hsl_label") as %?.
  wp_apply (wp_Tree__Get with "[$Hown_keys $Hsl_label]").
  iIntros "*". iNamedSuffix 1 "_map".
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  iApply "HΦ". iFrame "∗%". word.
Qed.

Definition checkUpd_post (keys upd : merkle_map_ty) : iProp Σ :=
  "%Hlen_labels" ∷ ([∗ map] label ↦ _ ∈ upd, ⌜ length label = 32%nat ⌝) ∗
  "%Hdisj" ∷ ⌜ upd ##ₘ keys ⌝.

Lemma wp_checkUpd ptr_keys keys d0 ptr_upd upd_refs upd :
  {{{
    "Hown_keys" ∷ own_Tree ptr_keys keys d0 ∗
    "#Hown_upd_refs" ∷ own_map ptr_upd DfracDiscarded upd_refs ∗
    "#Hown_upd" ∷ ([∗ map] sl;v ∈ upd_refs;upd,
      own_slice_small sl byteT DfracDiscarded v)
  }}}
  checkUpd #ptr_keys #ptr_upd
  {{{
    (err : bool), RET #err;
    "Hown_keys" ∷ own_Tree ptr_keys keys d0 ∗
    "Herr" ∷ (if err then True else checkUpd_post keys upd)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_loopErr) "Hptr_loopErr".
  wp_apply (wp_MapIter_fold _ _ _
    (λ upd_refs',
    ∃ (loopErr : bool),
    "Hown_keys" ∷ own_Tree ptr_keys keys d0 ∗
    "Hptr_loopErr" ∷ ptr_loopErr ↦[boolT] #loopErr ∗
    "HloopErr" ∷ (if loopErr then True else
      ∃ upd',
      "%Hdom0" ∷ ⌜ dom upd_refs' = dom upd' ⌝ ∗
      "%Hsub" ∷ ⌜ upd' ⊆ upd ⌝ ∗
      "Hpost" ∷ checkUpd_post keys upd')
    )%I with "Hown_upd_refs [$Hown_keys $Hptr_loopErr]").
  { iExists ∅. repeat try iSplit; try naive_solver; iPureIntro.
    - eapply map_empty_subseteq.
    - eapply map_disjoint_empty_l. }
  { clear. iIntros (? k sl_v Φ) "!> (H&_&%Hlook_ptr) HΦ". iNamed "H".
    wp_apply wp_StringToBytes. iIntros (?) "Hsl_label".
    iDestruct (own_slice_to_small with "Hsl_label") as "Hsl_label".
    iDestruct (big_sepM2_lookup_l_some with "Hown_upd") as %[v Hlook_val];
      [exact Hlook_ptr|].
    iDestruct (big_sepM2_lookup with "Hown_upd") as "#Hsl_val";
      [exact Hlook_ptr|exact Hlook_val|].
    wp_apply (wp_checkOneUpd with "[$Hown_keys $Hsl_label $Hsl_val //]").
    iIntros "*". iNamed 1.
    wp_if_destruct.
    { wp_store. iApply "HΦ". by iFrame. }
    iNamed "Herr". iApply "HΦ". iFrame "∗%".
    destruct loopErr; [done|]. iNamed "HloopErr". iNamed "Hpost".
    iPureIntro. exists (<[k:=v]> upd').
    repeat try split.
    - set_solver.
    - by apply insert_subseteq_l.
    - apply map_Forall_insert_2; [lia|done].
    - by apply map_disjoint_insert_l_2. }
  iIntros "[_ H]". iNamed "H".
  wp_load. iApply "HΦ". iFrame. destruct loopErr; [done|]. iNamed "HloopErr".
  iDestruct (big_sepM2_dom with "Hown_upd") as %Hdom2.
  opose proof (map_subset_dom_eq _ _ _ _ _ Hsub) as <-; [set_solver|].
  by iFrame.
Qed.

Lemma wp_applyUpd ptr_keys keys ptr_upd upd_refs upd :
  {{{
    "Hown_keys" ∷ own_Tree ptr_keys keys (DfracOwn 1) ∗
    "#Hown_upd_refs" ∷ own_map ptr_upd DfracDiscarded upd_refs ∗
    "#Hown_upd" ∷ ([∗ map] sl;v ∈ upd_refs;upd,
      own_slice_small sl byteT DfracDiscarded v) ∗
    "%Hlen_labels" ∷ ([∗ map] label ↦ _ ∈ upd, ⌜ length label = 32%nat ⌝)
  }}}
  applyUpd #ptr_keys #ptr_upd
  {{{
    RET #();
    "Hown_keys" ∷ own_Tree ptr_keys (upd ∪ keys) (DfracOwn 1)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply (wp_MapIter_fold _ _ _
    (λ upd_refs',
    ∃ upd',
    "%Hdom" ∷ ⌜ dom upd_refs' = dom upd' ⌝ ∗
    "%Hsub" ∷ ⌜ upd' ⊆ upd ⌝ ∗
    "Hown_keys" ∷ own_Tree ptr_keys (upd' ∪ keys) (DfracOwn 1)
    )%I with "Hown_upd_refs [Hown_keys]").
  { iExists ∅. rewrite map_empty_union. iFrame.
    iPureIntro. split; [done|]. eapply map_empty_subseteq. }
  { clear -Hlen_labels. iIntros (? k sl_v Φ) "!> (H&_&%Hlook_ptr) HΦ". iNamed "H".
    wp_apply wp_StringToBytes. iIntros (?) "Hsl_label".
    iDestruct (own_slice_to_small with "Hsl_label") as "Hsl_label".
    iPersist "Hsl_label".
    iDestruct (big_sepM2_lookup_l_some with "Hown_upd") as %[v Hlook_val];
      [exact Hlook_ptr|].
    iDestruct (big_sepM2_lookup with "Hown_upd") as "#Hsl_val";
      [exact Hlook_ptr|exact Hlook_val|].
    opose proof (map_Forall_lookup_1 _ _ _ _ Hlen_labels Hlook_val).
    wp_apply (wp_Tree__Put with "[$Hown_keys]").
    { iFrame "#". iPureIntro. simpl in *. lia. }
    iIntros "*". iNamed 1.
    wp_apply (std_proof.wp_Assert with "[//]").
    iApply "HΦ".
    iExists (<[k:=v]> upd').
    rewrite insert_union_l. iFrame.
    iPureIntro. repeat try split.
    - set_solver.
    - by apply insert_subseteq_l. }
  iIntros "[_ H]". iNamed "H".
  wp_pures. iApply "HΦ".
  iDestruct (big_sepM2_dom with "Hown_upd") as %Hdom1.
  opose proof (map_subset_dom_eq _ _ _ _ _ Hsub) as ->; [|done].
  by rewrite -Hdom -Hdom1.
Qed.

Lemma wp_Auditor__Update ptr_a ptr_upd upd :
  {{{
    "#Hvalid" ∷ Auditor.valid ptr_a ∗
    "#Hupdate" ∷ UpdateProof.own ptr_upd upd DfracDiscarded
  }}}
  Auditor__Update #ptr_a #ptr_upd
  {{{
    (err : bool), RET #err; True
  }}}.
Proof.
  iIntros (?) "H HΦ". iNamed "H". iNamed "Hvalid". wp_rec.
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlock H]". iNamed "H".
  wp_loadField. wp_apply wp_slice_len.
  iNamed "Hupdate". do 2 wp_loadField.
  wp_apply (wp_checkUpd with "[$Hown_keys $HUpdatesM $HUpdatesMSl //]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { wp_loadField. wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    2: { wp_pures. by iApply "HΦ". }
    iFrame "∗#". iModIntro. iFrame "∗#%". }
  iNamed "Herr". do 2 wp_loadField.
  wp_apply (wp_applyUpd with "[$Hown_keys $HUpdatesM $HUpdatesMSl //]").
  iNamed 1. wp_loadField.
  wp_apply (wp_Tree__Digest with "[$Hown_keys]"). iIntros "*". iNamed 1.

  (* update gs. *)
  iMod (mono_list_auth_own_update_app
    [(upd.(UpdateProof.Updates) ∪ (default ∅ (last gs.*1)), dig)]
    with "Hown_gs") as "[Hown_gs #Hlb_gs]".
  pose proof (f_equal length Hdigs_gs) as Hlen_digs_gs.
  rewrite !length_fmap in Hlen_digs_gs.
  iDestruct (big_sepL2_length with "Hown_hist") as %Hlen_hist.
  iDestruct (own_slice_sz with "Hsl_hist") as %Hlen_sl_hist.
  iDestruct (audit_gs_snoc with "Hinv_gs His_dig") as "{Hinv_gs} Hinv_gs"; [done..|].

  (* sign dig. *)
  wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_apply wp_NewSliceWithCap; [word|].
  iIntros "* Hsl_preSigByt".
  remember (Slice.mk _ _ _).
  rewrite replicate_eq_0; [|done].
  wp_apply (PreSigDig.wp_enc (PreSigDig.mk _ _) with
    "[$Hsl_preSigByt $Epoch $Dig $Hsl_dig]").
  (* TODO: record field getter somehow got unfolded here. *)
  replace (let (_, sz, _) := sl_hist in sz) with (sl_hist.(Slice.sz)); [|done].
  iIntros "*". iNamed 1. simpl.
  iDestruct (own_slice_to_small with "Hsl_b") as "Hsl_b".
  wp_loadField.
  wp_apply (wp_SigPrivateKey__Sign with "[$Hsl_b]").
  { iFrame "His_sk #%". simpl. iPureIntro.
    replace (uint.nat sl_hist.(Slice.sz)) with (length gs); [|word].
    rewrite lookup_snoc. naive_solver. }
  iIntros "*". iNamedSuffix 1 "_adtr".
  iMod (own_slice_small_persist with "Hsl_sig_adtr") as "#Hsl_sig_adtr".
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|]. iIntros "* Hptr_newInfo".
  iMod (struct_pointsto_persist with "Hptr_newInfo") as "#Hptr_newInfo".
  wp_loadField.
  wp_apply (wp_SliceAppend with "Hsl_hist"). iIntros "* Hsl_hist".
  wp_storeField. wp_loadField.
  wp_apply (wp_Mutex__Unlock with "[-HΦ]").
  2: { wp_pures. by iApply "HΦ". }
  iFrame "∗#". iModIntro.
  iDestruct (struct_fields_split with "Hptr_newInfo") as "H". iNamed "H".
  iDestruct (big_sepL2_snoc _ _ (AdtrEpochInfo.mk _ _ _) with "[$Hown_hist]") as "{Hown_hist} Hown_hist".
  { iFrame "#". }
  iFrame "Hown_gs Hown_hist".
  rewrite !fmap_app last_snoc Hdigs_gs. by iFrame "∗#%".
Qed.

End specs.
