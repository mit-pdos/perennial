From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core cryptoffi merkle serde.
From Perennial.Helpers Require Import Map.

Section gs.
Context `{!heapGS Σ, !pavG Σ}.

Definition maps_mono (ms : list adtr_map_ty) :=
  ∀ (i j : w64) mi mj,
  ms !! (uint.nat i) = Some mi →
  ms !! (uint.nat j) = Some mj →
  uint.Z i ≤ uint.Z j →
  mi ⊆ mj.

Definition epochs_ok (ms : list adtr_map_ty) :=
  ∀ (ep : w64) m_ep k ep' comm,
  ms !! (uint.nat ep) = Some m_ep →
  m_ep !! k = Some (ep', comm) →
  uint.Z ep' ≤ uint.Z ep.

Definition lower_map (m : adtr_map_ty) : merkle_map_ty :=
  (λ v, MapValPre.encodesF (MapValPre.mk v.1 v.2)) <$> m.

Definition gs_inv (gs : list (adtr_map_ty * dig_ty)) : iProp Σ :=
  "#His_digs" ∷ ([∗ list] x ∈ gs, is_dig (lower_map x.1) x.2) ∗
  "%Hmono_maps" ∷ ⌜ maps_mono gs.*1 ⌝ ∗
  "%Hok_epochs" ∷ ⌜ epochs_ok gs.*1 ⌝.

Lemma gs_snoc gs upd dig :
  let new_map := (upd ∪ (default ∅ (last gs.*1))) in
  gs_inv gs -∗
  is_dig (lower_map new_map) dig -∗
  ⌜ upd ##ₘ (default ∅ (last gs.*1)) ⌝ -∗
  ([∗ map] val ∈ upd, ⌜ val.1 = W64 (length gs) ⌝) -∗
  gs_inv (gs ++ [(new_map, dig)]).
Proof.
  iIntros "* #Hold_inv #His_dig %Hdisj %Hok_epoch".
  iNamedSuffix "Hold_inv" "_old".
iSplit; [|iPureIntro; split].
  - iApply big_sepL_snoc. iFrame "#".
  - unfold maps_mono in *. intros * Hlook_gsi Hlook_gsj Heq_ep.
    rewrite fmap_app in Hlook_gsi Hlook_gsj.
    destruct (decide (uint.Z i = uint.Z j)).
    { by simplify_eq/=. }
    destruct (decide (uint.Z j < length gs)).
    { eapply Hmono_maps_old.
      { rewrite lookup_app_l in Hlook_gsi; [done|].
        rewrite length_fmap. word. }
      { rewrite lookup_app_l in Hlook_gsj; [done|].
        rewrite length_fmap. word. }
      done. }
    rewrite lookup_app_r in Hlook_gsj.
    2: { rewrite length_fmap. word. }
    simpl in *. eapply list_lookup_singleton_Some in Hlook_gsj as [Heq_ep1 <-].
    rewrite length_fmap in Heq_ep1.
    rewrite lookup_app_l in Hlook_gsi.
    2: { rewrite length_fmap. word. }
    destruct (last gs.*1) as [m_last|] eqn:Hlast.
    2: { apply last_None in Hlast. by rewrite Hlast in Hlook_gsi. }
    simpl in *. trans m_last.
    2: { by apply map_union_subseteq_r. }
    rewrite last_lookup in Hlast.
    refine (Hmono_maps_old _
      (W64 (pred $ length gs)) _ _ Hlook_gsi _ _); [|word].
    replace (uint.nat (W64 _)) with (pred $ length gs); [|word].
    by rewrite length_fmap in Hlast.
  - unfold epochs_ok in *. intros * Hlook_gs Hlook_m.
    (* TODO: ep' somehow has w64_word_instance, whereas ep has w64. *)
    rewrite fmap_app in Hlook_gs.
    destruct (decide (uint.Z ep < length gs)).
    { eapply Hok_epochs_old; [|done].
      rewrite lookup_app_l in Hlook_gs; [done|].
      rewrite length_fmap. word. }
    rewrite lookup_app_r in Hlook_gs.
    2: { rewrite length_fmap. word. }
    simpl in *. apply list_lookup_singleton_Some in Hlook_gs as [Heq_ep <-].
    apply lookup_union_Some_raw in Hlook_m as [Hlook_upd | [_ Hlook_last]].
    { pose proof (map_Forall_lookup_1 _ _ _ _ Hok_epoch Hlook_upd) as ?.
      simpl in *. subst. word. }
    destruct (last gs.*1) as [m_last|] eqn:Hlast; [|set_solver]. simpl in *.
    opose proof (Hok_epochs_old
      (W64 (pred $ length gs)) _ _ _ _ _ Hlook_last) as ?; [|word].
    replace (uint.nat (W64 _)) with (pred $ length gs); [|word].
    by rewrite last_lookup length_fmap in Hlast.
Qed.

Definition adtr_sigpred γ : (list w8 → iProp Σ) :=
  λ preByt,
  (∃ pre gs,
  "%Henc" ∷ ⌜ PreSigDig.encodes preByt pre ⌝ ∗
  "#Hlb" ∷ mono_list_lb_own γ gs ∗
  "%Hlook_dig" ∷ ⌜ gs.*2 !! uint.nat pre.(PreSigDig.Epoch) = Some pre.(PreSigDig.Dig) ⌝ ∗
  "#Hinv_gs" ∷ gs_inv gs)%I.

End gs.

Module Auditor.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.
(* This representation predicate existentially hides the state of the auditor. *)
Definition own (ptr : loc) : iProp Σ :=
  ∃  ptrs_hist hist gs γ pk (ptr_keys : loc) (ptr_sk : loc) sl_hist,
  (* Physical ownership. *)
  "Hptr_keys" ∷ ptr ↦[Auditor :: "keyMap"] #ptr_keys ∗
  "Hptr_hist" ∷ ptr ↦[Auditor :: "histInfo"] (slice_val sl_hist) ∗
  "#Hptr_sk" ∷ ptr ↦[Auditor :: "sk"]□ #ptr_sk ∗
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) ptrs_hist ∗
  "#Hown_hist" ∷ ([∗ list] ptr_hist;info ∈ ptrs_hist;hist,
    AdtrEpochInfo.own ptr_hist info) ∗
  "Hown_sk" ∷ own_sig_sk ptr_sk pk (adtr_sigpred γ) ∗

  (* Ghost ownership. *)
  "Hown_gs" ∷ mono_list_auth_own γ 1 gs ∗
  "#Hinv_gs" ∷ gs_inv gs ∗

  (* Physical-ghost relation. *)
  "Hown_keys" ∷ own_merkle ptr_keys (lower_map (default ∅ (last gs.*1))) ∗
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
  {{{
    True
  }}}
  NewAuditor #()
  {{{
    ptr_adtr sl_adtrPk adtrPk adtr_γ, RET (#ptr_adtr, slice_val sl_adtrPk);
    "Hvalid_adtr" ∷ Auditor.valid ptr_adtr ∗
    "#Hsl_adtrPk" ∷ own_slice_small sl_adtrPk byteT DfracDiscarded adtrPk ∗
    "#His_adtrPk" ∷ is_sig_pk adtrPk (adtr_sigpred adtr_γ)
  }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_rec.
  wp_apply wp_new_free_lock.
  iIntros (?) "Hl".
  iMod (mono_list_own_alloc ([] : list (adtr_map_ty * dig_ty))) as (γ) "[Hown_gs _]".
  wp_apply (wp_SigGenerateKey (adtr_sigpred γ)).
  iIntros "*". iNamed 1.
  wp_apply wp_NewTree.
  iIntros "* Hm".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (ptr) "Ha".
  iDestruct (struct_fields_split with "Ha") as "Ha".
  iNamed "Ha".

  wp_pures. iApply "HΦ".
  iMod (own_slice_small_persist with "Hsl_sig_pk") as "#$".
  iMod (struct_field_pointsto_persist with "mu") as "#$".
  iMod (struct_field_pointsto_persist with "sk") as "#sk".
  iFrame "#".
  iMod (alloc_lock _ _ _ (Auditor.own ptr) with "Hl [-]") as "$"; [|done].
  rewrite zero_slice_val.
  iExists [], []. iFrame "Hown_gs ∗#". repeat try iSplit; try naive_solver.
  by iApply own_slice_nil.
Qed.

Lemma wp_Auditor__Get a (epoch : u64) :
  {{{
    "#Hvalid" ∷ Auditor.valid a
  }}}
  Auditor__Get #a #epoch
  {{{
    (b : bool) (p : loc) o, RET (#p, #b); AdtrEpochInfo.own p o
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
    iApply "HΦ".
    repeat iExists _.
    iDestruct (struct_fields_split with "H") as "H".
    iNamed "H".
    do 3 iMod (struct_field_pointsto_persist with "[$]") as "#?".
    rewrite zero_slice_val.
    iFrame "#".
    instantiate (1:=AdtrEpochInfo.mk [] [] []). simpl.
    repeat iDestruct (own_slice_small_nil byteT DfracDiscarded) as "$"; try done.
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

Lemma wp_checkOneUpd ptr_keys keys nextEp sl_label dq label sl_val val :
  {{{
    "Hown_keys" ∷ own_merkle ptr_keys (lower_map keys) ∗
    "Hsl_label" ∷ own_slice_small sl_label byteT dq label ∗
    "#Hsl_val" ∷ own_slice_small sl_val byteT DfracDiscarded val
  }}}
  checkOneUpd #ptr_keys #nextEp (slice_val sl_label) (slice_val sl_val)
  {{{
    (err : bool), RET #err;
    "Hown_keys" ∷ own_merkle ptr_keys (lower_map keys) ∗
    "Hsl_label" ∷ own_slice_small sl_label byteT dq label ∗
    "Herr" ∷ (if err then True else
      ∃ comm,
      "%Hlen_label" ∷ ⌜ length label = 32%nat ⌝ ∗
      "%Hlook_keys" ∷ ⌜ keys !! label = None ⌝ ∗
      "%Hdec_val" ∷ ⌜ val = MapValPre.encodesF (MapValPre.mk nextEp comm) ⌝)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply (wp_Tree__Get with "[$Hown_keys $Hsl_label]").
  iIntros "*". iNamedSuffix 1 "_map".
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  wp_apply (MapValPre.wp_dec with "[$Hsl_val]").
  iIntros "*". iNamedSuffix 1 "_val".
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  wp_apply wp_slice_len.
  wp_if_destruct. { iApply "HΦ". by iFrame. }
  iDestruct ("Herr_val" with "[//]") as "H".
  iNamedSuffix "H" "_dec". iNamed "Hown_obj_dec".
  wp_loadField.
  (* TODO: seal up own_merkle so it doesn't get unfolded by iFrame. *)
  wp_if_destruct. { iApply "HΦ". by iFrame "Htree_map ∗". }
  iApply "HΦ". iFrame "Htree_map ∗".
  iNamedSuffix "Herr_map" "_map".
  iDestruct (is_merkle_proof_to_entry with "His_proof_map") as "#His_entry".
  iDestruct (is_merkle_entry_with_map with "His_entry His_dig_map") as %Hlook_keys.
  iDestruct (own_slice_small_sz with "Hsl_tail_dec") as %Hlen_tail.
  opose proof (nil_length_inv tail _) as ->; [word|].
  (* TODO: somehow u64_le now gets unfolded by simpl. *)
  iPureIntro. eexists. repeat try split; [naive_solver|..].
  { rewrite lookup_fmap in Hlook_keys. by apply fmap_None in Hlook_keys. }
  by list_simplifier.
Qed.

Definition checkUpd_post keys nextEp upd upd_dec : iProp Σ :=
  "%Hlen_labels" ∷ ([∗ map] label ↦ _ ∈ upd, ⌜ length label = 32%nat ⌝) ∗
  "%Hdecode" ∷ ⌜ upd = lower_map upd_dec ⌝ ∗
  "%Hok_epoch" ∷ ([∗ map] val ∈ upd_dec, ⌜ val.1 = nextEp ⌝) ∗
  "%Hdisj" ∷ ⌜ upd_dec ##ₘ keys ⌝.

Lemma wp_checkUpd ptr_keys keys ptr_upd upd_refs upd nextEp :
  {{{
    "Hown_keys" ∷ own_merkle ptr_keys (lower_map keys) ∗
    "#Hown_upd_refs" ∷ own_map ptr_upd DfracDiscarded upd_refs ∗
    "#Hown_upd" ∷ ([∗ map] sl;v ∈ upd_refs;upd,
      own_slice_small sl byteT DfracDiscarded v)
  }}}
  checkUpd #ptr_keys #nextEp #ptr_upd
  {{{
    (err : bool), RET #err;
    "Hown_keys" ∷ own_merkle ptr_keys (lower_map keys) ∗
    "Herr" ∷ (if err then True else
      ∃ upd_dec, checkUpd_post keys nextEp upd upd_dec)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_loopErr) "Hptr_loopErr".
  wp_apply (wp_MapIter_fold _ _ _
    (λ upd_refs',
    ∃ (loopErr : bool),
    "Hown_keys" ∷ own_merkle ptr_keys (lower_map keys) ∗
    "Hptr_loopErr" ∷ ptr_loopErr ↦[boolT] #loopErr ∗
    "HloopErr" ∷ (if loopErr then True else
      ∃ upd' upd_dec',
      "%Hdom0" ∷ ⌜ dom upd_refs' = dom upd' ⌝ ∗
      "%Hdom1" ∷ ⌜ dom upd' = dom upd_dec' ⌝ ∗
      "%Hsub" ∷ ⌜ upd' ⊆ upd ⌝ ∗
      "Hpost" ∷ checkUpd_post keys nextEp upd' upd_dec')
    )%I with "Hown_upd_refs [$Hown_keys $Hptr_loopErr]").
  { iExists ∅, ∅. repeat try iSplit; try naive_solver; iPureIntro.
    - eapply map_empty_subseteq.
    - eapply map_disjoint_empty_l. }
  { clear. iIntros (? k sl_v Φ) "!> (H&_&%Hlook_ptr) HΦ". iNamed "H".
    wp_apply wp_StringToBytes. iIntros (?) "Hsl_label".
    iDestruct (own_slice_to_small with "Hsl_label") as "Hsl_label".
    iDestruct (big_sepM2_lookup_l_some with "Hown_upd") as %[v Hlook_val];
      [exact Hlook_ptr|].
    iDestruct (big_sepM2_lookup with "Hown_upd") as "#Hsl_val";
      [exact Hlook_ptr|exact Hlook_val|].
    wp_apply (wp_checkOneUpd with "[$Hown_keys $Hsl_label $Hsl_val]").
    iIntros "*". iNamed 1. wp_if_destruct.
    { wp_store. iApply "HΦ". by iFrame. }
    iNamed "Herr". iApply "HΦ". iFrame.
    destruct loopErr; [done|]. iNamed "HloopErr". iNamed "Hpost".
    iPureIntro. exists (<[k:=v]> upd'), (<[k:=(nextEp, comm)]> upd_dec').
    repeat try split.
    - set_solver.
    - set_solver.
    - by apply insert_subseteq_l.
    - by apply map_Forall_insert_2.
    - rewrite Hdecode /lower_map fmap_insert Hdec_val //.
    - by apply map_Forall_insert_2.
    - by apply map_disjoint_insert_l_2. }
  iIntros "[_ H]". iNamed "H".
  wp_load. iApply "HΦ". iFrame. destruct loopErr; [done|]. iNamed "HloopErr".
  iDestruct (big_sepM2_dom with "Hown_upd") as %Hdom2.
  opose proof (map_subset_dom_eq _ _ _ _ _ Hsub) as <-; [set_solver|].
  by iFrame.
Qed.

Lemma wp_applyUpd ptr_keys keys ptr_upd upd_refs upd :
  {{{
    "Hown_keys" ∷ own_merkle ptr_keys (lower_map keys) ∗
    "#Hown_upd_refs" ∷ own_map ptr_upd DfracDiscarded upd_refs ∗
    "#Hown_upd" ∷ ([∗ map] sl;v ∈ upd_refs;upd,
      own_slice_small sl byteT DfracDiscarded v) ∗
    "%Hlen_labels" ∷ ([∗ map] label ↦ _ ∈ upd, ⌜ length label = 32%nat ⌝)
  }}}
  applyUpd #ptr_keys #ptr_upd
  {{{
    RET #();
    "Hown_keys" ∷ own_merkle ptr_keys (upd ∪ lower_map keys)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply (wp_MapIter_fold _ _ _
    (λ upd_refs',
    ∃ upd',
    "%Hdom" ∷ ⌜ dom upd_refs' = dom upd' ⌝ ∗
    "%Hsub" ∷ ⌜ upd' ⊆ upd ⌝ ∗
    "Hown_keys" ∷ own_merkle ptr_keys (upd' ∪ lower_map keys)
    )%I with "Hown_upd_refs [Hown_keys]").
  { iExists ∅. rewrite map_empty_union. iFrame.
    iPureIntro. split; [done|]. eapply map_empty_subseteq. }
  { clear -Hlen_labels. iIntros (? k sl_v Φ) "!> (H&_&%Hlook_ptr) HΦ". iNamed "H".
    wp_apply wp_StringToBytes. iIntros (?) "Hsl_label".
    iDestruct (own_slice_to_small with "Hsl_label") as "Hsl_label".
    iDestruct (big_sepM2_lookup_l_some with "Hown_upd") as %[v Hlook_val];
      [exact Hlook_ptr|].
    iDestruct (big_sepM2_lookup with "Hown_upd") as "#Hsl_val";
      [exact Hlook_ptr|exact Hlook_val|].
    wp_apply (wp_Tree__Put with "[$Hown_keys $Hsl_label $Hsl_val]").
    iIntros "*". iNamed 1.
    opose proof ((proj2 Hgenie) _) as ->.
    { by opose proof (map_Forall_lookup_1 _ _ _ _ Hlen_labels Hlook_val) as ?. }
    wp_apply wp_Assert_true. iApply "HΦ".
    iExists (<[k:=v]> upd').
    iNamed "Herr". rewrite insert_union_l. iFrame "Htree".
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
    "Hupdate" ∷ UpdateProof.own ptr_upd upd
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
  wp_apply (wp_checkUpd with "[$Hown_keys $HUpdatesM $HUpdatesMSl]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { wp_loadField. wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    2: { wp_pures. by iApply "HΦ". }
    iFrame "∗#". iModIntro. iFrame "∗#%". }
  iNamed "Herr". do 2 wp_loadField. rewrite Hdecode {Hdecode} in Hlen_labels *.
  wp_apply (wp_applyUpd with "[$Hown_keys $HUpdatesM $HUpdatesMSl //]").
  iNamed 1. wp_loadField.
  wp_apply (wp_Tree__Digest with "[$Hown_keys]"). iIntros "*". iNamed 1.

  (* update gs. *)
  iMod (mono_list_auth_own_update_app
    [(upd_dec ∪ (default ∅ (last gs.*1)), dig)]
    with "Hown_gs") as "[Hown_gs #Hlb_gs]".
  rewrite -map_fmap_union.
  pose proof (f_equal length Hdigs_gs) as Hlen_digs_gs.
  rewrite !length_fmap in Hlen_digs_gs.
  iDestruct (big_sepL2_length with "Hown_hist") as %Hlen_hist.
  iDestruct (own_slice_sz with "Hsl_hist") as %Hlen_sl_hist.
  replace (sl_hist.(Slice.sz)) with (W64 $ length gs) in Hok_epoch; [|word].
  iDestruct (gs_snoc with "Hinv_gs His_dig [% //] [% //]") as "{Hinv_gs} Hinv_gs".

  (* sign dig. *)
  wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_apply wp_NewSlice_0. iIntros "* Hsl_preSigByt".
  wp_apply (PreSigDig.wp_enc (PreSigDig.mk _ _) with "[$Hsl_preSigByt $Epoch $Dig $Hsl_dig]").
  (* TODO: record field getter somehow got unfolded here. *)
  replace (let (_, sz, _) := sl_hist in sz) with (sl_hist.(Slice.sz)); [|done].
  iIntros "*". iNamed 1. simpl.
  iDestruct (own_slice_to_small with "Hsl_enc") as "Hsl_enc".
  wp_loadField.
  wp_apply (wp_SigPrivateKey__Sign with "[$Hown_sk $Hsl_enc]").
  { iFrame "#". iPureIntro. eexists. split; [done|].
    simpl. replace (uint.nat sl_hist.(Slice.sz)) with (length gs); [|word].
    by rewrite list_lookup_fmap lookup_snoc. }
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
  rewrite !fmap_app last_snoc Hdigs_gs. by iFrame "∗#".
Qed.

End specs.
