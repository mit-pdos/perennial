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
  "%Hmaps_mono" ∷ ⌜ maps_mono gs.*1 ⌝ ∗
  "%Hepochs_ok" ∷ ⌜ epochs_ok gs.*1 ⌝.

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
  ∃  ptrs_hist hist gs γ pk (ptr_map : loc) (ptr_sk : loc) sl_hist,
  (* Physical ownership. *)
  "Hptr_map" ∷ ptr ↦[Auditor :: "keyMap"] #ptr_map ∗
  "Hptr_hist" ∷ ptr ↦[Auditor :: "histInfo"] (slice_val sl_hist) ∗
  "#Hptr_sk" ∷ ptr ↦[Auditor :: "sk"]□ #ptr_sk ∗
  "Hsl_hist" ∷ own_slice_small sl_hist ptrT (DfracOwn 1) ptrs_hist ∗
  "#Hown_hist" ∷ ([∗ list] ptr_hist;info ∈ ptrs_hist;hist,
    AdtrEpochInfo.own ptr_hist info) ∗
  "Hown_sk" ∷ own_sig_sk ptr_sk pk (adtr_sigpred γ) ∗

  (* Ghost ownership. *)
  "Hown_gs" ∷ mono_list_auth_own γ 1 gs ∗
  "#Hinv_gs" ∷ gs_inv gs ∗

  (* Physical-ghost relation. *)
  "Hown_map" ∷ own_merkle ptr_map (lower_map (default ∅ (last gs.*1))) ∗
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
  by iApply own_slice_small_nil.
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
    iDestruct (own_slice_small_sz with "Hsl_hist") as %Hsz.
    unshelve epose proof (list_lookup_lt ptrs_hist (uint.nat epoch) ltac:(word)) as [? Hlookup].
    wp_apply (wp_SliceGet with "[$Hsl_hist //]").
    iIntros "Hsl".
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

Definition upd_checks (keys : adtr_map_ty) (nextEp : w64) (label val : list w8) :=
  ∃ comm,
  length label = 32%nat ∧
  keys !! label = None ∧
  val = MapValPre.encodesF (MapValPre.mk nextEp comm).

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
    "Herr" ∷ (if err then True else ⌜ upd_checks keys nextEp label val ⌝)
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
      ([∗ map] label ↦ val ∈ upd, ⌜ upd_checks keys nextEp label val ⌝))
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
      ∃ upd',
      "%Hdom" ∷ ⌜ dom upd_refs' = dom upd' ⌝ ∗
      "%Hsub" ∷ ⌜ upd' ⊆ upd ⌝ ∗
      "%Hchecks" ∷ ([∗ map] label ↦ val ∈ upd', ⌜ upd_checks keys nextEp label val ⌝))
    )%I with "Hown_upd_refs [$Hown_keys $Hptr_loopErr]").
  { iExists ∅. repeat try iSplit; try naive_solver.
    iPureIntro. eapply map_empty_subseteq. }
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
    iDestruct "Herr" as "%Herr". iApply "HΦ". iFrame.
    destruct loopErr; [done|]. iNamed "HloopErr".
    iExists (<[k:=v]> upd'). iPureIntro. repeat try split.
    - set_solver.
    - by apply insert_subseteq_l.
    - by apply map_Forall_insert_2. }
  iIntros "[_ H]". iNamed "H".
  wp_load. iApply "HΦ". iFrame. destruct loopErr; [done|]. iNamed "HloopErr".
  iDestruct (big_sepM2_dom with "Hown_upd") as %Hdom1.
  opose proof (map_subset_dom_eq _ _ _ _ _ Hsub) as ->; [|done].
  by rewrite -Hdom -Hdom1.
Qed.

Lemma wp_Auditor__Update a ptr_upd upd :
  {{{
    "#Hvalid" ∷ Auditor.valid a ∗
    "Hupdate" ∷ UpdateProof.own ptr_upd upd
  }}}
  Auditor__Update #a #ptr_upd
  {{{
    (e : bool), RET #e; True
  }}}.
Proof.
  iIntros (?) "H HΦ". iNamed "H". iNamed "Hvalid". wp_rec.
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlock H]". iNamed "H".
  wp_loadField. wp_apply wp_slice_len.
  iNamed "Hupdate". do 2 wp_loadField.

  (* XXX: checkUpd only gets called here. Inlining its proof. *)
  wp_rec.
  wp_pures.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (?) "Hl".
  wp_pures.
  wp_apply (wp_MapIter_fold _ _ _ (λ _,
                                     _
              )%I with "[$] [-HΦ]").
  { iNamedAccu. }
  {
    iIntros "* !# * [Hpre %Hlookup] HΦ".
    iNamed "Hpre".
    wp_pures.
    wp_apply wp_StringToBytes.
    iIntros "* ?".
    iDestruct (own_slice_to_small with "[$]") as "?".
    (* XXX: checkOneUpd only called here so inlining a proof. *)
    wp_rec.
    wp_pures.
    wp_loadField.
    wp_apply (wp_Tree_Get with "[$]").
    iIntros "* HGetPost".
    iNamed "HGetPost".
    (* iNamed "Hreply". *)
    wp_pures.
    admit.
  }
Admitted.

End specs.
