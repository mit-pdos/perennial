From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core cryptoffi merkle serde.

Section gs.
Context `{!heapGS Σ, !pavG Σ}.

Definition maps_mono (ms : list adtr_map_ty) :=
  ∀ (i j : nat) mi mj,
  ms !! i = Some mi →
  ms !! j = Some mj →
  i ≤ j →
  mi ⊆ mj.

Definition epochs_ok (ms : list adtr_map_ty) :=
  ∀ (ep : nat) m_ep k ep' comm,
  ms !! ep = Some m_ep →
  m_ep !! k = Some (ep', comm) →
  uint.nat ep' ≤ ep.

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
  ∃ γ pk gs (ptr_map : loc) (ptr_sk : loc) sl_hist ptrs_hist hist,
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

Lemma wp_newAuditor :
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
  iMod (mono_list_own_alloc ([] : list (adtr_map_ty * dig_ty))) as (?) "[? _]".
  wp_apply wp_SigGenerateKey.
  { shelve. }
  iIntros "*". iNamed 1.
  wp_pures.
  wp_apply wp_NewTree.
  iIntros "* Hm".
  wp_pures.
  wp_apply wp_allocStruct; [val_ty|].
  iIntros "* Ha".
  iDestruct (struct_fields_split with "Ha") as "Ha".
  iNamed "Ha".
  wp_pures. iApply "HΦ".
  iFrame "#".
  iMod (own_slice_small_persist with "Hsl_sig_pk") as "#$".
  repeat iExists _.
  iMod (struct_field_pointsto_persist with "mu") as "#?".
  iMod (struct_field_pointsto_persist with "sk") as "#?".
  iFrame "#".
  iMod (alloc_lock with "[$] [-]") as "$"; last done.
  iNext. repeat iExists _.
  iFrame "∗#%".
  rewrite zero_slice_val.
  iFrame.
  iSplitR.
  { by iApply own_slice_small_nil. }
  iSplitR.
  { by iApply big_sepL2_nil. }
  iSplit.
  { by iApply big_sepL2_nil. }
  done.
  Unshelve.
  apply _.
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
  iIntros (?) "H HΦ". iNamed "H".
  iNamed "Hvalid".
  wp_rec. wp_pures.
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlock Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
  iNamed "Hupdate".
  wp_loadField.

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
  wp_pures.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_pures.
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

End specs.
