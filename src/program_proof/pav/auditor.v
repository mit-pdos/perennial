From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core cryptoffi merkle serde server.

Definition lower_adtr (m : adtr_map_ty) : merkle_map_ty :=
  (λ v, MapValPre.encodesF (MapValPre.mk v.1 v.2)) <$> m.

Section invs.
Context `{!heapGS Σ, !pavG Σ}.
Definition maps_mono (ms : list adtr_map_ty) :=
  ∀ (i j : nat) mi mj,
  ms !! i = Some mi →
  ms !! j = Some mj →
  i ≤ j →
  mi ⊆ mj.

Definition maps_epoch_ok (ms : list adtr_map_ty) :=
  ∀ (ep : nat) m_ep k ep' comm,
  ms !! ep = Some m_ep →
  m_ep !! k = Some (ep', comm) →
  uint.nat ep' ≤ ep.

Definition adtr_inv ms := maps_mono ms ∧ maps_epoch_ok ms.
End invs.

Module comm_st.
Record t :=
  mk {
    key_maps: list (gmap opaque_label_ty (epoch_ty * comm_ty));
    digs: list dig_ty;
  }.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.
Definition valid γ (obj : t) : iProp Σ :=
  "#Hmaps" ∷ mono_list_lb_own γ obj.(key_maps) ∗
  "#Hdigs" ∷ ([∗ list] m;d ∈ obj.(key_maps);obj.(digs), is_dig (lower_adtr m) d).
End defs.
End comm_st.

Section inv.
Context `{!heapGS Σ, !pavG Σ}.
Definition adtr_sigpred γ : (list w8 → iProp Σ) :=
  λ preByt,
  (∃ pre st,
  "%Henc" ∷ ⌜ PreSigDig.encodes preByt pre ⌝ ∗
  "#Hcomm_st" ∷ comm_st.valid γ st ∗
  "%Hlook" ∷ ⌜ st.(comm_st.digs) !! uint.nat (pre.(PreSigDig.Epoch)) = Some pre.(PreSigDig.Dig) ⌝ ∗
  "%Hinv" ∷ ⌜ adtr_inv st.(comm_st.key_maps) ⌝
  )%I.
End inv.

Module Auditor.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.
(* This representation predicate existentially hides the state of the auditor. *)
Definition own (ptr : loc) : iProp Σ :=
  ∃ γ pk key_maps ptr_map last_map sl_sk sl_hist ptrs_hist hist,
  (* keys. *)
  "#Hptr_sk" ∷ ptr ↦[Auditor :: "sk"]□ (slice_val sl_sk) ∗
  "Hown_sk" ∷ own_sk sl_sk pk (adtr_sigpred γ) ∗
  (* maps. *)
  "Hmaps" ∷ mono_list_auth_own γ 1 key_maps ∗
  "%Hinv" ∷ ⌜ adtr_inv key_maps ⌝ ∗
  (* merkle tree. *)
  "Hown_map" ∷ own_merkle ptr_map (lower_adtr last_map) ∗
  "Hptr_map" ∷ ptr ↦[Auditor :: "keyMap"] #ptr_map ∗
  "%Hlast_map" ∷ ⌜ last key_maps = Some last_map ⌝ ∗
  (* history. *)
  "Hptr_hist" ∷ ptr ↦[Auditor :: "histInfo"] (slice_val sl_hist) ∗
  "Hsl_hist" ∷ own_slice_small sl_hist ptrT (DfracOwn 1) ptrs_hist ∗
  "Hown_hist" ∷ ([∗ list] ptr_hist;info ∈ ptrs_hist;hist,
    AdtrEpochInfo.own ptr_hist info) ∗
  "#Hdigs_hist" ∷ ([∗ list] m;info ∈ key_maps;hist,
    is_dig (lower_adtr m) info.(AdtrEpochInfo.Dig)).

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
  newAuditor #()
  {{{
    ptr_adtr sl_adtrPk adtrPk adtr_γ, RET (#ptr_adtr, slice_val sl_adtrPk);
    "Hvalid_adtr" ∷ Auditor.valid ptr_adtr ∗
    "#Hsl_adtrPk" ∷ own_slice_small sl_adtrPk byteT DfracDiscarded adtrPk ∗
    "#His_adtrPk" ∷ is_pk adtrPk (adtr_sigpred adtr_γ)
  }}}.
Proof. Admitted.

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
  admit. (* TODO: fill in UpdateProof.own *)
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
  -  wp_loadField.
     wp_apply (wp_Mutex__Unlock with "[-HΦ]").
     { iFrame "HmuR ∗#%". }
     wp_pures.
     wp_apply wp_allocStruct.
     { val_ty. }
     iIntros (?) "?".
     wp_pures.
     iApply "HΦ".
     admit. (* TODO: fill in AdtrEpochInfo.own *)
  - wp_loadField.
    iDestruct (own_slice_small_sz with "Hsl_hist") as %Hsz.
    unshelve epose proof (list_lookup_lt ptrs_hist (uint.nat epoch) ltac:(word)) as [? Hlookup].
    wp_apply (wp_SliceGet with "[$Hsl_hist //]").
    iIntros "Hsl".
    wp_pures.
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "HmuR ∗#%". }
    wp_pures.
    iApply "HΦ".
    (* FIXME: make Hown_hist have persistent ownership of AdtrEpochInfo *)
    admit.
Admitted.

End specs.
