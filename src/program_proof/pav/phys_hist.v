From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core serde.

Section wps.
Context `{!heapGS Σ, !pavG Σ}.

Definition is_HistEntry (ptr : loc) (obj : map_val_ty) : iProp Σ :=
  ∃ sl_HistVal,
  "#Hptr_Epoch" ∷ ptr ↦[HistEntry :: "Epoch"]□ #obj.1 ∗
  "#Hptr_HistVal" ∷ ptr ↦[HistEntry :: "HistVal"]□ (slice_val sl_HistVal) ∗
  "#Hsl_HistVal" ∷ own_slice_small sl_HistVal byteT DfracDiscarded obj.2.

Definition own_hist sl_hist hist : iProp Σ :=
  ∃ dim0_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "#Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;hist, is_HistEntry p o).

Lemma wp_put_hist sl_hist hist ptr_e ep pk  :
  {{{
    "Hown_hist" ∷ own_hist sl_hist hist ∗
    "#His_entry" ∷ is_HistEntry ptr_e (ep, pk)
  }}}
  SliceAppend ptrT (slice_val sl_hist) #ptr_e
  {{{
    sl_hist', RET (slice_val sl_hist');
    "Hown_hist" ∷ own_hist sl_hist' (hist ++ [(ep, pk)])
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hown_hist".
  wp_apply (wp_SliceAppend with "Hsl_hist"). iIntros (?) "Hsl_hist".
  iDestruct (big_sepL2_snoc with "[$Hdim0_hist $His_entry]") as "Hnew_dim0_hist".
  iApply "HΦ". iFrame "∗#".
Qed.

Lemma wp_GetHist sl_hist hist (ep : w64) :
  {{{
    "Hown_hist" ∷ own_hist sl_hist hist
  }}}
  GetHist (slice_val sl_hist) #ep
  {{{
    (is_reg : bool) sl_pk pk, RET (#is_reg, slice_val sl_pk);
    "Hown_hist" ∷ own_hist sl_hist hist ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk ∗
    "%Heq_lat" ∷
      ⌜ match lookup_puts_hist hist ep with
        | None => is_reg = false
        | Some pk' => is_reg = true ∧ pk = pk'
        end ⌝
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". rewrite /GetHist. iNamed "Hown_hist".
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_isReg) "Hptr_isReg".
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_val) "Hptr_val".
  iDestruct (own_slice_small_read with "Hsl_hist") as "[Hsl_hist Hsl_restore]".
  wp_apply (wp_forSlicePrefix
    (λ donel _,
    ∃ (is_reg : bool) sl_pk pk,
    "Hptr_isReg" ∷ ptr_isReg ↦[boolT] #is_reg ∗
    "Hptr_val" ∷ ptr_val ↦[slice.T byteT] (slice_val sl_pk) ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk ∗
    "%Heq_lat" ∷
      ⌜ match lookup_puts_hist (take (length donel) hist) ep with
        | None => is_reg = false
        | Some pk' => is_reg = true ∧ pk = pk'
        end ⌝)%I with "[] [$Hsl_hist Hptr_isReg Hptr_val]").
  2: { iExists _, Slice.nil, []. iFrame. iSplit; [|done].
    iDestruct (own_slice_zero byteT) as "H".
    by iDestruct (own_slice_to_small with "H") as "?". }
  { clear. iIntros "* %". iIntros (Φ) "!> H HΦ". iNamed "H".
    opose proof (list_lookup_middle done todo x _ _) as Hlook_x; [done|].
    subst dim0_hist.
    iDestruct (big_sepL2_lookup_1_some with "Hdim0_hist")
      as %[[new_ep new_pk] Hlook_hist]; [exact Hlook_x|].
    iDestruct (big_sepL2_lookup with "Hdim0_hist")
      as "His_entry"; [exact Hlook_x|exact Hlook_hist|].
    iNamed "His_entry". wp_loadField. wp_if_destruct.
    - wp_store. wp_loadField. wp_store. iApply "HΦ".
      iFrame "Hsl_HistVal". iFrame "∗#". rewrite app_length. simpl.
      replace (length done + 1)%nat with (S $ length done)%nat; [|lia].
      rewrite (take_S_r _ _ _ Hlook_hist).
      rewrite /lookup_puts_hist filter_app.
      opose proof (list_filter_singleton (λ x, uint.Z x.1 ≤ uint.Z ep)
        (new_ep, new_pk)) as [[_?]|[Htmp _]]. { exfalso. simpl in *. word. }
      rewrite Htmp. clear Htmp. rewrite last_snoc. naive_solver.
    - iApply "HΦ". iFrame "Hsl_pk". iFrame "∗#". rewrite app_length. simpl.
      replace (length done + 1)%nat with (S $ length done)%nat; [|lia].
      rewrite (take_S_r _ _ _ Hlook_hist).
      rewrite /lookup_puts_hist filter_app.
      opose proof (list_filter_singleton (λ x, uint.Z x.1 ≤ uint.Z ep)
        (new_ep, new_pk)) as [[Htmp _]|[_?]]. 2: { exfalso. simpl in *. word. }
      rewrite Htmp. clear Htmp. list_simplifier. by iFrame "%". }
  iIntros "[H0 H1]". iNamed "H1". iDestruct ("Hsl_restore" with "H0") as "Hsl_hist".
  do 2 wp_load. wp_pures. iApply "HΦ". iFrame "∗#".
  iDestruct (big_sepL2_length with "Hdim0_hist") as %Htmp.
  rewrite Htmp in Heq_lat. clear Htmp.
  rewrite firstn_all in Heq_lat. naive_solver.
Qed.

End wps.
