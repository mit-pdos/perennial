From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import alicebob.

From Perennial.program_proof.pav Require Import core serde.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Definition is_histEntry (ptr : loc) (opt_pk : option pk_ty) : iProp Σ :=
  match opt_pk with
  | None =>
    "#Hptr_is_reg" ∷ ptr ↦[histEntry :: "isReg"]□ #false
  | Some pk =>
    ∃ sl_pk,
    "#Hptr_is_reg" ∷ ptr ↦[histEntry :: "isReg"]□ #true ∗
    "#Hptr_pk" ∷ ptr ↦[histEntry :: "pk"]□ (slice_val sl_pk) ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk
  end.

Definition own_hist sl_hist hist : iProp Σ :=
  ∃ dim0_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "#Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;hist, is_histEntry p o).

Lemma wp_extendHist sl_hist hist (num_epochs : w64) :
  {{{
    "Hown_hist" ∷ own_hist sl_hist hist ∗
    "%Hlen_epochs" ∷ ⌜ Z.of_nat $ length hist <= uint.Z num_epochs ⌝
  }}}
  extendHist (slice_val sl_hist) #num_epochs
  {{{
    sl_hist', RET (slice_val sl_hist');
    "Hown_hist" ∷ own_hist sl_hist' (hist ++
      replicate (uint.nat num_epochs - length hist) (mjoin $ last hist))
  }}}.
Proof.
  iIntros (Φ) "H HΦ". wp_rec. iNamed "H". iNamed "Hown_hist".
  wp_apply wp_slice_len.
  iDestruct (own_slice_sz with "Hsl_hist") as %?.
  iDestruct (big_sepL2_length with "Hdim0_hist") as %?.
  wp_apply wp_Assert_decide; [word|].

  wp_apply wp_ref_of_zero; [done|].
  iIntros "* Hptr2_last".
  wp_pures. wp_bind (If _ _ _).
  wp_apply (wp_wand _ _ _
    (λ _,
    ∃ (ptr_entry : loc),
    "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
    "Hptr2_last" ∷ l ↦[ptrT] #ptr_entry ∗
    "#Hentry" ∷ is_histEntry ptr_entry (mjoin $ last hist)
    )%I
    with "[Hptr2_last Hsl_hist]"
  ).
  { wp_if_destruct.
    - wp_apply wp_allocStruct; [val_ty|].
      iIntros "* Hptr_last".
      wp_store.

      iPersist "Hptr_last".
      iDestruct (struct_fields_split with "Hptr_last") as "{Hptr_last} #H".
      iNamed "H".
      destruct hist. 2: { simpl in *. word. }
      by iFrame "∗#".
    - wp_pures.
      destruct (last hist) eqn:Hlast_hist.
      2: { apply last_None in Hlast_hist. simplify_eq/=. word. }
      rewrite last_lookup in Hlast_hist.
      iDestruct (big_sepL2_lookup_2_some with "Hdim0_hist") as %[??]; [done|].
      iDestruct (big_sepL2_lookup with "Hdim0_hist") as "His_entry"; [done..|].
      replace (pred $ length hist) with
        (uint.nat (word.sub sl_hist.(Slice.sz) (W64 1))) in * by word.
      iDestruct (own_slice_small_read with "Hsl_hist") as "[Hsl_hist Hclose]".
      wp_apply (wp_SliceGet with "[$Hsl_hist]"); [done|].
      iIntros "Hsl_hist".
      iDestruct ("Hclose" with "Hsl_hist") as "Hsl_hist".
      wp_store.
      by iFrame "∗#". }

  iIntros "*". iNamed 1.
  wp_apply wp_ref_to; [val_ty|].
  iIntros "* Hptr_new_hist".
  wp_apply wp_ref_to; [val_ty|].
  iIntros "* Hptr_i".
  wp_apply (wp_forUpto
    (λ i,
    ∃ sl_hist' dim0_hist',
    "%Hlt_i" ∷ ⌜ Z.of_nat $ length hist <= uint.Z i ⌝ ∗
    "Hptr2_last" ∷ l ↦[ptrT] #ptr_entry ∗
    "Hptr_new_hist" ∷ l0 ↦[slice.T ptrT] (slice_val sl_hist') ∗
    "Hsl_hist" ∷ own_slice sl_hist' ptrT (DfracOwn 1) dim0_hist' ∗
    "#Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist';(hist ++
      replicate (uint.nat i - length hist) (mjoin (last hist))),
      is_histEntry p o)
    )%I
    with "[] [$Hptr_i $Hptr2_last $Hptr_new_hist $Hsl_hist]"
  ); [word|..].
  2: { replace (_ - _)%nat with (0%nat) by word.
    list_simplifier. iFrame "#". word. }
  { iClear "% Hdim0_hist". iIntros (? Φ) "!> (H & Hptr_i & %) HΦ".
    iNamed "H". do 2 wp_load.
    wp_apply (wp_SliceAppend with "Hsl_hist").
    iIntros "* Hsl_hist". wp_store.
    iApply "HΦ". iFrame.
    remember (_ - _)%nat as prev_len.
    replace (_ - _)%nat with (S prev_len) by word.
    rewrite replicate_S_end (assoc (++)).
    iFrame "#". iIntros "!>". iSplit; [word|done]. }
  iClear "#". iIntros "[H _]". iNamed "H".
  wp_load.
  iApply "HΦ". by iFrame "∗#".
Qed.

End proof.
