From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import client core.

Section hist.
(* logical history. *)
Context `{!heapGS Σ, !pavG Σ}.

(* TODO: add inv that says every key in cli submap will have a vrf. *)
Definition know_hist_val_cliG cli_γ (uid ep : w64) (hist : list map_val_ty) (valid : w64) : iProp Σ :=
  ∃ (vals : list opaque_map_val_ty),
  "#Hpk_comm_reln" ∷
    ([∗ list] pk_val;comm_val ∈ filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist;vals,
    "%Heq_ep" ∷ ⌜ pk_val.1 = comm_val.1 ⌝ ∗
    "#Hcomm" ∷ is_comm pk_val.2 comm_val.2) ∗
  (* prior vers exist in prior or this map. *)
  "#Hhist" ∷
    ([∗ list] ver ↦ '(prior, comm) ∈ vals,
    ∃ dig m_γ label,
    "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat prior) (Some (dig, m_γ)) ∗
    "#Hin_prior" ∷ (uid, W64 ver) ↪[m_γ]□ Some (prior, comm) ∗
    "#His_label" ∷ is_vrf uid (W64 ver) label) ∗
  "#Hbound" ∷
    (∃ (bound : w64) dig m_γ label,
    "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat bound) (Some (dig, m_γ)) ∗
    "#His_label" ∷ is_vrf uid (W64 $ length vals) label ∗
    "%Hlt_bound" ∷ ⌜ uint.Z bound ≤ uint.Z valid ⌝ ∗
    (* next ver doesn't exist in this or later map. *)
    (("%Hgt_bound" ∷ ⌜ uint.Z ep ≤ uint.Z bound ⌝ ∗
    "#Hin_bound" ∷ (uid, W64 $ length vals) ↪[m_γ]□ None)
    ∨
    (* next ver exists in later map. *)
    (∃ comm,
    "%Hgt_bound" ∷ ⌜ uint.Z ep < uint.Z bound ⌝ ∗
    "#Hin_bound" ∷ (uid, W64 $ length vals) ↪[m_γ]□ Some (bound, comm)))).

Definition know_hist_cliG cli_γ (uid : w64) (hist : list map_val_ty) (valid : w64) : iProp Σ :=
  "%Hhist_valid" ∷ ([∗ list] x ∈ hist, ⌜ uint.Z x.1 ≤ uint.Z valid ⌝) ∗
  "#Hknow_vals" ∷ (∀ (ep : w64), ⌜ uint.Z ep ≤ uint.Z valid ⌝ -∗
    know_hist_val_cliG cli_γ uid ep hist valid).

End hist.

Section hist_derived.
Context `{!heapGS Σ, !pavG Σ}.

Lemma hist_val_extend_valid γ uid ep hist valid new_valid :
  uint.Z valid ≤ uint.Z new_valid →
  know_hist_val_cliG γ uid ep hist valid -∗
  know_hist_val_cliG γ uid ep hist new_valid.
Proof.
  intros ?. iNamed 1. iNamed "Hbound". iExists vals. iFrame "#".
  iDestruct "Hbound" as "[Hbound|Hbound]"; iNamed "Hbound"; iPureIntro; word.
Qed.

Lemma hist_extend_selfmon cli_γ uid hist valid new_valid :
  uint.Z valid ≤ uint.Z new_valid →
  ("#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist valid ∗
  "#His_bound" ∷ is_my_bound cli_γ uid (W64 $ length hist) new_valid) -∗
  "#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist new_valid.
Proof.
  intros ?. iNamed 1. iNamed "Hknow_hist". iSplit.
  { iApply big_sepL_forall. iPureIntro. simpl. intros * Hlook.
    specialize (Hhist_valid _ _ Hlook). word. }
  iIntros (ep ?). destruct (decide (uint.Z ep ≤ uint.Z valid)).
  { iSpecialize ("Hknow_vals" $! ep with "[]"). { iPureIntro. word. }
    iApply (hist_val_extend_valid with "Hknow_vals"). word. }
  iSpecialize ("Hknow_vals" $! valid with "[]"). { iPureIntro. lia. }
  iNamed "Hknow_vals". iExists vals. iSplit; [|iSplit].
  - rewrite (list_filter_iff_strong
      (λ x, uint.Z x.1 ≤ uint.Z ep)
      (λ x, uint.Z x.1 ≤ uint.Z valid) hist); last first.
    { intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook).
      naive_solver word. }
    iFrame "#".
  - iFrame "#".
  - iClear "Hhist Hbound".
    iDestruct (big_sepL2_length with "Hpk_comm_reln") as %Hlen_vals.
    rewrite list_filter_all in Hlen_vals; last first.
    { intros ?[??] Hlook. ospecialize (Hhist_valid _ _ Hlook). simpl in *. word. }
    iNamed "His_bound". rewrite Hlen_vals. by iFrame "#%".
Qed.

Definition get_lat (hist : list map_val_ty) (ep : w64) : lat_val_ty :=
  last $ filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist.

Lemma hist_audit_msv cli_γ uid hist valid adtr_γ aud_ep (ep : w64) :
  uint.Z ep ≤ uint.Z valid →
  uint.Z valid < uint.Z aud_ep →
  ("#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist valid ∗
  "#His_audit" ∷ is_audit cli_γ adtr_γ aud_ep) -∗
  "#Hmsv" ∷ msv adtr_γ ep uid (get_lat hist ep).
Proof.
  intros ??. iNamed 1.
  iNamed "Hknow_hist". iSpecialize ("Hknow_vals" $! ep with "[//]").
  iNamed "His_audit". list_elem ms (uint.nat ep) as m.
  iDestruct (mono_list_idx_own_get _ _ Hm_lookup with "Hadtr_maps") as "Hadtr_map".
  iFrame "Hadtr_map". iNamed "Hknow_vals". iExists vals. iSplit.
  { iClear "Hhist Hbound".
    iDestruct (big_sepL2_length with "Hpk_comm_reln") as %Hlen_vals.
    destruct (get_lat hist ep) as [[??]|] eqn:Hlat_pk, (last vals) as [[??]|]
      eqn:Hlat_comm; [|exfalso..|done];
      rewrite /get_lat last_lookup in Hlat_pk; rewrite last_lookup in Hlat_comm.
    + rewrite Hlen_vals in Hlat_pk.
      iDestruct (big_sepL2_lookup with "Hpk_comm_reln") as "?"; [exact Hlat_pk|exact Hlat_comm|].
      iFrame "#".
    + apply lookup_lt_Some in Hlat_pk. apply lookup_ge_None in Hlat_comm. lia.
    + apply lookup_ge_None in Hlat_pk. apply lookup_lt_Some in Hlat_comm. lia. }
  iNamedSuffix "Hbound" "_bnd". iFrame "#". iSplit.
  - iClear "Hbound". iApply (big_sepL_impl with "Hhist").
    iIntros (?[prior ?]) "!> %Hlook_vals". iNamed 1. iFrame "#".
    (* tedious: need prior ep < adtr_bound to get prior adtr map for map transf.
    get that by tracing val back to filtered hist and using hist validity. *)
    iDestruct (big_sepL2_lookup_2_some with "Hpk_comm_reln") as %[[??] Hlook_hist]; [exact Hlook_vals|].
    iDestruct (big_sepL2_lookup with "Hpk_comm_reln") as "Htmp"; [exact Hlook_hist|exact Hlook_vals|].
    iNamed "Htmp". opose proof (proj1 (elem_of_list_filter _ _ _) _) as [? _].
    { eapply elem_of_list_lookup. eauto using Hlook_hist. }
    simpl in *. list_elem ms (uint.nat prior) as mprior.
    iDestruct ("Hmap_transf" with "[$Hsubmap $Hin_prior $His_label]") as "H".
    { iPureIntro. exact Hmprior_lookup. }
    iNamed "H". iPureIntro.
    opose proof ((proj1 Hinv_adtr) _ _ _ _ Hmprior_lookup Hm_lookup _); [word|].
    by eapply lookup_weaken.
  - iClear "Hhist". list_elem ms (uint.nat bound) as mbound.
    iDestruct "Hbound" as "[Hbound|Hbound]"; iNamed "Hbound".
    + iSpecialize ("Hmap_transf" with "[$Hsubmap_bnd $Hin_bound $His_label_bnd]").
      { iPureIntro. exact Hmbound_lookup. }
      iNamed "Hmap_transf". iPureIntro.
      opose proof ((proj1 Hinv_adtr) _ _ _ _ Hm_lookup Hmbound_lookup _); [word|].
      by eapply lookup_weaken_None.
    + iSpecialize ("Hmap_transf" with "[$Hsubmap_bnd $Hin_bound $His_label_bnd]").
      { iPureIntro. exact Hmbound_lookup. }
      iNamed "Hmap_transf". iPureIntro.
      destruct (decide $ is_Some $ m !! label) as [[? Hlook_mkey]|]; last first.
      { by eapply eq_None_not_Some. }
      opose proof ((proj1 Hinv_adtr) _ _ _ _ Hm_lookup Hmbound_lookup _); [word|].
      opose proof (lookup_weaken _ _ _ _ Hlook_mkey _); [done|]. simplify_eq/=.
      opose proof ((proj2 Hinv_adtr) _ _ _ _ _ Hm_lookup Hlook_mkey) as ?. word.
Qed.

End hist_derived.

Section wps.
Context `{!heapGS Σ, !pavG Σ}.

Definition own_HistEntry (ptr : loc) (obj : map_val_ty) : iProp Σ :=
  ∃ sl_HistVal,
  "Hptr_Epoch" ∷ ptr ↦[HistEntry :: "Epoch"] #obj.1 ∗
  "Hptr_HistVal" ∷ ptr ↦[HistEntry :: "HistVal"] (slice_val sl_HistVal) ∗
  "#Hsl_HistVal" ∷ own_slice_small sl_HistVal byteT DfracDiscarded obj.2.

Definition own_hist cli_γ uid sl_hist hist valid : iProp Σ :=
  ∃ dim0_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;hist, own_HistEntry p o) ∗
  "#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist valid.

Lemma wp_put_hist cli_γ uid sl_hist hist ptr_e e :
  match last hist with
  | None => True
  | Some lat => uint.Z lat.1 < uint.Z e.1
  end →
  {{{
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist hist ∗
    "Hown_entry" ∷ own_HistEntry ptr_e e ∗
    "#His_key" ∷ is_my_key cli_γ uid (W64 $ length hist) e.1 e.2
  }}}
  SliceAppend ptrT (slice_val sl_hist) #ptr_e
  {{{
    sl_hist', RET (slice_val sl_hist');
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist' (hist ++ [e]) ∗
    "Hown_entry" ∷ own_HistEntry ptr_e e
  }}}.
Proof. Admitted.

Lemma wp_GetHist cli_γ uid sl_hist hist (ep : w64) :
  {{{
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist hist
  }}}
  GetHist (slice_val sl_hist) #ep
  {{{
    (is_reg : bool) sl_pk pk, RET (#is_reg, slice_val sl_pk);
    "Hown_hist" ∷ own_hist cli_γ uid sl_hist hist ∗
    "#Hsl_pk" ∷ own_slice_small sl_pk byteT DfracDiscarded pk ∗
    "%Heq_lat" ∷
      ⌜ match get_lat hist ep with
        | None => is_reg = false
        | Some lat => is_reg = true ∧ pk = lat.2
        end ⌝
  }}}.
Proof. Admitted.

End wps.
