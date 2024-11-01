From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import client core.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition lat_pk_comm_reln (lat_pk : lat_val_ty) (lat_comm : lat_opaque_val_ty) : iProp Σ :=
  match lat_pk, lat_comm with
  | Some (ep0, pk), Some (ep1, comm) => ⌜ ep0 = ep1 ⌝ ∗ is_comm pk comm
  | None, None => True
  | _, _ => False
  end.

Definition msv_final (adtr_γ : gname) (ep uid : w64) (lat : lat_val_ty) : iProp Σ :=
  ∃ (m : adtr_map_ty) (vals : list opaque_map_val_ty),
  "#Hcomm_reln" ∷ lat_pk_comm_reln lat (last vals) ∗
  "#Hmap" ∷ mono_list_idx_own adtr_γ (uint.nat ep) m ∗
  "#Hhist" ∷ ([∗ list] ver ↦ val ∈ vals,
    ∃ label,
    "#His_label" ∷ is_vrf uid (W64 ver) label ∗
    "%Hin_map" ∷ ⌜ m !! label = Some val ⌝) ∗
  "#Hbound" ∷
    (∃ label,
    "#His_label" ∷ is_vrf uid (W64 $ length vals) label ∗
    "%Hnin_map" ∷ ⌜ m !! label = None ⌝).

Definition know_hist_val_cliG cli_γ (uid ep : w64) (hist : list map_val_ty) : iProp Σ :=
  let vals := filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist in
  (* prior vers exist in prior or this map. *)
  "#Hhist" ∷ ([∗ list] ver ↦ '(prior, pk) ∈ vals,
    (∃ dig m_γ comm,
    "%Hlt_prior" ∷ ⌜ uint.Z prior ≤ uint.Z ep ⌝ ∗
    "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat prior) (Some (dig, m_γ)) ∗
    "#Hcomm" ∷ is_comm pk comm ∗
    "#Hin_prior" ∷ (uid, W64 ver) ↪[m_γ]□ Some (prior, comm))) ∗
  ( (* next ver doesn't exist in this or later map. *)
    "Hnin_nextver" ∷ (∃ (bound : w64) dig m_γ,
      "%Hgte_bound" ∷ ⌜ uint.Z ep ≤ uint.Z bound ⌝ ∗
      "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat bound) (Some (dig, m_γ)) ∗
      "#Hin_bound" ∷ (uid, W64 $ length vals) ↪[m_γ]□ None)
    ∨
    (* next ver exists in later map. *)
    "Hin_nextver" ∷ (∃ (bound : w64) dig m_γ comm,
      "%Hgt_bound" ∷ ⌜ uint.Z ep < uint.Z bound ⌝ ∗
      "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat bound) (Some (dig, m_γ)) ∗
      "#Hin_bound" ∷ (uid, W64 $ length vals) ↪[m_γ]□ Some (bound, comm))).

Definition know_hist_cliG cli_γ (uid : w64) (hist : list map_val_ty) (bound : w64) : iProp Σ :=
  "%Hok_bound" ∷ ⌜ ∀ ep val, hist !! ep = Some val → uint.Z val.1 ≤ uint.Z bound ⌝ ∗
  "#Hknow_vals" ∷ ∀ (ep : w64), ⌜ uint.Z ep ≤ uint.Z bound ⌝ -∗ know_hist_val_cliG cli_γ uid ep hist.

Definition own_HistEntry (ptr : loc) (obj : map_val_ty) : iProp Σ :=
  ∃ sl_HistVal,
  "Hptr_Epoch" ∷ ptr ↦[HistEntry :: "Epoch"] #obj.1 ∗
  "Hptr_HistVal" ∷ ptr ↦[HistEntry :: "HistVal"] (slice_val sl_HistVal) ∗
  "#Hsl_HistVal" ∷ own_slice_small sl_HistVal byteT DfracDiscarded obj.2.

Definition own_hist cli_γ uid sl_hist hist bound : iProp Σ :=
  ∃ dim0_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;hist, own_HistEntry p o) ∗
  "#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist bound.
End defs.

Section derived.
Context `{!heapGS Σ, !pavG Σ}.

(* TODO: upstream. *)
Lemma list_filter_iff_strong {A} (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  (∀ i x, l !! i = Some x → (P1 x ↔ P2 x)) →
  filter P1 l = filter P2 l.
Proof.
  intros HPiff. induction l as [|a l IH]; [done|].
  opose proof (HPiff 0%nat a _) as ?; [done|].
  ospecialize (IH _). { intros i x ?. by ospecialize (HPiff (S i) x _). }
  destruct (decide (P1 a)).
  - rewrite !filter_cons_True; [|by naive_solver..]. by rewrite IH.
  - rewrite !filter_cons_False; [|by naive_solver..]. by rewrite IH.
Qed.

(* TODO: upstream. *)
Lemma list_filter_all {A} (P : A → Prop)
    `{!∀ x, Decision (P x)} (l : list A) :
  (∀ i x, l !! i = Some x → P x) →
  filter P l = l.
Proof.
  intros HP. induction l as [|a l IH]; [done|].
  opose proof (HP 0%nat a _) as ?; [done|].
  ospecialize (IH _). { intros i x ?. by ospecialize (HP (S i) x _). }
  rewrite filter_cons_True; [|done]. by rewrite IH.
Qed.

Lemma hist_extend_selfmon cli_γ uid hist bound new_bound :
  uint.Z bound ≤ uint.Z new_bound →
  ("#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist bound ∗
  "#His_bound" ∷ is_my_bound cli_γ uid (W64 $ length hist) new_bound) -∗
  "#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist new_bound.
Proof.
  intros ?. iNamed 1. iNamed "Hknow_hist". iSplit.
  { iIntros (?? Hlook). iPureIntro. specialize (Hok_bound _ _ Hlook). word. }
  iIntros (ep ?). destruct (decide (uint.Z ep ≤ uint.Z bound)).
  { by iApply "Hknow_vals". }
  iSpecialize ("Hknow_vals" $! bound with "[]"). { iPureIntro. lia. }
  iSplit.
  - iNamed "Hknow_vals".
    rewrite (list_filter_iff_strong
      (λ x, uint.Z x.1 ≤ uint.Z ep)
      (λ x, uint.Z x.1 ≤ uint.Z bound) hist); [|naive_solver word].
    iApply (big_sepL_impl with "Hhist"). iIntros (?[??]) "!> %". iNamed 1.
    iFrame "#". iPureIntro. word.
  - iClear "Hknow_vals". iLeft.
    rewrite list_filter_all; last first.
    { intros ?? Hlook. ospecialize (Hok_bound _ _ Hlook). word. }
    iNamed "His_bound". iFrame "#". iPureIntro. word.
Qed.

Definition get_lat (hist : list map_val_ty) (ep : w64) : lat_val_ty :=
  last $ filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist.

Lemma hist_audit_msv cli_γ uid hist bound adtr_γ aud_ep (ep : w64) :
  uint.Z ep ≤ uint.Z bound →
  uint.Z bound < uint.Z aud_ep →
  ("#Hknow_hist" ∷ know_hist_cliG cli_γ uid hist bound ∗
  "#His_audit" ∷ is_audit cli_γ adtr_γ aud_ep) -∗
  "#Hmsv" ∷ msv_final adtr_γ ep uid (get_lat hist ep).
Proof.
  intros ??. iNamed 1.
  rewrite /msv_final.
  iNamed "Hknow_hist".
  iSpecialize ("Hknow_vals" $! ep with "[//]"). iNamed "Hknow_vals".
  iNamed "His_audit".
  rewrite /is_audit.
Admitted.

End derived.

Section wps.
Context `{!heapGS Σ, !pavG Σ}.

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
