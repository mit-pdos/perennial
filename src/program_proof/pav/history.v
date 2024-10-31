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

Definition know_hist_val_cliG cli_γ (uid ep : w64) (lat : lat_val_ty) : iProp Σ :=
  ∃ (vals : list opaque_map_val_ty),
  "%Hbound_vals" ∷ ⌜ length vals < 2^64 ⌝ ∗
  "#Hcomm_reln" ∷ lat_pk_comm_reln lat (last vals) ∗
  (* prior vers exist in prior or this map. *)
  "#Hhist" ∷ ([∗ list] ver ↦ '(prior, comm) ∈ vals,
    (∃ dig m_γ,
    "%Hlt_prior" ∷ ⌜ uint.Z prior ≤ uint.Z ep ⌝ ∗
    "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat prior) (Some (dig, m_γ)) ∗
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

Definition get_lat (phys : list map_val_ty) (ep : w64) : lat_val_ty :=
  last $ filter (λ x, uint.Z x.1 ≤ uint.Z ep) phys.

Definition phys_logic_reln phys (logic : list lat_val_ty) :=
  (∀ (ep : w64) lat, logic !! uint.nat ep = Some lat → lat = get_lat phys ep).

(* know_hist_cliG ties together phys_hist and logic_hist as two different
hist repr's, either of which may be convenient at a given time. *)
Definition know_hist_cliG cli_γ (uid : w64) (phys_hist : list map_val_ty) (logic_hist : list lat_val_ty) : iProp Σ :=
  "%Hphys_log" ∷ ⌜ phys_logic_reln phys_hist logic_hist ⌝ ∗
  "#Hknow_vals" ∷ ([∗ list] ep ↦ lat ∈ logic_hist, know_hist_val_cliG cli_γ uid (W64 ep) lat).

Definition own_HistEntry (ptr : loc) (obj : map_val_ty) : iProp Σ :=
  ∃ sl_HistVal,
  "Hptr_Epoch" ∷ ptr ↦[HistEntry :: "Epoch"] #obj.1 ∗
  "Hptr_HistVal" ∷ ptr ↦[HistEntry :: "HistVal"] (slice_val sl_HistVal) ∗
  "#Hsl_HistVal" ∷ own_slice_small sl_HistVal byteT DfracDiscarded obj.2.

Definition own_hist cli_γ uid sl_hist phys_hist : iProp Σ :=
  ∃ dim0_hist logic_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;phys_hist, own_HistEntry p o) ∗
  "#Hknow_hist" ∷ know_hist_cliG cli_γ uid phys_hist logic_hist.
End defs.

Section derived.
Context `{!heapGS Σ, !pavG Σ}.

Lemma hist_extend_selfmon logic_hist (ep : w64) cli_γ uid phys_hist :
  length logic_hist ≤ S $ uint.nat ep →
  ("#Hknow_hist" ∷ know_hist_cliG cli_γ uid phys_hist logic_hist ∗
  "#His_bound" ∷ is_my_bound cli_γ uid (W64 $ length phys_hist) ep) -∗
  ∃ new_hist,
  "%Hlen_hist" ∷ ⌜ length new_hist = S $ uint.nat ep ⌝ ∗
  "Hknow_hist" ∷ know_hist_cliG cli_γ uid phys_hist new_hist.
Proof.
  intros Hlen_hist. iNamed 1.
  iExists (logic_hist ++ (replicate ((S $ uint.nat ep) - length logic_hist) (mjoin $ last logic_hist))).
  iSplit.
  { iPureIntro. rewrite app_length length_replicate. lia. }
  iSplit; [admit|].
  iNamed "Hknow_hist". iFrame "#".
  iApply big_sepL_forall. iIntros "* %Hlook_repl".
  apply lookup_replicate in Hlook_repl as [-> ?].
  destruct (last logic_hist) eqn:Hlook_last; simpl.
  (* if some last elem, use that for hist. *)
  - rewrite last_lookup in Hlook_last.
    iDestruct (big_sepL_lookup with "Hknow_vals") as "Hknow_last"; [exact Hlook_last|].
    iDestruct "Hknow_last" as (vals) "Hknow_last". iNamed "Hknow_last".
    iExists vals. iFrame "#%". iSplit.
    + iApply (big_sepL_impl with "Hhist"). iIntros (?[??]) "!> %". iNamed 1.
      iFrame "#". iPureIntro. word.
    + iClear "Hhist Hknow_last". iNamed "His_bound". iLeft. iFrame "#".
      (* TODO: issue relating length phys_hist with length vals. *)
Admitted.

Lemma hist_audit_msv (ep aud_ep : w64) lat logic_hist cli_γ uid phys_hist adtr_γ :
  logic_hist !! uint.nat ep = Some lat →
  Z.of_nat $ length logic_hist ≤ uint.Z aud_ep →
  ("#Hknow_hist" ∷ know_hist_cliG cli_γ uid phys_hist logic_hist ∗
  "#His_audit" ∷ is_audit cli_γ adtr_γ aud_ep) -∗
  "#Hmsv" ∷ msv_final adtr_γ ep uid lat.
Proof. Admitted.

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
