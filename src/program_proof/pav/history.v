From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import client core.

Section core_iprop.
Context `{!heapGS Σ, !pavG Σ}.

(* TODO: maybe only cliG version needed. not pure or adtrG. *)
Definition know_hist_val_cliG cli_γ (uid ep : w64) (lat : lat_val_ty) : iProp Σ :=
  ∃ vals,
  "%Hbound_vals" ∷ ⌜ length vals < 2^64 ⌝ ∗
  "%Hlook_lat" ∷ ⌜ last vals = lat ⌝ ∗
  (* prior vers exist in prior or this map. *)
  "#Hhist" ∷ ([∗ list] ver ↦ '(prior, pk) ∈ vals,
    (∃ dig m_γ comm,
    "%Hlt_prior" ∷ ⌜ uint.Z prior ≤ uint.Z ep ⌝ ∗
    "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat prior) (Some (dig, m_γ)) ∗
    "#Hin_prior" ∷ (uid, W64 ver) ↪[m_γ]□ Some (prior, comm) ∗
    "#Hcomm" ∷ is_comm pk comm)) ∗
  ( (* next ver doesn't exist in this or later map. *)
    "Hnin_nextver" ∷ (∃ (bound : w64) dig m_γ,
      "%Hgte_bound" ∷ ⌜ uint.Z ep ≤ uint.Z bound ⌝ ∗
      "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat bound) (Some (dig, m_γ)) ∗
      "#Hin_bound" ∷ (uid, W64 $ length vals) ↪[m_γ] None)
    ∨
    (* next ver exists in later map. *)
    "Hin_nextver" ∷ (∃ (bound : w64) dig m_γ comm,
      "%Hgt_bound" ∷ ⌜ uint.Z ep < uint.Z bound ⌝ ∗
      "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat bound) (Some (dig, m_γ)) ∗
      "#Hin_bound" ∷ (uid, W64 $ length vals) ↪[m_γ] Some (bound, comm))).

Definition know_hist_cliG cli_γ (uid : w64) (hist : list lat_val_ty) : iProp Σ :=
  ([∗ list] ep ↦ lat ∈ hist, know_hist_val_cliG cli_γ uid (W64 ep) lat).

End core_iprop.

Section HistEntry.
Context `{!heapGS Σ}.
Definition own_HistEntry (ptr : loc) (obj : map_val_ty) : iProp Σ :=
  ∃ sl_HistVal,
  "Hptr_Epoch" ∷ ptr ↦[HistEntry :: "Epoch"] #obj.1 ∗
  "Hptr_HistVal" ∷ ptr ↦[HistEntry :: "HistVal"] (slice_val sl_HistVal) ∗
  "#Hsl_HistVal" ∷ own_slice_small sl_HistVal byteT DfracDiscarded obj.2.
End HistEntry.

Section hist.
Context `{!heapGS Σ, !pavG Σ}.

Definition get_lat (phys : list map_val_ty) (ep : w64) : lat_val_ty :=
  last $ filter (λ x, uint.Z x.1 ≤ uint.Z ep) phys.

Definition phys_logic_reln phys (logic : list lat_val_ty) :=
  (∀ (ep : w64) lat, logic !! uint.nat ep = Some lat → lat = get_lat phys ep).

Definition own_hist cli_γ uid sl_hist phys_hist : iProp Σ :=
  ∃ dim0_hist logic_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;phys_hist, own_HistEntry p o) ∗
  "%Hlogic_reln" ∷ ⌜ phys_logic_reln phys_hist logic_hist ⌝ ∗
  "#Hknow_hist" ∷ know_hist_cliG cli_γ uid logic_hist.
End hist.

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
