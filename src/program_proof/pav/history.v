From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core.

Section core_iprop.
Context `{!heapGS Σ, !pavG Σ}.

Definition know_hist_val_cliG cli_γ (uid ep : w64) (lat : lat_val_ty) : iProp Σ :=
  let len_vals := match lat with None => 0%nat | Some (ver, val) => S $ uint.nat ver end in
  ∃ vals,
  "%Hlen_vals" ∷ ⌜ length vals = len_vals ⌝ ∗
  "%Hbound_vals" ∷ ⌜ length vals < 2^64 ⌝ ∗
  "%Hlook_lat" ∷ ⌜ last vals = snd <$> lat ⌝ ∗
  "#Hhist" ∷ ([∗ list] ver ↦ '(prior, pk) ∈ vals,
    (∃ dig m_γ comm,
    "%Hlt_prior" ∷ ⌜ uint.Z prior ≤ uint.Z ep ⌝ ∗
    "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat prior) (Some (dig, m_γ)) ∗
    "#Hin_prior" ∷ (uid, W64 ver) ↪[m_γ]□ Some (prior, comm) ∗
    "#Hcomm" ∷ is_comm pk comm)) ∗
  ( "Hnin_nextver" ∷ (∃ (bound : w64) dig m_γ,
      "%Hgte_bound" ∷ ⌜ uint.Z ep ≤ uint.Z bound ⌝ ∗
      "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat bound) (Some (dig, m_γ)) ∗
      "#Hin_bound" ∷ (uid, W64 $ length vals) ↪[m_γ] None)
    ∨
    "Hin_nextver" ∷ (∃ (bound : w64) dig m_γ comm,
      "%Hgt_bound" ∷ ⌜ uint.Z ep < uint.Z bound ⌝ ∗
      "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat bound) (Some (dig, m_γ)) ∗
      "#Hin_bound" ∷ (uid, W64 $ length vals) ↪[m_γ] Some (bound, comm))).

Definition know_hist_cliG cli_γ (uid : w64) (hist : list lat_val_ty) : iProp Σ :=
  ([∗ list] ep ↦ lat ∈ hist, know_hist_val_cliG cli_γ uid (W64 ep) lat).

End core_iprop.

Module HistEntry.
Record t :=
  mk {
    Epoch: w64;
    HistVal: list w8;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_HistVal,
  "Hptr_Epoch" ∷ ptr ↦[HistEntry :: "Epoch"] #obj.(Epoch) ∗
  "Hptr_HistVal" ∷ ptr ↦[HistEntry :: "HistVal"] (slice_val sl_HistVal) ∗
  "#Hsl_HistVal" ∷ own_slice_small sl_HistVal byteT DfracDiscarded obj.(HistVal).
End defs.
End HistEntry.

Section hist.
Context `{!heapGS Σ, !pavG Σ}.

Definition get_lat (phys : list HistEntry.t) (ep : w64) : lat_val_ty :=
  let hist := (filter (λ x, uint.Z x.(HistEntry.Epoch) ≤ uint.Z ep) phys) in
  (λ x, (W64 $ pred $ length hist, (x.(HistEntry.Epoch), x.(HistEntry.HistVal)))) <$> (last hist).

Definition phys_logic_reln (phys : list HistEntry.t) (logic : list lat_val_ty) :=
  (∀ (ep : w64) lat, logic !! uint.nat ep = Some lat → lat = get_lat phys ep) ∧
  length logic = match last phys with None => 0%nat | Some x => S $ uint.nat x.(HistEntry.Epoch) end.

Definition own_hist cli_γ uid sl_hist (hist : list HistEntry.t) : iProp Σ :=
  ∃ dim0_hist logic_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;hist, HistEntry.own p o) ∗
  "%Hlogic_reln" ∷ ⌜ phys_logic_reln hist logic_hist ⌝ ∗
  "#Hknow_hist" ∷ know_hist_cliG cli_γ uid logic_hist.
End hist.
