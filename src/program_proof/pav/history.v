From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import client core.

Section defs.
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

Definition get_lat (phys : list map_val_ty) (ep : w64) : lat_val_ty :=
  last $ filter (λ x, uint.Z x.1 ≤ uint.Z ep) phys.

Definition phys_logic_reln phys (logic : list lat_val_ty) :=
  (∀ (ep : w64) lat, logic !! uint.nat ep = Some lat → lat = get_lat phys ep).

(* know_hist_cliG ties together phys_hist and logic_hist as two different
hist repr's, either of which may be convenient at any given time. *)
Definition know_hist_cliG cli_γ (uid : w64) (phys_hist : list map_val_ty) (logic_hist : list lat_val_ty) : iProp Σ :=
  ⌜ phys_logic_reln phys_hist logic_hist ⌝ ∗
  ([∗ list] ep ↦ lat ∈ logic_hist, know_hist_val_cliG cli_γ uid (W64 ep) lat).

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

Definition msv_final (adtr_γ : gname) (ep uid : w64) (lat : lat_val_ty) : iProp Σ.
Admitted.
End defs.

Section derived.
Context `{!heapGS Σ, !pavG Σ}.

Lemma hist_extend_selfmon logic_hist ep cli_γ uid phys_hist :
  (uint.Z $ length logic_hist) - 1 ≤ uint.nat ep →
  ("#Hknow_hist" ∷ know_hist_cliG cli_γ uid phys_hist logic_hist ∗
  "#His_bound" ∷ is_my_bound cli_γ uid (W64 $ length phys_hist) ep) -∗
  ∃ new_hist,
  "%Hlen_hist" ∷ ⌜ length new_hist = S $ uint.nat ep ⌝ ∗
  "Hknow_hist" ∷ know_hist_cliG cli_γ uid phys_hist new_hist.
Proof. Admitted.

Lemma hist_audit_msv ep lat logic_hist aud_ep cli_γ uid phys_hist adtr_γ :
  logic_hist !! uint.nat ep = Some lat →
  length logic_hist ≤ aud_ep →
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
