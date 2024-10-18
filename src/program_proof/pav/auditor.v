From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import core cryptoffi merkle serde server.

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
Record t :=
  mk {
    mu: loc;
    γ: gname;
    serv_γ: gname;
    sl_sk: Slice.t;
    serv_pk: list w8;
  }.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ pk sl_serv_pk key_maps ptr_map last_map sl_hist ptrs_hist hist,
  (* keys. *)
  "#Hptr_sk" ∷ ptr ↦[Auditor :: "sk"]□ (slice_val obj.(sl_sk)) ∗
  "Hown_sk" ∷ own_sk obj.(sl_sk) pk (adtr_sigpred obj.(γ)) ∗
  "#Hptr_servPk" ∷ ptr ↦[Auditor :: "servSigPk"]□ (slice_val sl_serv_pk) ∗
  "#Hsl_servPk" ∷ own_slice_small sl_serv_pk byteT DfracDiscarded obj.(serv_pk) ∗
  "#His_servPk" ∷ is_pk obj.(serv_pk) (serv_sigpred obj.(serv_γ)) ∗
  (* maps. *)
  "Hmaps" ∷ mono_list_auth_own obj.(γ) 1 key_maps ∗
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

Definition valid (ptr : loc) (obj : t) : iProp Σ :=
  "#Hptr_mu" ∷ ptr ↦[Auditor :: "mu"]□ #obj.(mu) ∗
  "#HmuR" ∷ is_lock nroot #obj.(mu) (own ptr obj).
End defs.
End Auditor.

Section specs.
Context `{!heapGS Σ, !pavG Σ}.
Lemma wp_newAuditor sl_servPk (servPk : list w8) :
  {{{
    "#Hsl_servPk" ∷ own_slice_small sl_servPk byteT DfracDiscarded servPk
  }}}
  newAuditor (slice_val sl_servPk)
  {{{
    ptr_adtr (adtr : Auditor.t) sl_adtrPk adtrPk adtr_γ, RET (#ptr_adtr, slice_val sl_adtrPk);
    "Hown_adtr" ∷ Auditor.own ptr_adtr adtr ∗
    "#Hsl_adtrPk" ∷ own_slice_small sl_adtrPk byteT DfracDiscarded adtrPk ∗
    "#His_adtrPk" ∷ is_pk adtrPk (adtr_sigpred adtr_γ)
  }}}.
Proof. Admitted.
End specs.
