From New.proof Require Import proof_prelude.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.proof.github_com.sanjit_bhat.pav Require Import
  hashchain ktcore merkle safemarshal.

Module sigpred.

Module cfg.
Record t :=
  mk {
    vrf: gname;
    startEp: gname;
    links: gname;
  }.
End cfg.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition vrf_pred γ enc : iProp Σ :=
  ∃ vrfPk,
  "%Henc" ∷ ⌜enc = ktcore.VrfSig.pure_enc (ktcore.VrfSig.mk' (W8 ktcore.VrfSigTag) vrfPk)⌝ ∗
  "%Hvalid" ∷ ⌜safemarshal.Slice1D.valid vrfPk⌝ ∗

  "#Hshot" ∷ ghost_var γ (□) vrfPk.

Definition links_inv links : iProp Σ :=
  ∃ digs cut maps,
  (* [offset] is the number of digs prior to links starting. *)
  let offset := (length digs - length links)%nat in
  "#Hlinks" ∷ ([∗ list] idx ↦ link ∈ links,
    let n_digs := (offset + idx + 1)%nat in
    "#His_link" ∷ hashchain.is_chain (take n_digs digs) cut link n_digs) ∗
  "%Hlt_links" ∷ ⌜length links ≤ length digs⌝ ∗
  "#Hmaps" ∷ ([∗ list] idx ↦ _;m ∈ links;maps,
    ∃ dig,
    "%Hlook_dig" ∷ ⌜digs !! (offset + idx)%nat = Some dig⌝ ∗
    "#His_map" ∷ merkle.is_map m dig) ∗
  "%Hmono" ∷ ⌜∀ i m0 m1,
    maps !! i = Some m0 →
    maps !! (S i) = Some m1 →
    m0 ⊆ m1⌝.

Definition links_pred γstartEp γlinks enc : iProp Σ :=
  (* [links] are all audited. they start from [startEp]. *)
  ∃ ep link startEp links,
  "%Henc" ∷ ⌜enc = ktcore.LinkSig.pure_enc (ktcore.LinkSig.mk' (W8 ktcore.LinkSigTag) ep link)⌝ ∗
  "%Hvalid" ∷ ⌜safemarshal.Slice1D.valid link⌝ ∗

  (* externalize startEp so that users agree on the epochs associated with links. *)
  "#Hshot" ∷ ghost_var γstartEp (□) startEp ∗
  "#Hlb" ∷ mono_list_lb_own γlinks links ∗
  "%Hlook" ∷ ⌜links !! (uint.nat ep - uint.nat startEp)%nat = Some link⌝ ∗
  "#Hinv" ∷ links_inv links.

Definition pred γ enc : iProp Σ :=
  vrf_pred γ.(cfg.vrf) enc ∨ links_pred γ.(cfg.startEp) γ.(cfg.links) enc.

#[global] Instance pred_pers γ e : Persistent (pred γ e).
Proof. apply _. Qed.

End proof.
End sigpred.
