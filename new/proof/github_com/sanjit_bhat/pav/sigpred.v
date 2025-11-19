From New.proof Require Import proof_prelude.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.proof.github_com.sanjit_bhat.pav Require Import
  hashchain ktcore merkle safemarshal.

Module sigpred.

Module γs.
Record t :=
  mk {
    vrf: gname;
    chain: gname;
  }.
End γs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition vrf_pred γ enc : iProp Σ :=
  ∃ vrfPk,
  "%Henc" ∷ ⌜enc = ktcore.VrfSig.pure_enc (ktcore.VrfSig.mk' (W8 ktcore.VrfSigTag) vrfPk)⌝ ∗
  "%Hvalid" ∷ ⌜safemarshal.Slice1D.valid vrfPk⌝ ∗

  "#Hshot" ∷ ghost_var γ (□) vrfPk.

(* TODO: figure out what to do for auditors who:
(1) don't have digs down to ep 0, even with inversion.
(2) have only checked monotonicity from an ep.
(3) might have inverted down to Some cut. *)
Definition chain_inv chain : iProp Σ :=
  "#Hdig_map" ∷ ([∗ list] x ∈ chain,
    merkle.is_map x.(sigpred.entry.map) x.(sigpred.entry.dig)) ∗
  "%Hmono" ∷ ⌜∀ (x y : nat) cx cy,
    x ≤ y →
    chain !! x = Some cx →
    chain !! y = Some cy →
    cx.(sigpred.entry.map) ⊆ cy.(sigpred.entry.map)⌝ ∗
  "#Hdig_link" ∷ ([∗ list] k ↦ x ∈ chain,
    hashchain.is_chain (take (S k) ((λ y, y.(sigpred.entry.dig)) <$> chain))
      None x.(sigpred.entry.link) (S k)).

Definition chain_pred γ enc : iProp Σ :=
  ∃ ep link chain c,
  "%Henc" ∷ ⌜enc = ktcore.LinkSig.pure_enc (ktcore.LinkSig.mk' (W8 ktcore.LinkSigTag) ep link)⌝ ∗
  "%Hvalid" ∷ ⌜safemarshal.Slice1D.valid link⌝ ∗

  "#Hlb" ∷ mono_list_lb_own γ chain ∗
  "%Hlook" ∷ ⌜chain !! (sint.nat ep) = Some c⌝ ∗
  "%Heq" ∷ ⌜c.(sigpred.entry.link) = link⌝ ∗

  "#Hinv" ∷ chain_inv chain.

Definition pred γ enc : iProp Σ :=
  vrf_pred γ.(γs.vrf) enc ∨ chain_pred γ.(γs.chain) enc.

#[global] Instance pred_pers γ e : Persistent (pred γ e).
Proof. apply _. Qed.

End proof.
End sigpred.
