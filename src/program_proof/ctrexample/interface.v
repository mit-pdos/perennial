From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From iris.algebra Require Export mono_nat.
From Perennial.program_proof.grove_shared Require Import urpc_spec urpc_proof.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.base_logic Require Import lib.ghost_map lib.saved_spec.

Section interface.

Context `{!inG Σ mono_natUR}.

Definition localhost : chan := W64 53021371269120.

Definition counter_lb γ (x:nat) : iProp Σ := own γ (◯MN x).
Definition counter_own γ (x:nat) : iProp Σ := own γ (●MN x).

Context `{!urpcregG Σ}.

Context `{HPRE: !gooseGlobalGS Σ}.

(* HOCAP-style spec *)
Program Definition FAISpec (γ:gname) : savedSpecO Σ (list u8) (list u8) :=
  λ reqData, λne (Φ : list u8 -d> iPropO Σ),
  (
      ∀ (x:nat), counter_own γ x ={⊤}=∗ counter_own γ (x + 1) ∗
                                    (∀ l, ⌜has_encoding l [EncUInt64 x]⌝ -∗ Φ l)
    )%I
.
Next Obligation.
  solve_proper.
Defined.

(* TaDa-style spec *)
Program Definition FAISpec_tada (γ:gname) : savedSpecO Σ (list u8) (list u8) :=
  λ reqData, λne (Φ : list u8 -d> iPropO Σ),
  (
       ∃ Eo Ei,
       |={Eo,Ei}=> ∃ x, counter_own γ x ∗
                      (counter_own γ (x+1) ={Ei,Eo}=∗ (∀ l, ⌜has_encoding l [EncUInt64 x]⌝ -∗ Φ l))
    )%I
.

Next Obligation.
  solve_proper.
Defined.

Definition is_CtrServer_urpc γurpc_gn γ : iProp Σ :=
  is_urpc_spec_pred γurpc_gn localhost 0 (FAISpec γ) ∗
  is_urpc_dom (γurpc_gn) {[ W64 0 ]}.

End interface.
