From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From iris.algebra Require Import mono_nat.
From Perennial.program_proof.memkv Require Import rpc_spec.
From Perennial.program_proof Require Import marshal_proof.

Section interface.

Context `{inG Σ mono_natUR}.
Context `{HPRE: !gooseGlobalGS Σ}.

Definition counter_lb γ (x:nat) : iProp Σ := own γ (◯MN x).
Definition counter_own γ (x:nat) : iProp Σ := own γ (●MN x).

Definition FAISpec γ (reqData:list u8) (Φ:list u8 → iProp Σ) : iProp Σ :=
  □(
      ∀ (x:nat), counter_own γ x ={⊤}=∗ counter_own γ (x + 1) ∗
                                    (∀ l, ⌜has_encoding l [EncUInt64 x]⌝ -∗ Φ l)
    )
.

End interface.
