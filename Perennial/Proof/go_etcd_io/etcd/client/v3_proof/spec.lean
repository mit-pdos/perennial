/-
Port of `new/proof/go_etcd_io/etcd/client/v3_proof/spec.v`: interpreting the
etcd model's effects as separation-logic specifications.

Differences from Rocq:
* Rocq imports `v3_proof/base`, which needs `proof.context` (not yet ported);
  nothing from `base` is used here beyond the model and the prelude, so this
  file imports `model` directly.
* Rocq's `ghost_varG Σ EtcdState.t` becomes `[allG GF] [Pos.Countable EtcdState.t]`
  (Lean's `ghost_var` encodes its value via `Pos.Countable`).
* The `MRet`/`MBind` instances for `Spec` are a Lean `Monad` instance.
* The Rocq lemma `test` ends in `Abort` and is not ported.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Proof.go_etcd_io.etcd.client.v3_proof.model

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace go_etcd_io.etcd.client.v3_proof

section spec
variable {GF : BundledGFunctors}

variable (GF) in
def Spec (Resp : Type) : Type := (Resp → IProp GF) → IProp GF

instance Spec_Monad : Monad (Spec GF) where
  pure resp := fun Φ => Φ resp
  bind ma kmb := fun ΦB => ma (fun respa => kmb respa ΦB)

variable [allG GF] [Pos.Countable EtcdState.t]

/-- This is only in grove_ffi. -/
axiom own_time (t : w64) : IProp GF

def handle_etcdE_spec (γ : GName) : Handler etcdE (Spec GF) :=
  fun _A e =>
    match e with
    | .GetState => fun Φ => iprop(∃ σ q, ghost_var γ q σ ∗ (ghost_var γ q σ -∗ Φ σ))
    | .SetState σ' => fun Φ =>
        iprop(∃ (_σ : EtcdState.t), ghost_var γ 1 _σ ∗ (ghost_var γ 1 σ' -∗ Φ ()))
    | .GetTime => fun Φ => iprop(∀ time, own_time time -∗ own_time time ∗ Φ time)
    | .Assume P => fun Φ => iprop(⌜P⌝ -∗ Φ ())
    | .Assert P => fun Φ => iprop(⌜P⌝ ∗ Φ ())
    | .SuchThat pred => fun Φ => iprop(∀ x, ⌜pred x⌝ -∗ Φ x)

def GrantSpec (req : LeaseGrantRequest.t) (γ : GName) : Spec GF LeaseGrantResponse.t :=
  interp (handle_etcdE_spec γ) (LeaseGrant req)

end spec

end go_etcd_io.etcd.client.v3_proof

end Perennial
