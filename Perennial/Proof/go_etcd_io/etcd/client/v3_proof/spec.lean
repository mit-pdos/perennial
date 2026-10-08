/-
Interpreting the etcd model's effects as separation-logic specifications.

Notes:
* Nothing from `v3_proof/base` is used beyond the model and the prelude, so this
  file imports `model` directly.
* The ghost state needs `[allG GF] [Pos.Countable EtcdState.t]`
  (`ghost_var` encodes its value via `Pos.Countable`).
* `Spec` has a `Monad` instance.
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

variable [AllG GF] [Pos.Countable EtcdState]

/-- This is only in grove_ffi. -/
axiom ownTime (t : w64) : IProp GF

def handleEtcdESpec (γ : GName) : Handler EtcdE (Spec GF) :=
  fun _A e =>
    match e with
    | .GetState => fun Φ => iprop(∃ σ q, ghostVar γ q σ ∗ (ghostVar γ q σ -∗ Φ σ))
    | .SetState σ' => fun Φ =>
        iprop(∃ (_σ : EtcdState), ghostVar γ 1 _σ ∗ (ghostVar γ 1 σ' -∗ Φ ()))
    | .GetTime => fun Φ => iprop(∀ time, ownTime time -∗ ownTime time ∗ Φ time)
    | .Assume P => fun Φ => iprop(⌜P⌝ -∗ Φ ())
    | .Assert P => fun Φ => iprop(⌜P⌝ ∗ Φ ())
    | .SuchThat pred => fun Φ => iprop(∀ x, ⌜pred x⌝ -∗ Φ x)

def GrantSpec (req : LeaseGrantRequest) (γ : GName) : Spec GF LeaseGrantResponse :=
  interp (handleEtcdESpec γ) (LeaseGrant req)

end spec

end go_etcd_io.etcd.client.v3_proof

end Perennial
