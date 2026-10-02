/-
Port of `new/ghost/token.v`: "unique tokens". `token γ` provides ownership of
the token named `γ`; `token_exclusive` proves only one exists.
-/
import Perennial.Ghost.Own

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode Excl

variable {GF : BundledGFunctors} [allG GF]

def token (γ : GName) : IProp GF := own γ (excl () : Excl Unit)

theorem token_unseal (γ : GName) : (token γ : IProp GF) = own γ (excl () : Excl Unit) := rfl

instance token_timeless (γ : GName) : Timeless (token (GF := GF) γ) := by
  unfold token; infer_instance

theorem token_alloc_strong (P : GName → Prop) (HP : PredInfinite P) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ token (GF := GF) γ :=
  own_alloc_strong _ P HP trivial

theorem token_alloc : ⊢ |==> ∃ γ, token (GF := GF) γ :=
  own_alloc _ trivial

theorem token_exclusive (γ : GName) : ⊢ token (GF := GF) γ -∗ token γ -∗ False := by
  unfold token
  iintro H1 H2
  icombine H1 H2 gives H
  icases internalCmraValid_discrete (A := Excl Unit) $$ H with %H
  exact H.elim

instance token_combine_gives (γ : GName) :
    CombineSepGives (token (GF := GF) γ) (token γ) iprop(⌜False⌝) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    icases token_exclusive γ $$ H1 H2 with ⟨⟩

end Perennial
