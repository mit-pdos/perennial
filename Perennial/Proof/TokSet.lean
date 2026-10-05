/-
Port of `new/proof/tok_set.v`: a counter of tokens. `ownTokAuth γ n` says
that exactly `n` tokens `ownToks γ 1` have been handed out.

Built on `Auth Nat` (with `(ℕ, +)`).
-/
import Perennial.Proof.ProofPrelude

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode Auth

section proof
variable {GF : BundledGFunctors} [AllG GF]

def ownTokAuthDfracDef (γ : GName) (dq : DFrac) (num_toks : Nat) : IProp GF :=
  own γ (●{dq} num_toks : Auth Nat)
@[irreducible] def ownTokAuthDfrac (γ : GName) (dq : DFrac) (num_toks : Nat) : IProp GF :=
  ownTokAuthDfracDef γ dq num_toks
theorem ownTokAuthDfrac_unseal : @ownTokAuthDfrac GF _ = @ownTokAuthDfracDef GF _ := by
  funext; with_unfolding_all rfl

/-- Rocq notation `ownTokAuth γ n`. -/
abbrev ownTokAuth (γ : GName) (n : Nat) : IProp GF := ownTokAuthDfrac γ (DFrac.own 1) n

def ownToksDef (γ : GName) (n : Nat) : IProp GF :=
  own γ (◯ n : Auth Nat)
@[irreducible] def ownToks (γ : GName) (n : Nat) : IProp GF := ownToksDef γ n
theorem ownToks_unseal : @ownToks GF _ = @ownToksDef GF _ := by
  funext; with_unfolding_all rfl

local macro "unseal" : tactic => `(tactic|
  simp only [ownTokAuth, ownTokAuthDfrac_unseal, ownTokAuthDfracDef, ownToks_unseal, ownToksDef])

private theorem nat_op (a b : Nat) : CMRA.op a b = a + b := rfl
private theorem nat_inc (a b : Nat) : a ≼ b ↔ a ≤ b :=
  ⟨fun ⟨c, h⟩ => by rw [h, nat_op]; omega, fun h => ⟨b - a, by rw [nat_op]; omega⟩⟩
private theorem nat_local_update {x y x' y' : Nat} (h : x + y' = x' + y) :
    (x, y) ~l~> (x', y') :=
  CommMonoidLike.leftCancelAdd_local_update h

instance ownToks_combine_as (γ : GName) (n m : Nat) :
    CombineSepAs (ownToks (GF := GF) γ n) (ownToks γ m) (ownToks γ (n + m)) where
  combine_sep_as := by
    unseal
    rw [← nat_op, frag_op]
    exact (own_op γ _ _).2

instance ownTokAuth_toks_combine_gives_as (γ : GName) (dq : DFrac) (n m : Nat) :
    CombineSepGives (ownTokAuthDfrac (GF := GF) γ dq n) (ownToks γ m) iprop(⌜m ≤ n⌝) where
  combine_sep_gives := by
    unseal
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %hv
    imodintro; ipureintro
    obtain ⟨_, hinc, _⟩ := both_dfrac_valid_discrete.mp hv
    exact (nat_inc _ _).mp hinc

instance (priority := default - 40) ownTokAuth_combine_as (γ : GName) (dq dq' : DFrac) (n : Nat) :
    CombineSepAs (ownTokAuthDfrac (GF := GF) γ dq n) (ownTokAuthDfrac γ dq' n)
      (ownTokAuthDfrac γ (dq • dq') n) where
  combine_sep_as := by
    unseal
    rw [auth_dfrac_op]
    exact (own_op γ _ _).2

instance ownTokAuth_combine_gives_as (γ : GName) (dq dq' : DFrac) (n n' : Nat) :
    CombineSepGives (ownTokAuthDfrac (GF := GF) γ dq n) (ownTokAuthDfrac γ dq' n')
      iprop(⌜✓ (dq • dq') ∧ n = n'⌝) where
  combine_sep_gives := by
    unseal
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %hv
    imodintro; ipureintro
    obtain ⟨h1, h2, _⟩ := auth_dfrac_op_valid.mp hv
    exact ⟨h1, h2⟩

instance ownTokAuthDfrac_update_to_persistent (γ : GName) (dq : DFrac) (n : Nat) :
    UpdateIntoPersistently (ownTokAuthDfrac (GF := GF) γ dq n)
      (ownTokAuthDfrac γ DFrac.discard n) where
  update_into_persistently := by
    unseal
    refine (own_update γ _ _ auth_update_auth_persist).trans (BIUpdate.mono ?_)
    exact intuitionistically_of_intuitionistic.2

theorem ownTokAuth_alloc : ⊢ |==> ∃ γ, ownTokAuth (GF := GF) γ 0 := by
  unseal
  exact own_alloc _ (auth_valid.mpr trivial)

theorem ownTokAuth_add (m : Nat) (γ : GName) (n : Nat) :
    ownTokAuth (GF := GF) γ n ⊢ |==> (ownTokAuth γ (n + m) ∗ ownToks γ m) := by
  unseal
  have hup : (n, (UCMRA.unit : Nat)) ~l~> (n + m, m) := nat_local_update (by show n + m = n + m + 0; omega)
  exact (own_update γ _ ((● (n + m) : Auth Nat) • ◯ m) (auth_update_alloc hup)).trans
    (BIUpdate.mono (own_op γ (● (n + m) : Auth Nat) (◯ m)).1)

theorem ownTokAuth_sub (m : Nat) (γ : GName) (n : Nat) :
    ⊢ ownTokAuth (GF := GF) γ n -∗ ownToks γ m ==∗ ownTokAuth γ (n - m) := by
  iintro H1 H2
  icombine H1 H2 gives %H
  unseal
  have hup : (n, m) ~l~> (n - m, (UCMRA.unit : Nat)) := nat_local_update (by show n + 0 = n - m + m; omega)
  iapply own_update_2 γ _ _ _ (auth_update_dealloc hup) $$ H1 H2

theorem ownTokAuth_S (γ : GName) (n : Nat) :
    ownTokAuth (GF := GF) γ n ⊢ |==> (ownTokAuth γ (n + 1) ∗ ownToks γ 1) :=
  ownTokAuth_add 1 γ n

theorem ownTokAuth_delete_S (γ : GName) (n : Nat) :
    ⊢ ownTokAuth (GF := GF) γ (n + 1) -∗ ownToks γ 1 ==∗ ownTokAuth γ n := by
  iintro H1 H2
  ihave H := ownTokAuth_sub 1 γ (n + 1) $$ H1 H2
  simp only [Nat.add_sub_cancel]
  iexact H

theorem ownToks_0 (γ : GName) : ⊢ |==> ownToks (GF := GF) γ 0 := by
  unseal
  exact own_unit γ

theorem ownToks_add (m n : Nat) (γ : GName) :
    ownToks (GF := GF) γ (n + m) ⊣⊢ ownToks γ n ∗ ownToks γ m := by
  unseal
  rw [← nat_op, frag_op]
  exact own_op γ _ _

theorem ownToks_add_1 (m n : Nat) (γ : GName) :
    ownToks (GF := GF) γ (n + m) ⊢ ownToks γ n ∗ ownToks γ m :=
  (ownToks_add m n γ).1

theorem ownToks_add_2 (m n : Nat) (γ : GName) :
    ownToks (GF := GF) γ n ∗ ownToks γ m ⊢ ownToks γ (n + m) :=
  (ownToks_add m n γ).2

instance ownToks_Timeless (γ : GName) (n : Nat) : Timeless (ownToks (GF := GF) γ n) := by
  unseal; infer_instance

instance ownTokAuthDfrac_Persistent (γ : GName) (n : Nat) :
    Persistent (ownTokAuthDfrac (GF := GF) γ DFrac.discard n) := by
  unseal; infer_instance

instance ownTokAuthDfrac_Timeless (γ : GName) (dq : DFrac) (n : Nat) :
    Timeless (ownTokAuthDfrac (GF := GF) γ dq n) := by
  unseal; infer_instance

/-- Rocq names this `typed_pointsto_fractional` (a copy-paste name). -/
instance ownTokAuth_fractional (γ : GName) (n : Nat) :
    Fractional (fun q => ownTokAuthDfrac (GF := GF) γ (DFrac.own q) n) where
  fractional p q := by
    unseal
    rw [← (own_op γ _ _).to_eq]
    exact (congrArg (own γ) (auth_dfrac_op (dq1 := .own p) (dq2 := .own q))).to_bi

instance ownTokAuth_as_fractional (γ : GName) (q : Qp) (n : Nat) :
    AsFractional (ownTokAuthDfrac (GF := GF) γ (DFrac.own q) n) ioΦ
      (fun q => ownTokAuthDfrac γ (DFrac.own q) n) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := ownTokAuth_fractional γ n

end proof

end Perennial
