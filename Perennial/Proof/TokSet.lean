/-
Port of `new/proof/tok_set.v`: a counter of tokens. `own_tok_auth γ n` says
that exactly `n` tokens `own_toks γ 1` have been handed out.

Built on `Auth Nat` (with `(ℕ, +)`).
-/
import Perennial.Proof.ProofPrelude

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode Auth

section proof
variable {GF : BundledGFunctors} [allG GF]

def own_tok_auth_dfrac_def (γ : GName) (dq : DFrac) (num_toks : Nat) : IProp GF :=
  own γ (●{dq} num_toks : Auth Nat)
@[irreducible] def own_tok_auth_dfrac (γ : GName) (dq : DFrac) (num_toks : Nat) : IProp GF :=
  own_tok_auth_dfrac_def γ dq num_toks
theorem own_tok_auth_dfrac_unseal : @own_tok_auth_dfrac GF _ = @own_tok_auth_dfrac_def GF _ := by
  funext; with_unfolding_all rfl

/-- Rocq notation `own_tok_auth γ n`. -/
abbrev own_tok_auth (γ : GName) (n : Nat) : IProp GF := own_tok_auth_dfrac γ (DFrac.own 1) n

def own_toks_def (γ : GName) (n : Nat) : IProp GF :=
  own γ (◯ n : Auth Nat)
@[irreducible] def own_toks (γ : GName) (n : Nat) : IProp GF := own_toks_def γ n
theorem own_toks_unseal : @own_toks GF _ = @own_toks_def GF _ := by
  funext; with_unfolding_all rfl

local macro "unseal" : tactic => `(tactic|
  simp only [own_tok_auth, own_tok_auth_dfrac_unseal, own_tok_auth_dfrac_def, own_toks_unseal, own_toks_def])

private theorem nat_op (a b : Nat) : CMRA.op a b = a + b := rfl
private theorem nat_inc (a b : Nat) : a ≼ b ↔ a ≤ b :=
  ⟨fun ⟨c, h⟩ => by rw [h, nat_op]; omega, fun h => ⟨b - a, by rw [nat_op]; omega⟩⟩
private theorem nat_local_update {x y x' y' : Nat} (h : x + y' = x' + y) :
    (x, y) ~l~> (x', y') :=
  CommMonoidLike.leftCancelAdd_local_update h

instance own_toks_combine_as (γ : GName) (n m : Nat) :
    CombineSepAs (own_toks (GF := GF) γ n) (own_toks γ m) (own_toks γ (n + m)) where
  combine_sep_as := by
    unseal
    rw [← nat_op, frag_op]
    exact (own_op γ _ _).2

instance own_tok_auth_toks_combine_gives_as (γ : GName) (dq : DFrac) (n m : Nat) :
    CombineSepGives (own_tok_auth_dfrac (GF := GF) γ dq n) (own_toks γ m) iprop(⌜m ≤ n⌝) where
  combine_sep_gives := by
    unseal
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %hv
    imodintro; ipureintro
    obtain ⟨_, hinc, _⟩ := both_dfrac_valid_discrete.mp hv
    exact (nat_inc _ _).mp hinc

instance (priority := default - 40) own_tok_auth_combine_as (γ : GName) (dq dq' : DFrac) (n : Nat) :
    CombineSepAs (own_tok_auth_dfrac (GF := GF) γ dq n) (own_tok_auth_dfrac γ dq' n)
      (own_tok_auth_dfrac γ (dq • dq') n) where
  combine_sep_as := by
    unseal
    rw [auth_dfrac_op]
    exact (own_op γ _ _).2

instance own_tok_auth_combine_gives_as (γ : GName) (dq dq' : DFrac) (n n' : Nat) :
    CombineSepGives (own_tok_auth_dfrac (GF := GF) γ dq n) (own_tok_auth_dfrac γ dq' n')
      iprop(⌜✓ (dq • dq') ∧ n = n'⌝) where
  combine_sep_gives := by
    unseal
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %hv
    imodintro; ipureintro
    obtain ⟨h1, h2, _⟩ := auth_dfrac_op_valid.mp hv
    exact ⟨h1, h2⟩

instance own_tok_auth_dfrac_update_to_persistent (γ : GName) (dq : DFrac) (n : Nat) :
    UpdateIntoPersistently (own_tok_auth_dfrac (GF := GF) γ dq n)
      (own_tok_auth_dfrac γ DFrac.discard n) where
  update_into_persistently := by
    unseal
    refine (own_update γ _ _ auth_update_auth_persist).trans (BIUpdate.mono ?_)
    exact intuitionistically_of_intuitionistic.2

theorem own_tok_auth_alloc : ⊢ |==> ∃ γ, own_tok_auth (GF := GF) γ 0 := by
  unseal
  exact own_alloc _ (auth_valid.mpr trivial)

theorem own_tok_auth_add (m : Nat) (γ : GName) (n : Nat) :
    own_tok_auth (GF := GF) γ n ⊢ |==> (own_tok_auth γ (n + m) ∗ own_toks γ m) := by
  unseal
  have hup : (n, (UCMRA.unit : Nat)) ~l~> (n + m, m) := nat_local_update (by show n + m = n + m + 0; omega)
  exact (own_update γ _ ((● (n + m) : Auth Nat) • ◯ m) (auth_update_alloc hup)).trans
    (BIUpdate.mono (own_op γ (● (n + m) : Auth Nat) (◯ m)).1)

theorem own_tok_auth_sub (m : Nat) (γ : GName) (n : Nat) :
    ⊢ own_tok_auth (GF := GF) γ n -∗ own_toks γ m ==∗ own_tok_auth γ (n - m) := by
  iintro H1 H2
  icombine H1 H2 gives %H
  unseal
  have hup : (n, m) ~l~> (n - m, (UCMRA.unit : Nat)) := nat_local_update (by show n + 0 = n - m + m; omega)
  iapply own_update_2 γ _ _ _ (auth_update_dealloc hup) $$ H1 H2

theorem own_tok_auth_S (γ : GName) (n : Nat) :
    own_tok_auth (GF := GF) γ n ⊢ |==> (own_tok_auth γ (n + 1) ∗ own_toks γ 1) :=
  own_tok_auth_add 1 γ n

theorem own_tok_auth_delete_S (γ : GName) (n : Nat) :
    ⊢ own_tok_auth (GF := GF) γ (n + 1) -∗ own_toks γ 1 ==∗ own_tok_auth γ n := by
  iintro H1 H2
  ihave H := own_tok_auth_sub 1 γ (n + 1) $$ H1 H2
  simp only [Nat.add_sub_cancel]
  iexact H

theorem own_toks_0 (γ : GName) : ⊢ |==> own_toks (GF := GF) γ 0 := by
  unseal
  exact own_unit γ

theorem own_toks_add (m n : Nat) (γ : GName) :
    own_toks (GF := GF) γ (n + m) ⊣⊢ own_toks γ n ∗ own_toks γ m := by
  unseal
  rw [← nat_op, frag_op]
  exact own_op γ _ _

theorem own_toks_add_1 (m n : Nat) (γ : GName) :
    own_toks (GF := GF) γ (n + m) ⊢ own_toks γ n ∗ own_toks γ m :=
  (own_toks_add m n γ).1

theorem own_toks_add_2 (m n : Nat) (γ : GName) :
    own_toks (GF := GF) γ n ∗ own_toks γ m ⊢ own_toks γ (n + m) :=
  (own_toks_add m n γ).2

instance own_toks_Timeless (γ : GName) (n : Nat) : Timeless (own_toks (GF := GF) γ n) := by
  unseal; infer_instance

instance own_tok_auth_dfrac_Persistent (γ : GName) (n : Nat) :
    Persistent (own_tok_auth_dfrac (GF := GF) γ DFrac.discard n) := by
  unseal; infer_instance

instance own_tok_auth_dfrac_Timeless (γ : GName) (dq : DFrac) (n : Nat) :
    Timeless (own_tok_auth_dfrac (GF := GF) γ dq n) := by
  unseal; infer_instance

/-- Rocq names this `typed_pointsto_fractional` (a copy-paste name). -/
instance own_tok_auth_fractional (γ : GName) (n : Nat) :
    Fractional (fun q => own_tok_auth_dfrac (GF := GF) γ (DFrac.own q) n) where
  fractional p q := by
    unseal
    rw [← (own_op γ _ _).to_eq]
    exact (congrArg (own γ) (auth_dfrac_op (dq1 := .own p) (dq2 := .own q))).to_bi

instance own_tok_auth_as_fractional (γ : GName) (q : Qp) (n : Nat) :
    AsFractional (own_tok_auth_dfrac (GF := GF) γ (DFrac.own q) n) ioΦ
      (fun q => own_tok_auth_dfrac γ (DFrac.own q) n) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := own_tok_auth_fractional γ n

end proof

end Perennial
