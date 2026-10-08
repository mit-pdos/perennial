/-
Ghost state for a monotonically increasing nat,
wrapping iris-lean's `MonoNat = Auth MaxNat` camera.
-/
import Perennial.Ghost.Own

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode MonoNat

variable {GF : BundledGFunctors} [AllG GF]

def monoNatAuthOwn (γ : GName) (q : Qp) (n : Nat) : IProp GF :=
  own γ (MonoNat.auth (DFrac.own q) (MaxNat.ofNat n))

def monoNatLbOwn (γ : GName) (n : Nat) : IProp GF :=
  own γ (MonoNat.lb (MaxNat.ofNat n))

instance monoNatAuthOwn_timeless (γ : GName) (q : Qp) (n : Nat) :
    Timeless (monoNatAuthOwn (GF := GF) γ q n) := by
  unfold monoNatAuthOwn; infer_instance
instance monoNatLbOwn_timeless (γ : GName) (n : Nat) :
    Timeless (monoNatLbOwn (GF := GF) γ n) := by
  unfold monoNatLbOwn; infer_instance
instance monoNatLbOwn_persistent (γ : GName) (n : Nat) :
    Persistent (monoNatLbOwn (GF := GF) γ n) := by
  unfold monoNatLbOwn; infer_instance

instance monoNatAuthOwn_fractional (γ : GName) (n : Nat) :
    Fractional (fun q => monoNatAuthOwn (GF := GF) γ q n) where
  fractional p q := by
    unfold monoNatAuthOwn
    rw [← (own_op γ _ _).to_eq]
    exact (congrArg (own γ) (auth_dfrac_op (.own p) (.own q) _)).to_bi

instance monoNatAuthOwn_as_fractional (γ : GName) (q : Qp) (n : Nat) :
    AsFractional (monoNatAuthOwn (GF := GF) γ q n) ioΦ
      (fun q => monoNatAuthOwn γ q n) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := monoNatAuthOwn_fractional γ n

theorem monoNatAuthOwn_agree (γ : GName) (q1 q2 : Qp) (n1 n2 : Nat) :
    ⊢ monoNatAuthOwn (GF := GF) γ q1 n1 -∗ monoNatAuthOwn γ q2 n2 -∗
      ⌜q1 + q2 ≤ 1 ∧ n1 = n2⌝ := by
  unfold monoNatAuthOwn
  iintro H1 H2
  icombine H1 H2 gives %Hvalid
  ipureintro
  obtain ⟨h1, h2⟩ := (auth_dfrac_op_valid _ _ _ _).mp Hvalid
  exact ⟨h1, congrArg MaxNat.toNat h2⟩

theorem monoNatAuthOwn_exclusive (γ : GName) (n1 n2 : Nat) :
    ⊢ monoNatAuthOwn (GF := GF) γ 1 n1 -∗ monoNatAuthOwn γ 1 n2 -∗ False := by
  iintro H1 H2
  icases monoNatAuthOwn_agree γ 1 1 n1 n2 $$ H1 H2 with %⟨H, -⟩
  exfalso
  have : (1 : Rat) + 1 ≤ 1 := H
  grind

theorem monoNatLbOwn_valid (γ : GName) (q : Qp) (n m : Nat) :
    ⊢ monoNatAuthOwn (GF := GF) γ q n -∗ monoNatLbOwn γ m -∗ ⌜q ≤ 1 ∧ m ≤ n⌝ := by
  unfold monoNatAuthOwn monoNatLbOwn
  iintro H1 H2
  icombine H1 H2 gives %Hvalid
  ipureintro
  obtain ⟨h1, h2⟩ := (both_dfrac_valid _ _ _).mp Hvalid
  exact ⟨h1, h2⟩

/-- The conclusion of this lemma is persistent; the proofmode will preserve the
`mono_nat_auth_own` in the premise as long as the conclusion is introduced to
the persistent context. -/
theorem monoNatLbOwn_get (γ : GName) (q : Qp) (n : Nat) :
    ⊢ monoNatAuthOwn (GF := GF) γ q n -∗ monoNatLbOwn γ n := by
  unfold monoNatAuthOwn monoNatLbOwn
  iintro H
  iapply own_mono γ _ _ (included _ _) $$ H

theorem monoNatLbOwn_le {γ : GName} {n : Nat} (n' : Nat) (h : n' ≤ n) :
    ⊢ monoNatLbOwn (GF := GF) γ n -∗ monoNatLbOwn γ n' := by
  unfold monoNatLbOwn
  iintro H
  iapply own_mono γ _ _ (lb_mono (MaxNat.ofNat n') (MaxNat.ofNat n) h) $$ H

theorem monoNatLbOwn_0 (γ : GName) : ⊢ |==> monoNatLbOwn (GF := GF) γ 0 := by
  unfold monoNatLbOwn
  exact own_unit γ

theorem mono_nat_own_alloc_strong (P : GName → Prop) (n : Nat) (HP : PredInfinite P) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ monoNatAuthOwn (GF := GF) γ 1 n ∗ monoNatLbOwn γ n := by
  unfold monoNatAuthOwn monoNatLbOwn
  imod own_alloc_strong ((●MN (MaxNat.ofNat n)) • (◯MN (MaxNat.ofNat n))) P HP
    (by simp [both_valid]) with ⟨%γ, %HPγ, H⟩
  imodintro
  iexists γ
  isplitr
  · ipureintro; exact HPγ
  · icases (own_op γ _ _).1 $$ H with ⟨$, $⟩

theorem mono_nat_own_alloc (n : Nat) :
    ⊢ |==> ∃ γ, monoNatAuthOwn (GF := GF) γ 1 n ∗ monoNatLbOwn γ n := by
  imod mono_nat_own_alloc_strong (fun _ => True) n PredInfinite.true with ⟨%γ, -, H⟩
  imodintro
  iexists γ
  iexact H

theorem mono_nat_own_update {γ : GName} {n : Nat} (n' : Nat) (h : n ≤ n') :
    ⊢ monoNatAuthOwn (GF := GF) γ 1 n ==∗
      monoNatAuthOwn γ 1 n' ∗ monoNatLbOwn γ n' := by
  iintro H
  ihave >Hauth : |==> monoNatAuthOwn (GF := GF) γ 1 n' $$ [H]
  · unfold monoNatAuthOwn
    iapply own_update γ _ _ (update (MaxNat.ofNat n') h) $$ H
  · imodintro
    ihave #Hlb := monoNatLbOwn_get γ 1 n' $$ Hauth
    isplitl [Hauth]
    · iexact Hauth
    · iexact Hlb

end Perennial
