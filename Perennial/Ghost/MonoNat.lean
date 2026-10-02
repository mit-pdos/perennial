/-
Port of `new/ghost/mono_nat.v`: ghost state for a monotonically increasing nat,
wrapping iris-lean's `MonoNat = Auth MaxNat` camera.
-/
import Perennial.Ghost.Own

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode MonoNat

variable {GF : BundledGFunctors} [allG GF]

def mono_nat_auth_own (γ : GName) (q : Qp) (n : Nat) : IProp GF :=
  own γ (MonoNat.auth (DFrac.own q) (MaxNat.ofNat n))

def mono_nat_lb_own (γ : GName) (n : Nat) : IProp GF :=
  own γ (MonoNat.lb (MaxNat.ofNat n))

instance mono_nat_auth_own_timeless (γ : GName) (q : Qp) (n : Nat) :
    Timeless (mono_nat_auth_own (GF := GF) γ q n) := by
  unfold mono_nat_auth_own; infer_instance
instance mono_nat_lb_own_timeless (γ : GName) (n : Nat) :
    Timeless (mono_nat_lb_own (GF := GF) γ n) := by
  unfold mono_nat_lb_own; infer_instance
instance mono_nat_lb_own_persistent (γ : GName) (n : Nat) :
    Persistent (mono_nat_lb_own (GF := GF) γ n) := by
  unfold mono_nat_lb_own; infer_instance

instance mono_nat_auth_own_fractional (γ : GName) (n : Nat) :
    Fractional (fun q => mono_nat_auth_own (GF := GF) γ q n) where
  fractional p q := by
    unfold mono_nat_auth_own
    rw [← (own_op γ _ _).to_eq]
    exact (congrArg (own γ) (auth_dfrac_op (.own p) (.own q) _)).to_bi

instance mono_nat_auth_own_as_fractional (γ : GName) (q : Qp) (n : Nat) :
    AsFractional (mono_nat_auth_own (GF := GF) γ q n) ioΦ
      (fun q => mono_nat_auth_own γ q n) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := mono_nat_auth_own_fractional γ n

theorem mono_nat_auth_own_agree (γ : GName) (q1 q2 : Qp) (n1 n2 : Nat) :
    ⊢ mono_nat_auth_own (GF := GF) γ q1 n1 -∗ mono_nat_auth_own γ q2 n2 -∗
      ⌜q1 + q2 ≤ 1 ∧ n1 = n2⌝ := by
  unfold mono_nat_auth_own
  iintro H1 H2
  icombine H1 H2 gives %Hvalid
  ipureintro
  obtain ⟨h1, h2⟩ := (auth_dfrac_op_valid _ _ _ _).mp Hvalid
  exact ⟨h1, congrArg MaxNat.toNat h2⟩

theorem mono_nat_auth_own_exclusive (γ : GName) (n1 n2 : Nat) :
    ⊢ mono_nat_auth_own (GF := GF) γ 1 n1 -∗ mono_nat_auth_own γ 1 n2 -∗ False := by
  iintro H1 H2
  icases mono_nat_auth_own_agree γ 1 1 n1 n2 $$ H1 H2 with %⟨H, -⟩
  exfalso
  have : (1 : Rat) + 1 ≤ 1 := H
  grind

theorem mono_nat_lb_own_valid (γ : GName) (q : Qp) (n m : Nat) :
    ⊢ mono_nat_auth_own (GF := GF) γ q n -∗ mono_nat_lb_own γ m -∗ ⌜q ≤ 1 ∧ m ≤ n⌝ := by
  unfold mono_nat_auth_own mono_nat_lb_own
  iintro H1 H2
  icombine H1 H2 gives %Hvalid
  ipureintro
  obtain ⟨h1, h2⟩ := (both_dfrac_valid _ _ _).mp Hvalid
  exact ⟨h1, h2⟩

/-- The conclusion of this lemma is persistent; the proofmode will preserve the
`mono_nat_auth_own` in the premise as long as the conclusion is introduced to
the persistent context. -/
theorem mono_nat_lb_own_get (γ : GName) (q : Qp) (n : Nat) :
    ⊢ mono_nat_auth_own (GF := GF) γ q n -∗ mono_nat_lb_own γ n := by
  unfold mono_nat_auth_own mono_nat_lb_own
  iintro H
  iapply own_mono γ _ _ (included _ _) $$ H

theorem mono_nat_lb_own_le {γ : GName} {n : Nat} (n' : Nat) (h : n' ≤ n) :
    ⊢ mono_nat_lb_own (GF := GF) γ n -∗ mono_nat_lb_own γ n' := by
  unfold mono_nat_lb_own
  iintro H
  iapply own_mono γ _ _ (lb_mono (MaxNat.ofNat n') (MaxNat.ofNat n) h) $$ H

theorem mono_nat_lb_own_0 (γ : GName) : ⊢ |==> mono_nat_lb_own (GF := GF) γ 0 := by
  unfold mono_nat_lb_own
  exact own_unit γ

theorem mono_nat_own_alloc_strong (P : GName → Prop) (n : Nat) (HP : PredInfinite P) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ mono_nat_auth_own (GF := GF) γ 1 n ∗ mono_nat_lb_own γ n := by
  unfold mono_nat_auth_own mono_nat_lb_own
  imod own_alloc_strong ((●MN (MaxNat.ofNat n)) • (◯MN (MaxNat.ofNat n))) P HP
    (by simp [both_valid]) with ⟨%γ, %HPγ, H⟩
  imodintro
  iexists γ
  isplitr
  · ipureintro; exact HPγ
  · icases (own_op γ _ _).1 $$ H with ⟨$, $⟩

theorem mono_nat_own_alloc (n : Nat) :
    ⊢ |==> ∃ γ, mono_nat_auth_own (GF := GF) γ 1 n ∗ mono_nat_lb_own γ n := by
  imod mono_nat_own_alloc_strong (fun _ => True) n PredInfinite.true with ⟨%γ, -, H⟩
  imodintro
  iexists γ
  iexact H

theorem mono_nat_own_update {γ : GName} {n : Nat} (n' : Nat) (h : n ≤ n') :
    ⊢ mono_nat_auth_own (GF := GF) γ 1 n ==∗
      mono_nat_auth_own γ 1 n' ∗ mono_nat_lb_own γ n' := by
  iintro H
  ihave >Hauth : |==> mono_nat_auth_own (GF := GF) γ 1 n' $$ [H]
  · unfold mono_nat_auth_own
    iapply own_update γ _ _ (update (MaxNat.ofNat n') h) $$ H
  · imodintro
    ihave #Hlb := mono_nat_lb_own_get γ 1 n' $$ Hauth
    isplitl [Hauth]
    · iexact Hauth
    · iexact Hlb

end Perennial
