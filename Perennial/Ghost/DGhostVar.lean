/-
A ghost variable of arbitrary (countable) type
with `DFrac` ownership; can be mutated when fully owned.
-/
module

public import Perennial.Ghost.Own
public import Perennial.Ghost.Countable
public import Perennial.IrisLib.DFractional

@[expose] public section

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode DFracAgree

variable {GF : BundledGFunctors} [AllG GF] {A : Type} [Pos.Countable A]

def dghostVar (γ : GName) (dq : DFrac) (a : A) : IProp GF :=
  own γ (DFracAgree.mk dq (encodeO a))

theorem dghostVar_unseal (γ : GName) (dq : DFrac) (a : A) :
    (dghostVar γ dq a : IProp GF) = own γ (DFracAgree.mk dq (encodeO a)) := rfl

instance dghostVar_timeless (γ : GName) (dq : DFrac) (a : A) :
    Timeless (dghostVar (GF := GF) γ dq a) := by
  unfold dghostVar; infer_instance

instance dghostVar_persistent (γ : GName) (a : A) :
    Persistent (dghostVar (GF := GF) γ .discard a) := by
  unfold dghostVar; infer_instance

instance dghostVar_dfractional (γ : GName) (a : A) :
    DFractional (fun dq => dghostVar (GF := GF) γ dq a) where
  dfractional p q := by unfold dghostVar; rw [mk_op]; exact own_op γ _ _
  dfractional_persistent := by unfold dghostVar; infer_instance
  dfractional_persist dq := by
    unfold dghostVar; exact own_update γ _ _ persist

instance dghostVar_as_dfractional (γ : GName) (dq : DFrac) (a : A) :
    AsDFractional (dghostVar (GF := GF) γ dq a) (fun dq => dghostVar γ dq a) dq where
  as_dfractional := .rfl
  as_dfractional_dfractional := dghostVar_dfractional γ a

instance dghostVar_fractional (γ : GName) (a : A) :
    Fractional (fun q => dghostVar (GF := GF) γ (.own q) a) :=
  fractional_of_dfractional (fun dq => dghostVar γ dq a)

instance dghostVar_as_fractional (γ : GName) (q : Qp) (a : A) :
    AsFractional (dghostVar (GF := GF) γ (.own q) a) ioΦ
      (fun q => dghostVar γ (.own q) a) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := dghostVar_fractional γ a

theorem dghostVar_alloc_strong (a : A) (P : GName → Prop) (HP : PredInfinite P) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ (dghostVar (GF := GF) γ (.own 1) a) :=
  own_alloc_strong _ P HP (mk_valid.mpr DFrac.valid_own_one)

theorem dghostVar_alloc (a : A) : ⊢ |==> ∃ γ, (dghostVar (GF := GF) γ (.own 1) a) :=
  own_alloc _ (mk_valid.mpr DFrac.valid_own_one)

theorem dghostVar_valid_2 (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac) :
    ⊢ dghostVar (GF := GF) γ dq1 a1 -∗ dghostVar γ dq2 a2 -∗ ⌜✓ (dq1 • dq2) ∧ a1 = a2⌝ := by
  unfold dghostVar
  iintro H1 H2
  icombine H1 H2 gives %H
  obtain ⟨Hq, Ha⟩ := op_valid.mp H
  ipureintro
  exact ⟨Hq, encodeO_inj Ha⟩

/-- Almost all the time, this is all you really need. -/
theorem dghostVar_agree (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac) :
    ⊢ dghostVar (GF := GF) γ dq1 a1 -∗ dghostVar γ dq2 a2 -∗ ⌜a1 = a2⌝ := by
  iintro H1 H2
  ihave ⟨-, $⟩ := dghostVar_valid_2 γ a1 dq1 a2 dq2 $$ H1 H2

instance dghostVar_combine_gives (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac) :
    CombineSepGives (dghostVar (GF := GF) γ dq1 a1) (dghostVar γ dq2 a2)
      iprop(⌜✓ (dq1 • dq2) ∧ a1 = a2⌝) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    icases dghostVar_valid_2 γ a1 dq1 a2 dq2 $$ H1 H2 with %H
    itrivial

/-- Lower priority than the `Fractional` instance, which is used when `a1 = a2`. -/
instance (priority := default - 20) dghostVar_combine_as (γ : GName) (a1 : A) (dq1 : DFrac)
    (a2 : A) (dq2 : DFrac) (dq : DFrac) [h : IsOp .merge dq dq1 dq2] :
    CombineSepAs (dghostVar (GF := GF) γ dq1 a1) (dghostVar γ dq2 a2) (dghostVar γ dq a1) where
  combine_sep_as := by
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %⟨-, rfl⟩
    unfold dghostVar
    rw [h.is_op, mk_op]
    icombine H1 H2 as $

/-- This is just an instance of dfractionality above, but that can be hard to find. -/
theorem dghostVar_split (γ : GName) (a : A) (dq1 dq2 : DFrac) :
    ⊢ dghostVar (GF := GF) γ (dq1 • dq2) a -∗ dghostVar γ dq1 a ∗ dghostVar γ dq2 a := by
  unfold dghostVar
  rw [mk_op]
  iintro H
  iapply (own_op γ _ _).1
  iexact H

/-- Update the ghost variable to new value `b`. -/
theorem dghostVar_update (b : A) (γ : GName) (a : A) :
    ⊢ dghostVar (GF := GF) γ (.own 1) a ==∗ dghostVar γ (.own 1) b := by
  unfold dghostVar
  haveI : Exclusive (DFracAgree.mk (.own (1 : Qp)) (encodeO a)) := mk_exclusive
  iapply own_update γ _ (DFracAgree.mk (.own 1) (encodeO b))
    (.exclusive (mk_valid.mpr DFrac.valid_own_one))

theorem dghostVar_update_2 (b : A) (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac)
    (Hq : dq1 • dq2 = .own 1) :
    ⊢ dghostVar (GF := GF) γ dq1 a1 -∗ dghostVar γ dq2 a2 ==∗
      dghostVar γ dq1 b ∗ dghostVar γ dq2 b := by
  unfold dghostVar
  iintro H1 H2
  ieval (rewrite [← (own_op γ _ _).to_eq])
  iapply own_update_2 γ _ _ _ (update₂ Hq) $$ H1 H2

theorem dghostVar_update_halves (b : A) (γ : GName) (a1 a2 : A) :
    ⊢ dghostVar (GF := GF) γ (.own (1 : Qp).half) a1 -∗ dghostVar γ (.own (1 : Qp).half) a2 ==∗
      dghostVar γ (.own (1 : Qp).half) b ∗ dghostVar γ (.own (1 : Qp).half) b :=
  dghostVar_update_2 b γ a1 _ a2 _ (by rw [DFrac.op_own, Qp.half_add_half])

theorem dghostVar_persist (γ : GName) (q : Qp) (a : A) :
    ⊢ dghostVar (GF := GF) γ (.own q) a ==∗ dghostVar γ .discard a := by
  unfold dghostVar
  iapply own_update γ _ (DFracAgree.mk .discard (encodeO a)) persist

/-! ### Framing support -/

instance frame_dghost_var (p : Bool) (γ : GName) (a : A) (q1 q2 q : Qp)
    [FrameFractionalQp q1 q2 q] :
    Frame p (dghostVar (GF := GF) γ (.own q1) a) (dghostVar γ (.own q2) a)
      (dghostVar γ (.own q) a) :=
  frame_fractional (fun q => dghostVar γ (.own q) a) q1 q2 q

end Perennial
