/-
Port of `new/ghost/dghost_var.v`: a ghost variable of arbitrary (countable) type
with `DFrac` ownership; can be mutated when fully owned.
-/
import Perennial.Ghost.Own
import Perennial.Ghost.Countable
import Perennial.IrisLib.DFractional

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode DFracAgree

variable {GF : BundledGFunctors} [allG GF] {A : Type} [Pos.Countable A]

def dghost_var (γ : GName) (dq : DFrac) (a : A) : IProp GF :=
  own γ (DFracAgree.mk dq (encodeO a))

theorem dghost_var_unseal (γ : GName) (dq : DFrac) (a : A) :
    (dghost_var γ dq a : IProp GF) = own γ (DFracAgree.mk dq (encodeO a)) := rfl

instance dghost_var_timeless (γ : GName) (dq : DFrac) (a : A) :
    Timeless (dghost_var (GF := GF) γ dq a) := by
  unfold dghost_var; infer_instance

instance dghost_var_dfractional (γ : GName) (a : A) :
    DFractional (fun dq => dghost_var (GF := GF) γ dq a) where
  dfractional p q := by unfold dghost_var; rw [mk_op]; exact own_op γ _ _
  dfractional_persistent := by unfold dghost_var; infer_instance
  dfractional_persist dq := by
    unfold dghost_var; exact own_update γ _ _ persist

instance dghost_var_as_dfractional (γ : GName) (dq : DFrac) (a : A) :
    AsDFractional (dghost_var (GF := GF) γ dq a) (fun dq => dghost_var γ dq a) dq where
  as_dfractional := .rfl
  as_dfractional_dfractional := dghost_var_dfractional γ a

instance dghost_var_fractional (γ : GName) (a : A) :
    Fractional (fun q => dghost_var (GF := GF) γ (.own q) a) :=
  fractional_of_dfractional (fun dq => dghost_var γ dq a)

instance dghost_var_as_fractional (γ : GName) (q : Qp) (a : A) :
    AsFractional (dghost_var (GF := GF) γ (.own q) a) ioΦ
      (fun q => dghost_var γ (.own q) a) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := dghost_var_fractional γ a

theorem dghost_var_alloc_strong (a : A) (P : GName → Prop) (HP : PredInfinite P) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ (dghost_var (GF := GF) γ (.own 1) a) :=
  own_alloc_strong _ P HP (mk_valid.mpr DFrac.valid_own_one)

theorem dghost_var_alloc (a : A) : ⊢ |==> ∃ γ, (dghost_var (GF := GF) γ (.own 1) a) :=
  own_alloc _ (mk_valid.mpr DFrac.valid_own_one)

theorem dghost_var_valid_2 (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac) :
    ⊢ dghost_var (GF := GF) γ dq1 a1 -∗ dghost_var γ dq2 a2 -∗ ⌜✓ (dq1 • dq2) ∧ a1 = a2⌝ := by
  unfold dghost_var
  iintro H1 H2
  icombine H1 H2 gives %H
  obtain ⟨Hq, Ha⟩ := op_valid.mp H
  ipureintro
  exact ⟨Hq, encodeO_inj Ha⟩

/-- Almost all the time, this is all you really need. -/
theorem dghost_var_agree (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac) :
    ⊢ dghost_var (GF := GF) γ dq1 a1 -∗ dghost_var γ dq2 a2 -∗ ⌜a1 = a2⌝ := by
  iintro H1 H2
  ihave ⟨-, $⟩ := dghost_var_valid_2 γ a1 dq1 a2 dq2 $$ H1 H2

instance dghost_var_combine_gives (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac) :
    CombineSepGives (dghost_var (GF := GF) γ dq1 a1) (dghost_var γ dq2 a2)
      iprop(⌜✓ (dq1 • dq2) ∧ a1 = a2⌝) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    icases dghost_var_valid_2 γ a1 dq1 a2 dq2 $$ H1 H2 with %H
    itrivial

/-- Lower priority than the `Fractional` instance, which is used when `a1 = a2`. -/
instance (priority := default - 20) dghost_var_combine_as (γ : GName) (a1 : A) (dq1 : DFrac)
    (a2 : A) (dq2 : DFrac) (dq : DFrac) [h : IsOp .merge dq dq1 dq2] :
    CombineSepAs (dghost_var (GF := GF) γ dq1 a1) (dghost_var γ dq2 a2) (dghost_var γ dq a1) where
  combine_sep_as := by
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %⟨-, rfl⟩
    unfold dghost_var
    rw [h.is_op, mk_op]
    icombine H1 H2 as $

/-- This is just an instance of dfractionality above, but that can be hard to find. -/
theorem dghost_var_split (γ : GName) (a : A) (dq1 dq2 : DFrac) :
    ⊢ dghost_var (GF := GF) γ (dq1 • dq2) a -∗ dghost_var γ dq1 a ∗ dghost_var γ dq2 a := by
  unfold dghost_var
  rw [mk_op]
  iintro H
  iapply (own_op γ _ _).1
  iexact H

/-- Update the ghost variable to new value `b`. -/
theorem dghost_var_update (b : A) (γ : GName) (a : A) :
    ⊢ dghost_var (GF := GF) γ (.own 1) a ==∗ dghost_var γ (.own 1) b := by
  unfold dghost_var
  haveI : Exclusive (DFracAgree.mk (.own (1 : Qp)) (encodeO a)) := mk_exclusive
  iapply own_update γ _ (DFracAgree.mk (.own 1) (encodeO b))
    (.exclusive (mk_valid.mpr DFrac.valid_own_one))

theorem dghost_var_update_2 (b : A) (γ : GName) (a1 : A) (dq1 : DFrac) (a2 : A) (dq2 : DFrac)
    (Hq : dq1 • dq2 = .own 1) :
    ⊢ dghost_var (GF := GF) γ dq1 a1 -∗ dghost_var γ dq2 a2 ==∗
      dghost_var γ dq1 b ∗ dghost_var γ dq2 b := by
  unfold dghost_var
  iintro H1 H2
  ieval (rewrite [← (own_op γ _ _).to_eq])
  iapply own_update_2 γ _ _ _ (update₂ Hq) $$ H1 H2

theorem dghost_var_update_halves (b : A) (γ : GName) (a1 a2 : A) :
    ⊢ dghost_var (GF := GF) γ (.own (1 : Qp).half) a1 -∗ dghost_var γ (.own (1 : Qp).half) a2 ==∗
      dghost_var γ (.own (1 : Qp).half) b ∗ dghost_var γ (.own (1 : Qp).half) b :=
  dghost_var_update_2 b γ a1 _ a2 _ (by rw [DFrac.op_own, Qp.half_add_half])

theorem dghost_var_persist (γ : GName) (q : Qp) (a : A) :
    ⊢ dghost_var (GF := GF) γ (.own q) a ==∗ dghost_var γ .discard a := by
  unfold dghost_var
  iapply own_update γ _ (DFracAgree.mk .discard (encodeO a)) persist

/-! ### Framing support -/

instance frame_dghost_var (p : Bool) (γ : GName) (a : A) (q1 q2 q : Qp)
    [FrameFractionalQp q1 q2 q] :
    Frame p (dghost_var (GF := GF) γ (.own q1) a) (dghost_var γ (.own q2) a)
      (dghost_var γ (.own q) a) :=
  frame_fractional (fun q => dghost_var γ (.own q) a) q1 q2 q

end Perennial
