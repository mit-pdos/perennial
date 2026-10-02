/-
Port of `new/ghost/ghost_var.v`: a ghost variable of arbitrary (countable) type
with fractional ownership; can be mutated when fully owned.
-/
import Perennial.Ghost.Own
import Perennial.Ghost.Countable

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode DFracAgree

variable {GF : BundledGFunctors} [allG GF] {A : Type} [Pos.Countable A]

def ghost_var (γ : GName) (q : Qp) (a : A) : IProp GF :=
  own γ (Frac.mk q (encodeO a))

theorem ghost_var_unseal (γ : GName) (q : Qp) (a : A) :
    (ghost_var γ q a : IProp GF) = own γ (Frac.mk q (encodeO a)) := rfl

instance ghost_var_timeless (γ : GName) (q : Qp) (a : A) :
    Timeless (ghost_var (GF := GF) γ q a) := by
  unfold ghost_var; infer_instance

instance ghost_var_fractional (γ : GName) (a : A) :
    Fractional (fun q => ghost_var (GF := GF) γ q a) where
  fractional p q := by unfold ghost_var; rw [Frac.mk_op]; exact own_op γ _ _

instance ghost_var_as_fractional (γ : GName) (a : A) (q : Qp) :
    AsFractional (ghost_var (GF := GF) γ q a) ioΦ (fun q => ghost_var γ q a) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := ghost_var_fractional γ a

theorem ghost_var_alloc_strong (a : A) (P : GName → Prop) (HP : PredInfinite P) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ (ghost_var (GF := GF) γ 1 a) :=
  own_alloc_strong _ P HP (mk_valid.mpr DFrac.valid_own_one)

theorem ghost_var_alloc (a : A) : ⊢ |==> ∃ γ, (ghost_var (GF := GF) γ 1 a) :=
  own_alloc _ (mk_valid.mpr DFrac.valid_own_one)

theorem ghost_var_valid_2 (γ : GName) (a1 : A) (q1 : Qp) (a2 : A) (q2 : Qp) :
    ⊢ ghost_var (GF := GF) γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜q1 + q2 ≤ 1 ∧ a1 = a2⌝ := by
  unfold ghost_var
  iintro H1 H2
  icombine H1 H2 gives %H
  obtain ⟨Hq, Ha⟩ := Frac.op_valid.mp H
  ipureintro
  exact ⟨Hq, encodeO_inj Ha⟩

/-- Almost all the time, this is all you really need. -/
theorem ghost_var_agree (γ : GName) (a1 : A) (q1 : Qp) (a2 : A) (q2 : Qp) :
    ⊢ ghost_var (GF := GF) γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜a1 = a2⌝ := by
  iintro H1 H2
  ihave ⟨-, $⟩ := ghost_var_valid_2 γ a1 q1 a2 q2 $$ H1 H2

instance ghost_var_combine_gives (γ : GName) (a1 : A) (q1 : Qp) (a2 : A) (q2 : Qp) :
    CombineSepGives (ghost_var (GF := GF) γ q1 a1) (ghost_var γ q2 a2)
      iprop(⌜q1 + q2 ≤ 1 ∧ a1 = a2⌝) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    icases ghost_var_valid_2 γ a1 q1 a2 q2 $$ H1 H2 with %H
    itrivial

/-- Lower priority than the `Fractional` instance, which is used when `a1 = a2`. -/
instance (priority := default - 20) ghost_var_combine_as (γ : GName) (a1 : A) (q1 : Qp)
    (a2 : A) (q2 : Qp) (q : Qp) [h : IsOp .merge q q1 q2] :
    CombineSepAs (ghost_var (GF := GF) γ q1 a1) (ghost_var γ q2 a2) (ghost_var γ q a1) where
  combine_sep_as := by
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %⟨-, rfl⟩
    unfold ghost_var
    rw [h.is_op, show (q1 • q2 : Qp) = q1 + q2 from rfl, Frac.mk_op]
    icombine H1 H2 as $

/-- This is just an instance of fractionality above, but that can be hard to find. -/
theorem ghost_var_split (γ : GName) (a : A) (q1 q2 : Qp) :
    ⊢ ghost_var (GF := GF) γ (q1 + q2) a -∗ ghost_var γ q1 a ∗ ghost_var γ q2 a := by
  iintro ⟨$, $⟩

/-- Update the ghost variable to new value `b`. -/
theorem ghost_var_update (b : A) (γ : GName) (a : A) :
    ⊢ ghost_var (GF := GF) γ 1 a ==∗ ghost_var γ 1 b := by
  unfold ghost_var
  haveI : Exclusive (Frac.mk (1 : Qp) (encodeO a)) := mk_exclusive
  iapply own_update γ _ (Frac.mk 1 (encodeO b)) (.exclusive (mk_valid.mpr DFrac.valid_own_one))

theorem ghost_var_update_2 (b : A) (γ : GName) (a1 : A) (q1 : Qp) (a2 : A) (q2 : Qp)
    (Hq : q1 + q2 = 1) :
    ⊢ ghost_var (GF := GF) γ q1 a1 -∗ ghost_var γ q2 a2 ==∗
      ghost_var γ q1 b ∗ ghost_var γ q2 b := by
  unfold ghost_var
  iintro H1 H2
  ieval (rewrite [← (own_op γ _ _).to_eq])
  iapply own_update_2 γ _ _ _ (Frac.update₂ Hq) $$ H1 H2

theorem ghost_var_update_halves (b : A) (γ : GName) (a1 a2 : A) :
    ⊢ ghost_var (GF := GF) γ (1 : Qp).half a1 -∗ ghost_var γ (1 : Qp).half a2 ==∗
      ghost_var γ (1 : Qp).half b ∗ ghost_var γ (1 : Qp).half b :=
  ghost_var_update_2 b γ a1 _ a2 _ (Qp.half_add_half 1)

/-! ### Framing support -/

instance frame_ghost_var (p : Bool) (γ : GName) (a : A) (q1 q2 q : Qp) [FrameFractionalQp q1 q2 q] :
    Frame p (ghost_var (GF := GF) γ q1 a) (ghost_var γ q2 a) (ghost_var γ q a) :=
  frame_fractional (fun q => ghost_var γ q a) q1 q2 q

end Perennial
