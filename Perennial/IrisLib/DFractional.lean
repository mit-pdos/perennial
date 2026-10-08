/-
This library is a (partial) copy of the Iris fractional library, adapted to
dfrac. We do extend the interface to include dfrac-specific laws.
-/
import Iris

namespace Perennial
open Iris Iris.Std BI OFE ProofMode

section classes
variable {PROP : Type _} [BI PROP] [BIUpdate PROP]

class DFractional (Φ : DFrac → PROP) : Prop where
  dfractional (dp dq : DFrac) : Φ (dp • dq) ⊣⊢ Φ dp ∗ Φ dq
  dfractional_persistent : Persistent (Φ .discard)
  dfractional_persist (dq : DFrac) : Φ dq ⊢ |==> Φ .discard

export DFractional (dfractional dfractional_persistent dfractional_persist)

/-- The `AsDFractional` typeclass is analogous to `AsFractional`: it is only
there to assist higher-order unification for APIs that want to take a `P` that
has to be turned into `Φ dq`. -/
class AsDFractional (P : PROP) (Φ : DFrac → PROP) (dq : DFrac) : Prop where
  as_dfractional : P ⊣⊢ Φ dq
  as_dfractional_dfractional : DFractional Φ

export AsDFractional (as_dfractional as_dfractional_dfractional)

end classes

section dfractional
variable {PROP : Type _} [BI PROP] [BIUpdate PROP] {P P1 P2 : PROP} {Φ Ψ : DFrac → PROP}

theorem fractional_of_dfractional (Φ : DFrac → PROP) [h : DFractional Φ] :
    Fractional (fun q => Φ (.own q)) where
  fractional p q := h.dfractional (.own p) (.own q)

/- TODO: not sure if this is a good instance to have. -/
set_option synthInstance.checkSynthOrder false in
instance (priority := low) as_fractional_of_as_dfractional {q : Qp}
    [h : AsDFractional P Φ (.own q)] :
    AsFractional P ioΦ (fun q => Φ (.own q)) ioq q where
  as_fractional := h.as_dfractional
  as_fractional_fractional :=
    haveI := h.as_dfractional_dfractional; fractional_of_dfractional Φ

instance (priority := low) dfractional_as_dfractional [h : DFractional Φ] (dq : DFrac) :
    AsDFractional (Φ dq) Φ dq where
  as_dfractional := .rfl
  as_dfractional_dfractional := h

/-- A theorem rather than an instance, since `Φ` cannot be
determined from `Persistent P`. -/
theorem as_dfractional_persistent [h : AsDFractional P Φ .discard] : Persistent P where
  persistent :=
    haveI := h.as_dfractional_dfractional.dfractional_persistent
    h.as_dfractional.1.trans ((Persistent.persistent).trans (persistently_mono h.as_dfractional.2))

instance (priority := default - 10) persistent_dfractional
    [Persistent P] [TCOr (Affine P) (Absorbing P)] : DFractional (fun _ => P) where
  dfractional _ _ := persistent_sep_dup
  dfractional_persistent := inferInstance
  dfractional_persist _ := BIUpdate.intro

instance dfractional_sep [hΦ : DFractional Φ] [hΨ : DFractional Ψ] :
    DFractional (fun dq => iprop(Φ dq ∗ Ψ dq)) where
  dfractional p q := (sep_congr (hΦ.dfractional p q) (hΨ.dfractional p q)).trans sep_sep_sep_comm
  dfractional_persistent :=
    haveI := hΦ.dfractional_persistent; haveI := hΨ.dfractional_persistent; inferInstance
  dfractional_persist dq :=
    (sep_mono (hΦ.dfractional_persist dq) (hΨ.dfractional_persist dq)).trans bupd_sep

theorem dfractional_split {dq1 dq2 : DFrac} [h : AsDFractional P Φ (dq1 • dq2)] :
    P ⊣⊢ Φ dq1 ∗ Φ dq2 :=
  h.as_dfractional.trans (h.as_dfractional_dfractional.dfractional dq1 dq2)

set_option synthInstance.checkSynthOrder false in
instance (priority := default - 10) from_sep_dfractional {dq1 dq2 : DFrac}
    [h : AsDFractional P Φ (dq1 • dq2)] : FromSep P (Φ dq1) (Φ dq2) where
  from_sep := (h.as_dfractional_dfractional.dfractional dq1 dq2).2.trans h.as_dfractional.2

set_option synthInstance.checkSynthOrder false in
/-- dfrac-based `CombineSepAs` instances need lower priority than
`combineSepAsFractional` so that two `DFrac.own`s combine. -/
instance (priority := default - 20) combine_sep_as_dfractional {dq1 dq2 : DFrac}
    [h1 : AsDFractional P1 Φ dq1] [h2 : AsDFractional P2 Φ dq2] :
    CombineSepAs P1 P2 (Φ (dq1 • dq2)) where
  combine_sep_as :=
    (sep_mono h1.as_dfractional.1 h2.as_dfractional.1).trans
      (h1.as_dfractional_dfractional.dfractional dq1 dq2).2

set_option synthInstance.checkSynthOrder false in
instance (priority := default - 10) into_sep_dfractional {dq1 dq2 : DFrac}
    [h : AsDFractional P Φ (dq1 • dq2)] : IntoSep P (Φ dq1) (Φ dq2) where
  into_sep := h.as_dfractional.1.trans (h.as_dfractional_dfractional.dfractional dq1 dq2).1

instance dfractional_big_sepL {A : Type _} {l : List A} {Ψ : Nat → A → DFrac → PROP}
    [h : ∀ k x, DFractional (Ψ k x)] :
    DFractional (fun dq => iprop([∗list] k ↦ x ∈ l, Ψ k x dq)) where
  dfractional p q :=
    ⟨(BigSepL.bigSepL_mono_of_forall fun {_ _} => (DFractional.dfractional p q).1).trans
      BigSepL.bigSepL_sep_eqv.1,
     BigSepL.bigSepL_sep_eqv.2.trans
      (BigSepL.bigSepL_mono_of_forall fun {_ _} => (DFractional.dfractional p q).2)⟩
  dfractional_persistent :=
    haveI := fun k x => (h k x).dfractional_persistent; inferInstance
  dfractional_persist dq :=
    (BigSepL.bigSepL_mono_of_forall fun {_ _} => DFractional.dfractional_persist dq).trans
      (BigSepL.bigSepL_bupd _ l)

private theorem big_sepL2_bupd_mono {A B : Type _} :
    ∀ (l1 : List A) (l2 : List B) (Φ Ψ : Nat → A → B → PROP),
    (∀ k x1 x2, Φ k x1 x2 ⊢ |==> Ψ k x1 x2) →
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ |==> [∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2
  | [], [], _, _, _ => BIUpdate.intro
  | [], _ :: _, _, _, _ => false_elim
  | _ :: _, [], _, _, _ => false_elim
  | _ :: xs1, _ :: xs2, Φ, Ψ, h =>
    (sep_mono (h 0 _ _) (big_sepL2_bupd_mono xs1 xs2 (fun n => Φ (n + 1)) (fun n => Ψ (n + 1))
      fun k => h (k + 1))).trans bupd_sep

instance dfractional_big_sepL2 {A B : Type _} {l1 : List A} {l2 : List B}
    {Ψ : Nat → A → B → DFrac → PROP} [h : ∀ k x1 x2, DFractional (Ψ k x1 x2)] :
    DFractional (fun dq => iprop([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2 dq)) where
  dfractional p q :=
    (BigSepL2.bigSepL2_eqv_of_forall_eqv fun {_ _ _} => DFractional.dfractional p q).trans
      BigSepL2.bigSepL2_sep_eqv
  dfractional_persistent :=
    haveI := fun k x1 x2 => (h k x1 x2).dfractional_persistent; inferInstance
  dfractional_persist dq :=
    big_sepL2_bupd_mono l1 l2 _ _ fun _ _ _ => DFractional.dfractional_persist dq

theorem dfractional_update_to_dfrac [BIAffine PROP] (Φ : DFrac → PROP) [h : DFractional Φ]
    (dq : DFrac) (Hvalid : ✓ dq) : Φ (.own 1) ⊢ |==> Φ dq := by
  -- split `own 1` into `own q • own q'` when `q < 1`
  have split : ∀ (q : Qp) (hq : q.val < 1),
      Φ (.own 1) ⊢ Φ (.own q) ∗ Φ (.own ⟨1 - q.val, by grind⟩) := fun q hq => by
    have : (1 : Qp) = q + ⟨1 - q.val, by grind⟩ := Subtype.ext (by simp; grind)
    rw [this]; exact (h.dfractional (.own q) (.own ⟨1 - q.val, by grind⟩)).1
  cases dq with
  | own q =>
    have hq : q.val ≤ 1 := Hvalid
    by_cases hlt : q.val < 1
    · exact (split q hlt).trans (sep_elim_left.trans BIUpdate.intro)
    · have : q = 1 := Subtype.ext (by grind)
      subst this; exact BIUpdate.intro
  | discard => exact h.dfractional_persist _
  | ownDiscard q =>
    have hq : q.val < 1 := Hvalid
    refine (split q hq).trans ?_
    refine (sep_mono BIUpdate.intro (h.dfractional_persist _)).trans (bupd_sep.trans ?_)
    exact bupd_mono (h.dfractional (.own q) .discard).2

end dfractional
end Perennial
