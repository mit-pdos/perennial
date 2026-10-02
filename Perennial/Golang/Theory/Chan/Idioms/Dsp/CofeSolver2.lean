import Iris

/-!
Port of `new/golang/theory/chan/idioms/dsp/cofe_solver_2.v` (from Actris).

A version of the COFE solver for a functor `F T` that is parametrized by a COFE `T`:
for all COFEs `An`, `A` it constructs a COFE `T An A` together with an isomorphism
`F A (T A An) (T A An) ≅ T An A`.

Lean notes:
* iris-lean's solver is `Iris.COFE.OFunctor.Fix` (with `Fix.fold`/`Fix.unfold`); the
  OFE equivalence of iris-lean is Leibniz equality, so the isomorphism laws are equalities.
* Rocq's record `solution_2` is not reproduced: `T F An A` is the carrier, and
  `result_2 F An A : OFE.Iso (F A (T F A An) (T F A An)) (T F An A)` the isomorphism.
* Everything lives in `Type` (universe 0), as needed for ghost state over `IProp`.
-/

set_option autoImplicit false

namespace Perennial
open Iris OFE COFE

namespace cofe_solver_2

section
variable (F : (T : Type) → [COFE T] → OFunctorPre.{0,0,0})
variable [Fcontr : ∀ (T : Type) [COFE T], OFunctorContractive (F T)]
variable [Fcofe : ∀ (T : Type) [COFE T] (Bn B : Type) [COFE Bn] [COFE B], IsCOFE (F T Bn B)]
variable [Finh : ∀ (T : Type) [COFE T] (Bn B : Type) [COFE Bn] [COFE B], Inhabited (F T Bn B)]

/-- Rocq `F_2`: the functor `X ↦ F A (F An X X) (F An X X)`. -/
abbrev F_2 (An : Type) [COFE An] (A : Type) [COFE A] : OFunctorPre :=
  ComposeOF (F A) (F An)

instance F_2_contractive (An : Type) [COFE An] (A : Type) [COFE A] :
    OFunctorContractive (F_2 F An A) :=
  oFunctor_composeOF_contractive_right

instance F_2_cofe (An : Type) [COFE An] (A : Type) [COFE A] (α : Type) [COFE α] :
    IsCOFE (F_2 F An A α α) := Fcofe A _ _

instance F_2_inh (An : Type) [COFE An] (A : Type) [COFE A] :
    Inhabited (F_2 F An A (ULift Unit) (ULift Unit)) := Finh A _ _

/-- Rocq `T`: the solution of `F_2 An A`. -/
def T (An : Type) [COFE An] (A : Type) [COFE A] : Type := OFunctor.Fix (F_2 F An A)

instance T_cofe (An : Type) [COFE An] (A : Type) [COFE A] : COFE (T F An A) :=
  inferInstanceAs (COFE (OFunctor.Fix (F_2 F An A)))

instance T_inhabited (An : Type) [COFE An] (A : Type) [COFE A] : Inhabited (T F An A) :=
  inferInstanceAs (Inhabited (OFunctor.Fix (F_2 F An A)))

/-- The folding isomorphism of the solution `T An A`. -/
def T_fold {An : Type} [COFE An] {A : Type} [COFE A] :
    F A (F An (T F An A) (T F An A)) (F An (T F An A) (T F An A)) -n> T F An A :=
  OFunctor.Fix.fold (F := F_2 F An A)

def T_unfold {An : Type} [COFE An] {A : Type} [COFE A] :
    T F An A -n> F A (F An (T F An A) (T F An A)) (F An (T F An A) (T F An A)) :=
  OFunctor.Fix.unfold (F := F_2 F An A)

theorem T_fold_unfold {An : Type} [COFE An] {A : Type} [COFE A] (x : T F An A) :
    T_fold F (T_unfold F x) = x := OFunctor.Fix.fold_unfold (F := F_2 F An A) x

theorem T_unfold_fold {An : Type} [COFE An] {A : Type} [COFE A] x :
    T_unfold F (T_fold F (An := An) (A := A) x) = x :=
  OFunctor.Fix.unfold_fold (F := F_2 F An A) x

/-- The type of the isomorphism pair at `(An, A)`. -/
abbrev IsoPair (An : Type) [COFE An] (A : Type) [COFE A] : Type :=
  (F A (T F A An) (T F A An) -n> T F An A) × (T F An A -n> F A (T F A An) (T F A An))

def T_iso_fun_aux {An : Type} [COFE An] {A : Type} [COFE A]
    (r : IsoPair F A An) : IsoPair F An A :=
  ((T_fold F).comp (OFunctor.map r.1 r.2), (OFunctor.map r.2 r.1).comp (T_unfold F))

instance T_iso_aux_fun_contractive {An : Type} [COFE An] {A : Type} [COFE A] :
    Contractive (T_iso_fun_aux F (An := An) (A := A)) where
  distLater_dist {n r1 r2} h := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · exact (T_fold F).ne.ne <|
        OFunctorContractive.map_distLater (fun m hm => (h m hm).1) (fun m hm => (h m hm).2) x
    · exact OFunctorContractive.map_distLater (fun m hm => (h m hm).2) (fun m hm => (h m hm).1) _

instance T_iso_aux_fun_ne {An : Type} [COFE An] {A : Type} [COFE A] :
    NonExpansive (T_iso_fun_aux F (An := An) (A := A)) := inferInstance

def T_iso_fun_aux_2 {An : Type} [COFE An] {A : Type} [COFE A]
    (r : IsoPair F An A) : IsoPair F An A :=
  T_iso_fun_aux F (T_iso_fun_aux F r)

instance T_iso_fun_aux_2_contractive {An : Type} [COFE An] {A : Type} [COFE A] :
    Contractive (T_iso_fun_aux_2 F (An := An) (A := A)) where
  distLater_dist h :=
    (T_iso_aux_fun_ne F).ne ((T_iso_aux_fun_contractive F).distLater_dist h)

def T_iso_fun {An : Type} [COFE An] {A : Type} [COFE A] : IsoPair F An A :=
  fixpoint (T_iso_fun_aux_2 F (An := An) (A := A))

theorem T_iso_fun_unfold {An : Type} [COFE An] {A : Type} [COFE A] :
    T_iso_fun F (An := An) (A := A) = T_iso_fun_aux F (T_iso_fun_aux F (T_iso_fun F)) :=
  fixpoint_unfold (T_iso_fun_aux_2 F (An := An) (A := A)).toContractiveHom

theorem T_iso_fun_unfold_1 {An : Type} [COFE An] {A : Type} [COFE A] y :
    (T_iso_fun F (An := An) (A := A)).1 y =
      (T_iso_fun_aux F (T_iso_fun_aux F (T_iso_fun F))).1 y := by
  rw [← T_iso_fun_unfold]

theorem T_iso_fun_unfold_2 {An : Type} [COFE An] {A : Type} [COFE A] y :
    (T_iso_fun F (An := An) (A := A)).2 y =
      (T_iso_fun_aux F (T_iso_fun_aux F (T_iso_fun F))).2 y := by
  rw [← T_iso_fun_unfold]

private theorem iso_laws {An : Type} [COFE An] {A : Type} [COFE A] (φ : IsoPair F An A)
    (hφ : φ = T_iso_fun_aux F (T_iso_fun_aux F φ)) (n : Nat) :
    (∀ y, φ.1 (φ.2 y) ≡{n}≡ y) ∧ (∀ x, φ.2 (φ.1 x) ≡{n}≡ x) := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
  have hl1 : DistLater n (φ.1.comp φ.2) Hom.id := fun m hm y => (IH m hm).1 y
  have hl2 : DistLater n (φ.2.comp φ.1) Hom.id := fun m hm x => (IH m hm).2 x
  generalize hψ : T_iso_fun_aux F φ = ψ at hφ
  -- `ψ.2 ∘ ψ.1 ≈ id` and `ψ.1 ∘ ψ.2 ≈ id` at level `n`
  have hψ21 : ∀ w, ψ.2 (ψ.1 w) ≡{n}≡ w := by
    intro w; subst hψ
    simp only [T_iso_fun_aux, Hom.comp_apply, T_unfold_fold]
    rw [← OFunctor.map_comp]
    exact (OFunctorContractive.map_distLater hl1 hl1 w).trans (OFunctor.map_id w).dist
  have hψ12 : ∀ t, ψ.1 (ψ.2 t) ≡{n}≡ t := by
    intro t; subst hψ
    simp only [T_iso_fun_aux, Hom.comp_apply]
    rw [← OFunctor.map_comp]
    refine .trans ((T_fold F).ne.ne ?_) (T_fold_unfold F t).dist
    exact (OFunctorContractive.map_distLater hl2 hl2 _).trans (OFunctor.map_id _).dist
  refine ⟨fun y => ?_, fun x => ?_⟩
  · rw [hφ]
    simp only [T_iso_fun_aux, Hom.comp_apply]
    rw [← OFunctor.map_comp]
    refine .trans ((T_fold F).ne.ne ?_) (T_fold_unfold F y).dist
    exact (OFunctor.map_ne.ne (fun w => hψ21 w) (fun w => hψ21 w) _).trans (OFunctor.map_id _).dist
  · rw [hφ]
    simp only [T_iso_fun_aux, Hom.comp_apply, T_unfold_fold]
    rw [← OFunctor.map_comp]
    exact (OFunctor.map_ne.ne (x₁ := ψ.1.comp ψ.2) (x₂ := Hom.id) (fun w => hψ12 w) (y₁ := ψ.1.comp ψ.2) (y₂ := Hom.id) (fun w => hψ12 w) _).trans (OFunctor.map_id _).dist

/-- Rocq `result_2`: the isomorphism `F A (T A An) ≅ T An A`. -/
def result_2 (An : Type) [COFE An] (A : Type) [COFE A] :
    OFE.Iso (F A (T F A An) (T F A An)) (T F An A) where
  hom := (T_iso_fun F).1
  inv := (T_iso_fun F).2
  hom_inv := OFE.eq_dist_2 fun n => (iso_laws F _ (T_iso_fun_unfold F) n).1 _
  inv_hom := OFE.eq_dist_2 fun n => (iso_laws F _ (T_iso_fun_unfold F) n).2 _

end
end cofe_solver_2
end Perennial
