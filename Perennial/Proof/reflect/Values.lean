/-
The vocabulary of the specs of `reflect` (`goose/model/overlay/reflect`): what a `reflect.Type`
and a `reflect.Value` of the model hold for a Go type `T`.

* `reflType rt T`: `rt` is the `reflect.Type` of `T`, the model's `rtype` holding `T`'s token
  `go.tok T` (`internal/reflectcore`).
* `reflPtr w T p`: `w` is `reflect.ValueOf(any(p))` for `p : *T`: a direct `Value` of kind
  `Pointer` holding `any(p)`.
* `reflElem v T p`: `v` is `Elem()` of a `reflPtr` for a non-nil `p`: the addressable `Value` of
  the `T` at `p`, which holds `any(p)` (`flagIndir | flagAddr`).
* `reflNew T p`: the zero `T` at `p`, as a typed points-to at every Lean type that represents `T`
  (`reflNew_pointsto`).
-/
module

public import Perennial.Proof.reflect.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace reflect

/-- A kind is below 32 (it fits the kind bits of a flag). -/
theorem kindOf_lt {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (h : go.kindOf u = some k) : k < 27 := by
  unfold go.kindOf at h
  split at h <;> try (cases h; omega)
  simp only [List.find?] at h
  repeat (first | (split at h <;> try (cases h; omega)) | (simp at h; omega))
  all_goals simp_all

/-- The flag bits of a `reflElem`: kind `k`, `flagIndir` and `flagAddr`. -/
theorem elemFlag_bits (k : Nat) (hk : k < 27) :
    (W64 k ||| W64 128 ||| W64 256) &&& W64 31 = W64 k ∧
    (W64 k ||| W64 128 ||| W64 256) ≠ W64 0 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 256 ≠ W64 0 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 352 = W64 256 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 96 = W64 0 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 512 = W64 0 := by
  revert k; decide

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `rt` is the `reflect.Type` of `T`: the interface holding the model's `rtype` of `T`'s token. -/
def reflType (rt : reflect.Type') (T : go.GoType) : Prop :=
  rt = interface.mkOk reflect.rtype.ty #(reflect.rtype.mk (go.tok T))

/-- `w` is `reflect.ValueOf(any(p))` for `p : *T`: direct, of kind `Pointer` (22). -/
def reflPtr (w : reflect.Value) (T : go.GoType) (p : Loc) : Prop :=
  w = reflect.Value.mk (go.tok (go.PointerType T)) (interface.mkOk (go.PointerType T) #p) (W64 22)

/-- `v` is the addressable `reflect.Value` of the `T` at `p` (`Elem()` of a `reflPtr`): it holds
`any(p)`, and its flag is `T`'s kind with `flagIndir` (128) and `flagAddr` (256). -/
def reflElem (v : reflect.Value) (T : go.GoType) (p : Loc) : Prop :=
  ∃ k : Nat, go.kindOf (GoSemanticsFunctions.underlying T) = some k ∧
    v = reflect.Value.mk (go.tok T) (interface.mkOk (go.PointerType T) #p)
      (W64 k ||| W64 128 ||| W64 256)

/-- The zero `T` at `p`: its typed points-to at each Lean type `V` that represents `T`. -/
def reflNew (T : go.GoType) (p : Loc) : IProp GF :=
  iprop(∀ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V)
    (_ : IntoValTyped (GF := GF) V T), p ↦ (zero_val V))

theorem reflNew_pointsto (T : go.GoType) (p : Loc) {V : Type} [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V T] :
    reflNew (GF := GF) T p ⊢ p ↦ (zero_val V) := by
  unfold reflNew
  iintro H
  ispecialize H $$ %V %inferInstance %inferInstance %inferInstance
  iexact H

end defs

end reflect

end Perennial
