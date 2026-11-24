/-
Shared definitions of the proofs of `internal/reflectcore`: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.internal.reflectcore
public import Perennial.GeneratedProof.internal.reflectcore
public import Perennial.Proof.«unsafe».Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.reflectcore

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.reflectcore :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.reflectcore :=
  build_get_is_pkg_init_wf

end init

end internal.reflectcore

namespace reflect

/-! ## The shapes of types: `isZeroSize` and `isDirectIface` -/

section shapes
variable [GooseExts] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- The kinds whose values an interface stores in its data word: `Chan` (18), `Func` (19),
`Map` (21), `Pointer` (22), `UnsafePointer` (26). -/
def directKind (k : Nat) : Bool := decide (k = 18 ∨ k = 19 ∨ k = 21 ∨ k = 22 ∨ k = 26)

/-- The result of a loop over some booleans that returns false at the first false one, and true
after the last: none if one before the first false one is undefined. -/
def allTrue : List (Option Bool) → Option Bool
  | [] => some true
  | some true :: r => allTrue r
  | some false :: _ => some false
  | none :: _ => none

/-- `isZeroSize(t)` (the model's, `type.go`) for the type `t`, computed with at most `n` nested
calls: none when `n` is too small, or a type it reaches has no kind, or an array's length or a
struct's field count is not below `2^63` (the model's loop counters are Go `int`s).
* an array: whether its length is 0 or its element type is zero-size;
* a struct: whether all its fields' types are zero-size;
* another type: false. -/
def zeroSizeN : Nat → go.GoType → Option Bool
  | 0, _ => none
  | n + 1, t =>
    match underlying t with
    | go.ArrayType len e =>
      if 0 ≤ len ∧ len < 2 ^ 63 then (if len = 0 then some true else zeroSizeN n e) else none
    | go.StructType fs =>
      if fs.length < 2 ^ 63 then allTrue (fs.map fun f => zeroSizeN n (go.fieldDeclType f))
      else none
    | u => (go.kindOf u).map fun _ => false

/-- `isDirectIface(t)` (the model's, `type.go`: gc's `types.IsDirectIface`) for the type `t`,
computed with at most `n` nested calls, none in the cases of `zeroSizeN`:
* an array: whether its length is 1 and its element type is direct;
* a struct: whether it has a field, its last field's type is direct, and its other fields'
  types are zero-size;
* another type: whether its kind is a `directKind`. -/
def directIfaceN : Nat → go.GoType → Option Bool
  | 0, _ => none
  | n + 1, t =>
    match underlying t with
    | go.ArrayType len e =>
      if 0 ≤ len ∧ len < 2 ^ 63 then (if len = 1 then directIfaceN n e else some false)
      else none
    | go.StructType fs =>
      if fs.length < 2 ^ 63 then
        match fs.getLast? with
        | none => some false
        | some f =>
          match directIfaceN n (go.fieldDeclType f) with
          | some true => allTrue (fs.dropLast.map fun f => zeroSizeN n (go.fieldDeclType f))
          | some false => some false
          | none => none
      else none
    | u => (go.kindOf u).map directKind


omit [GooseExts] go_gctx [GoSemanticsFunctions] in
/-- Only an array type has kind `Array`, and only a struct type kind `Struct`. -/
theorem kindOf_ne_17_25 {u : go.GoType} {k : Nat} (hk : go.kindOf u = some k)
    (ha : ∀ len e, u = go.ArrayType len e → False) (hs : ∀ fs, u = go.StructType fs → False) :
    k ≠ 17 ∧ k ≠ 25 := by
  unfold go.kindOf at hk
  split at hk <;> try (first | (exfalso; exact ha _ _ rfl) | (exfalso; exact hs _ rfl) | (cases hk; omega))
  simp only [List.find?] at hk
  repeat (first | (split at hk <;> try (cases hk; omega)) | (simp at hk; omega))
  all_goals simp_all

omit go_gctx in
/-- The type of a kind other than `Array` and `Struct`: `directIfaceN` is its kind's
`directKind`, at any fuel. -/
theorem directIfaceN_of_kind {t u : go.GoType} [t ↓u u] {k : Nat} (n : Nat)
    (hk : go.kindOf u = some k) (h17 : k ≠ 17) (h25 : k ≠ 25) :
    directIfaceN (n + 1) t = some (directKind k) := by
  have hu : underlying t = u := go.is_underlying
  simp only [directIfaceN, hu]
  split
  · simp [go.kindOf] at hk; omega
  · simp [go.kindOf] at hk; omega
  · simp [hk]

omit go_gctx in
/-- A struct whose last field's type has a kind outside `directKind`, `Array` and `Struct` (as
`int64`) is not direct. -/
theorem directIfaceN_struct_last {t : go.GoType} {fs : List go.field_decl}
    [t ↓u go.StructType fs] {f : go.field_decl} {u : go.GoType} {k : Nat} (n : Nat)
    (hlen : fs.length < 2 ^ 63) (hlast : fs.getLast? = some f)
    (hfu : underlying (go.fieldDeclType f) = u) (hk : go.kindOf u = some k) (h17 : k ≠ 17)
    (h25 : k ≠ 25) (hd : directKind k = false) :
    directIfaceN (n + 2) t = some false := by
  have hu : underlying t = go.StructType fs := go.is_underlying
  haveI : go.fieldDeclType f ↓u u := ⟨hfu⟩
  have hf := directIfaceN_of_kind (t := go.fieldDeclType f) n hk h17 h25
  rw [hd] at hf
  conv => lhs; unfold directIfaceN
  simp only [hu, hlen, ite_true, hlast, hf]

end shapes

end reflect

end Perennial
