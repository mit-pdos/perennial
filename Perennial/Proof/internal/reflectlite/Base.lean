/-
Shared definitions of the proofs of `internal/reflectlite` (the Go model,
`goose/model/overlay/internal/reflectlite`): its `isPkgInit` (no package variables).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.internal.reflectlite
public import Perennial.GeneratedProof.internal.reflectlite
public import Perennial.Proof.internal.abi.Base
public import Perennial.Proof.internal.gomodel.Base
public import Perennial.Proof.internal.reflectcore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.reflectlite

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.reflectlite :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.reflectlite :=
  build_get_is_pkg_init_wf

end init

/-- A kind is below 27. -/
theorem kindOf_lt {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (h : go.kindOf u = some k) : k < 27 := by
  unfold go.kindOf at h
  split at h <;> try (cases h; omega)
  simp only [List.find?] at h
  repeat (first | (split at h <;> try (cases h; omega)) | (simp at h; omega))
  all_goals simp_all

/-- `Kind(TypeKind(t))` (`int` to `abi.Kind`, a `uint8`) of a kind `k` is `W8 k`. -/
theorem kind_w8 {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (h : go.kindOf u = some k) : (W8 (sint.Z (W64 (k : Int))) : w8) = W8 (k : Int) := by
  have hlt := kindOf_lt h
  have hz : sint.Z (W64 (k : Int)) = k := by
    simp only [sint.Z, W64, BitVec.toInt_ofInt]
    rw [Int.bmod_def]
    split <;> omega
  rw [hz]

/-- A kind other than `Struct` is another `abi.Kind` than `Struct`'s. -/
theorem kind_ne_struct {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (h : go.kindOf u = some k) (hk : k ≠ 25) : (W8 (sint.Z (W64 (k : Int))) : w8) ≠ W8 25 := by
  rw [kind_w8 h]
  have key : ∀ k : Nat, k < 27 → k ≠ 25 → (W8 (k : Int) : w8) ≠ W8 25 := by decide
  exact key k (kindOf_lt h) hk

/-- `Kind(TypeKind(t))` (`int` to `abi.Kind`) of a kind `k` is `W8 k`, for a literal `k`. -/
theorem kind_w8n : ∀ k : Nat, k < 27 → (W8 (sint.Z (W64 (k : Int))) : w8) = W8 (k : Int) := by
  decide

/-- `Kind(x)` (`uintptr` to `abi.Kind`) of a kind `k` (`flag.kind`) is `W8 k`. -/
theorem kind_u8 : ∀ k : Nat, k < 27 → (W8 (uint.Z (W64 (k : Int))) : w8) = W8 (k : Int) := by
  decide

/-- The flag bits of a `Value` of kind `k`: direct (`k`), indirect (`k | flagIndir`), and the
addressable one of a variable (`k | flagIndir | flagAddr`). -/
theorem flag_bits : ∀ k : Nat, k < 27 → 0 < k →
    W64 k ≠ W64 0 ∧ (W64 k ||| W64 128) ≠ W64 0 ∧
    W64 k &&& W64 31 = W64 k ∧ (W64 k ||| W64 128) &&& W64 31 = W64 k ∧
    W64 k &&& W64 128 = W64 0 ∧ (W64 k ||| W64 128) &&& W64 128 = W64 128 ∧
    W64 k &&& W64 96 = W64 0 ∧ (W64 k ||| W64 128) &&& W64 96 = W64 0 ∧
    (W64 k ||| W64 128 ||| W64 256) ≠ W64 0 ∧ (W64 k ||| W64 128 ||| W64 256) &&& W64 96 = W64 0 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 256 ≠ W64 0 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 31 = W64 k ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 128 = W64 128 := by
  decide

/-- `Elem()`'s flag on the direct `Value` of a pointer (kind 22): `k | flagIndir | flagAddr`. -/
theorem elem_flag : ∀ k : Nat, k < 27 →
    W64 22 &&& W64 96 ||| W64 128 ||| W64 256 ||| W64 k = W64 k ||| W64 128 ||| W64 256 := by
  decide

/-- `assignTo`'s flag of a `Value` of kind `k`, direct or indirect: its `flagIndir` bit. -/
theorem assign_flag_bits : ∀ k : Nat, k < 27 →
    (W64 k &&& (W64 256 ||| W64 128) ||| W64 0 ||| W64 k) &&& W64 128 = W64 k &&& W64 128 ∧
    ((W64 k ||| W64 128) &&& (W64 256 ||| W64 128) ||| W64 0 ||| W64 k) &&& W64 128 =
      (W64 k ||| W64 128) &&& W64 128 := by
  decide

/-- Different kinds are different `abi.Kind`s. -/
theorem kind_ne_aux : ∀ a : Nat, a < 27 → ∀ b : Nat, b < 27 → a ≠ b →
    (W8 (a : Int) : w8) ≠ W8 (b : Int) := by
  decide

theorem kind_ne (a b : Nat) (ha : a < 27) (hb : b < 27) (h : a ≠ b) :
    (W8 (a : Int) : w8) ≠ W8 (b : Int) :=
  kind_ne_aux a ha b hb h

/-- A kind other than a constant kind is another `abi.Kind`. -/
theorem kne_18 : ∀ a : Nat, a < 27 → a ≠ 18 → (W8 (a : Int) : w8) ≠ W8 18 := by
  decide

theorem kne_19 : ∀ a : Nat, a < 27 → a ≠ 19 → (W8 (a : Int) : w8) ≠ W8 19 := by
  decide

theorem kne_20 : ∀ a : Nat, a < 27 → a ≠ 20 → (W8 (a : Int) : w8) ≠ W8 20 := by
  decide

theorem kne_22 : ∀ a : Nat, a < 27 → a ≠ 22 → (W8 (a : Int) : w8) ≠ W8 22 := by
  decide

theorem kne_25 : ∀ a : Nat, a < 27 → a ≠ 25 → (W8 (a : Int) : w8) ≠ W8 25 := by
  decide

/-- `abi.Kind`s of literal flags. -/
theorem u8_lit20 : (W8 (uint.Z (W64 20)) : w8) = W8 20 := by decide
theorem u8_lit22 : (W8 (uint.Z (W64 22)) : w8) = W8 22 := by decide

/-- Different kinds are different `int`s. -/
theorem kind_ne64_aux : ∀ a : Nat, a < 27 → ∀ b : Nat, b < 27 → a ≠ b →
    (W64 (a : Int) : w64) ≠ W64 (b : Int) := by
  decide

theorem kind_ne64 (a b : Nat) (ha : a < 27) (hb : b < 27) (h : a ≠ b) :
    (W64 (a : Int) : w64) ≠ W64 (b : Int) :=
  kind_ne64_aux a ha b hb h

/-- A kind is not `Interface` (20) if its type is not an interface type. -/
theorem kindOf_ne_20 {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (hk : go.kindOf u = some k) (hi : go.isInterfaceType u = false) : k ≠ 20 := by
  unfold go.kindOf at hk
  split at hk <;> try (first | (cases hk; omega) | (simp [go.isInterfaceType] at hi))
  simp only [List.find?] at hk
  repeat (first | (split at hk <;> try (cases hk; omega)) | (simp at hk; omega))
  all_goals simp_all

/-- A kind is not `Struct` (25) if its type is not a struct type. -/
theorem kindOf_ne_25 {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (hk : go.kindOf u = some k) (hs : ∀ fs, u = go.StructType fs → False) : k ≠ 25 := by
  unfold go.kindOf at hk
  split at hk <;> try (first | (exfalso; exact hs _ rfl) | (cases hk; omega))
  simp only [List.find?] at hk
  repeat (first | (split at hk <;> try (cases hk; omega)) | (simp at hk; omega))
  all_goals simp_all

/-- Only a pointer type has kind `Pointer` (22). -/
theorem kindOf_22 {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (hk : go.kindOf u = some k) (h22 : k = 22) : ∃ e, u = go.PointerType e := by
  refine Classical.byContradiction fun hne => ?_
  have : k ≠ 22 := by
    unfold go.kindOf at hk
    split at hk <;> try (first | (exfalso; exact hne ⟨_, rfl⟩) | (cases hk; omega))
    simp only [List.find?] at hk
    repeat (first | (split at hk <;> try (cases hk; omega)) | (simp at hk; omega))
    all_goals simp_all
  exact this h22

/-- Only a channel type has kind `Chan` (18). -/
theorem kindOf_18 {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (hk : go.kindOf u = some k) (h18 : k = 18) : ∃ d e, u = go.ChannelType d e := by
  refine Classical.byContradiction fun hne => ?_
  have : k ≠ 18 := by
    unfold go.kindOf at hk
    split at hk <;> try (first | (exfalso; exact hne ⟨_, _, rfl⟩) | (cases hk; omega))
    simp only [List.find?] at hk
    repeat (first | (split at hk <;> try (cases hk; omega)) | (simp at hk; omega))
    all_goals simp_all
  exact this h18

/-- Only a function type has kind `Func` (19). -/
theorem kindOf_19 {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (hk : go.kindOf u = some k) (h19 : k = 19) : ∃ sig, u = go.FunctionType sig := by
  refine Classical.byContradiction fun hne => ?_
  have : k ≠ 19 := by
    unfold go.kindOf at hk
    split at hk <;> try (first | (exfalso; exact hne ⟨_, rfl⟩) | (cases hk; omega))
    simp only [List.find?] at hk
    repeat (first | (split at hk <;> try (cases hk; omega)) | (simp at hk; omega))
    all_goals simp_all
  exact this h19

/-- A kind is not 0 (`Invalid`). -/
theorem kindOf_pos {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (h : go.kindOf u = some k) : 0 < k := by
  unfold go.kindOf at h
  split at h <;> try (cases h; omega)
  simp only [List.find?] at h
  repeat (first | (split at h <;> try (cases h; omega)) | (simp at h; omega))
  all_goals simp_all

/-- A kind of an interface type is `Interface` (20). -/
theorem kindOf_interface {elems : List go.InterfaceElem} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] :
    go.kindOf (go.InterfaceType elems) = some 20 := by
  simp [go.kindOf]

/-- One method call: unfold it and execute. -/
macro "wp_meth1" : tactic => `(tactic| (wp_method_call; wp_call; try wp_auto))

/-- Symbolically execute the next method calls (`wp_method_call; wp_call`) as far as they go. -/
macro "wp_meths" : tactic => `(tactic| repeat (wp_method_call; wp_call; try wp_auto))

section layout
variable [GooseExts] [GoLocalContext] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

omit go_gctx in
/-- A struct type whose `directIfaceN` is defined has fewer than `2^63` fields. -/
theorem directIfaceN_struct_len {n : Nat} {t : go.GoType} {b : Bool} {fs : List go.field_decl}
    (h : reflect.directIfaceN n t = some b) (hu : underlying t = go.StructType fs) :
    fs.length < 2 ^ 63 := by
  cases n with
  | zero => simp [reflect.directIfaceN] at h
  | succ n =>
    have hm := reflect.notLayoutModelled_of_directIfaceN h
    simp only [reflect.directIfaceN, hu, hm, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · assumption
    · cases h

/-- A defined type without type arguments (`isDefined` of the model: `go.identByName` and not a
pointer to its element type). -/
def isDefinedT : go.GoType → Bool
  | go.Named _ [] => true
  | _ => false

end layout

section repr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `xv` is `ValueOf(any(x))` for a value `x : V` of a non-interface type `t` of kind `k`: for a
type whose values an interface stores in its data word (`directIfaceN n t = some true`), the
direct `Value` holding the interface; for another, the indirect `Value` holding `any(q)` for a
variable `q` holding `x`. -/
def valueOfRepr {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (xv : Value) (t : go.GoType)
    (k : Nat) (x : V) : IProp GF :=
  iprop(⌜(∃ n, reflect.directIfaceN n t = some true) ∧
      xv = Value.mk (go.tok t) (interface.mkOk t #x) (W64 k)⌝ ∨
    ∃ q : Loc, ⌜(∃ n, reflect.directIfaceN n t = some false) ∧
      xv = Value.mk (go.tok t) (interface.mkOk (go.PointerType t) #q) (W64 k ||| W64 128)⌝ ∗
      q ↦ x)

/-- The pure facts of a `valueOfRepr`: its token and its flag's bits. -/
theorem valueOfRepr_facts {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (xv : Value)
    (t : go.GoType) (k : Nat) (x : V) (hk : k < 27) (hk0 : 0 < k) :
    valueOfRepr (GF := GF) xv t k x ⊢
      ⌜xv.typ_' = go.tok t ∧ xv.flag' ≠ W64 0 ∧ xv.flag' &&& W64 31 = W64 k ∧
        xv.flag' &&& W64 96 = W64 0 ∧ (xv.flag' = W64 k ∨ xv.flag' = W64 k ||| W64 128)⌝ ∗
      valueOfRepr (GF := GF) xv t k x := by
  have hb := flag_bits k hk hk0
  unfold valueOfRepr
  iintro H
  icases H with (⟨%hd, %hxv⟩ | ⟨%q, ⟨%hd, %hxv⟩, Hq⟩)
  · subst hxv
    isplitr
    · ipureintro
      exact ⟨rfl, hb.1, hb.2.2.1, hb.2.2.2.2.2.2.1, Or.inl rfl⟩
    ileft
    ipureintro
    exact ⟨hd, rfl⟩
  · subst hxv
    isplitr
    · ipureintro
      exact ⟨rfl, hb.2.1, hb.2.2.2.1, hb.2.2.2.2.2.2.2.1, Or.inr rfl⟩
    iright
    iexists q
    iframe
    ipureintro
    exact ⟨hd, rfl⟩

end repr

end internal.reflectlite

end Perennial
