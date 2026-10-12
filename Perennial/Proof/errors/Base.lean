/-
Shared definitions of the proofs of the Go `errors` package: its `isPkgInit`, the
predicates of the specs of `Unwrap`, `AsType`, `As` and `Is` (`isUnwrappable`,
`isErrorTree`, `errorIsTree`, ...), lemmas about them, and the (unprovable) initializer
of the global `errorType`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.errors
public import Perennial.GeneratedProof.errors

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace errors

/-- `T` can be the element type of the target `*T` of `errors.As`: its underlying type is an
interface type, or it implements `error` (it is in the type set of `error`: its method set has
`Error() string`). For any other `T`, Go's `As` panics with
`errors: *target must be interface or implement error` (when `err` is not `nil`). Method sets
are uninterpreted in the semantics (`methodSet`), so the second disjunct is, for a concrete
type, an assumption about the semantics (a class such as `context.ErrorStringIsError`). -/
def AsTarget [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] (T : go.GoType) : Prop :=
  (∃ elems, underlying T = go.InterfaceType elems) ∨ go.typeSetContains T go.error = true

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.errors :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.errors :=
  build_get_is_pkg_init_wf

theorem wp_errorType_init :
    {{ (True : IProp GF) }}
      (App (Val errorType.init) (Val #()))
    {{ RET #(); True }} := by
  -- Unprovable: `errorType'init` is opaque (an axiom in Perennial/Code/errors.lean):
  -- `var errorType = reflectlite.TypeOf((*error)(nil)).Elem()` is not translated
  -- (`errors.toml` excludes it and the `internal/reflectlite` import), so goose emits only
  -- an axiomatized `errorType'init : val`, which has no semantics.
  sorry

def isUnwrappable (err : GoError) : IProp GF :=
  match err with
  | interface.nil => iprop(True)
  | interface.ok ii =>
    if methodSet ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #()))
      {{ (err : GoInterfaceOk), RET #(interface.ok err); True }})
    else iprop(True)

instance isUnwrappable_persistent (err : GoError) : Persistent (isUnwrappable (GF := GF) err) := by
  unfold isUnwrappable
  split
  · infer_instance
  · split <;> infer_instance

/-! ### `AsType`

`AsType[E](err)` walks the error tree of `err`, calling the
`Unwrap() error`, `Unwrap() []error` and `As(any) bool` methods of every error
in the tree, so its precondition must specify these methods. We do so with a
pure set `S` of errors that contains `err` and is closed under the `Unwrap`
methods (`isErrorTree`); for each error in `S` the precondition gives the
specs of its methods (persistently) and a typing fact for the type assertion
`err.(E)` (`AsTypeTyped`).

The proof relies on goose translating a bare `return` with blank named results
(`func asType[E error](...) (_ E, _ bool)`) to the zero values; goose used to
emit `![E] "_"`, a free variable (the `_` results are bound anonymously), which
made those return paths stuck. -/

/-- The value extracted by a successful type assertion `ii.(T)` has Lean type
`T'` (for an interface type `T` the assertion returns the interface value
itself, otherwise the dynamic value). This is guaranteed by Go's typing; it is
not derivable in the model, which has no typing of interface values. -/
def AsTypeTyped [GoSemanticsFunctions] (T' : Type) (T : go.GoType) (ii : GoInterfaceOk) : Prop :=
  if go.isInterfaceType (underlying T) then
    go.typeSetContains ii.ty T = true → ∃ x : T', (#x : val) = #(interface.ok ii)
  else ii.ty = T → ∃ x : T', (#x : val) = ii.v

/-- The specs `AsType[T]` needs of one error `ii` of the tree `S`:
* `As(any) bool` (if `ii` has it) is called with a pointer `l` to a `T'`, may
  write the target, and returns a `bool`;
* `Unwrap() error` returns an error in `S`;
* `Unwrap() []error` returns a slice of errors in `S`. -/
def asTypeNode (S : GoError → Prop) (T' : Type) [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) (ii : GoInterfaceOk) : IProp GF :=
  iprop(
    "%Htyped" ∷ ⌜AsTypeTyped T' T ii⌝ ∗
    "#HAs" ∷ (if methodSet ii.ty !! go!"As" = some (go.Signature [go.any] false [go.bool]) then
      iprop(∀ (l : Loc) (v : T'),
        {{ l ↦ v }}
          (App (Val #(methods ii.ty go!"As" ii.v)) (Val #(interface.mkOk (go.PointerType T) #l)))
        {{ (b : Bool) (v' : T'), RET #b; l ↦ v' }})
      else iprop(True)) ∗
    "#HUnwrap" ∷ (if methodSet ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #()))
      {{ (e : GoError), RET #e; ⌜S e⌝ }})
      else if methodSet ii.ty !! go!"Unwrap" =
          some (go.Signature [] false [go.GoType.SliceType go.error]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #()))
      {{ (s : GoSlice) (dq : DFrac) (es : List GoError), RET #s;
          s ↦*{dq} es ∗ ⌜∀ e ∈ es, S e⌝ }})
      else iprop(True)))

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] in
theorem asTypeTyped_val [GoSemanticsFunctions] {T' : Type} [ZeroVal T'] {T : go.GoType}
    {ii : GoInterfaceOk} (h : AsTypeTyped T' T ii) :
    ∃ x : T', (if go.isInterfaceType (underlying T) = true then
        (if go.typeSetContains ii.ty T = true then #(interface.ok ii) else #(zero_val T'))
      else if ii.ty = T then ii.v else #(zero_val T') : val) = #x := by
  unfold AsTypeTyped at h
  split
  · rename_i hI
    simp only [hI, ↓reduceIte] at h
    split
    · obtain ⟨x, hx⟩ := h ‹_›; exact ⟨x, hx.symm⟩
    · exact ⟨_, rfl⟩
  · rename_i hI
    simp only [hI, Bool.false_eq_true, ↓reduceIte] at h
    split
    · obtain ⟨x, hx⟩ := h ‹_›; exact ⟨x, hx.symm⟩
    · exact ⟨_, rfl⟩

/-- Every non-nil error of `S` satisfies `asTypeNode`. -/
abbrev isErrorTree (S : GoError → Prop) (T' : Type) [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) : IProp GF :=
  iprop(□ ∀ ii : GoInterfaceOk, ⌜S (interface.ok ii)⌝ -∗ asTypeNode (GF := GF) S T' T ii)

instance isErrorTree_persistent (S : GoError → Prop) (T' : Type) [ZeroVal T']
    [TypedPointsto (GF := GF) T'] (T : go.GoType) :
    Persistent (isErrorTree (GF := GF) S T' T) := by
  unfold isErrorTree; infer_instance

/-- `P` under an opaque name, to keep the Löb induction hypothesis of `wp_asType`
(which contains `▷`s) away from the later stripping that the proof mode does for
every hypothesis mentioning `▷` at every symbolic execution step. -/
def asTypeHide (P : IProp GF) : IProp GF := P

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx hG sem package_sem in
theorem asTypeHide_intro {P Q : IProp GF} : (□ asTypeHide P -∗ Q) ⊢ (□ P -∗ Q) := .rfl

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx hG sem package_sem in
theorem asTypeHide_elim {P Q : IProp GF} : (□ P -∗ Q) ⊢ (□ asTypeHide P -∗ Q) := .rfl

/-- A leaf of an error tree: an error without an `As(any) bool` or `Unwrap` method (an
`errors.New` error, a gRPC status error, ...), so that `AsType` and `As` only check its type. -/
def isLeafError [GoSemanticsFunctions] (ii : GoInterfaceOk) : Prop :=
  methodSet ii.ty !! go!"As" ≠ some (go.Signature [go.any] false [go.bool]) ∧
  methodSet ii.ty !! go!"Unwrap" ≠ some (go.Signature [] false [go.error]) ∧
  methodSet ii.ty !! go!"Unwrap" ≠ some (go.Signature [] false [go.GoType.SliceType go.error])

/-- A leaf error (whose value has the Lean type of the target's Go type when its own type is the
target's, `AsTypeTyped`) is a one-error tree. -/
theorem isErrorTree_leaf (ii : GoInterfaceOk) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} (hleaf : isLeafError ii)
    (htyped : AsTypeTyped T' T ii) :
    ⊢ isErrorTree (GF := GF) (· = interface.ok ii) T' T := by
  obtain ⟨hAs, hU1, hU2⟩ := hleaf
  iintro !> %ii' %h
  cases h
  unfold asTypeNode
  simp only [hAs, hU1, hU2, ↓reduceIte]
  iframe %
  isplitr <;> itrivial

/-! ### `Is`

`Is(err, target)` walks the error tree of `err` as `AsType` does, checking at each error `e`
whether `e == target` (when `target`'s dynamic type is comparable, which it finds by reflection)
and calling `e.Is(target)` if `e` has an `Is(error) bool` method. Its precondition is the
analogue of `isErrorTree`: a pure set `S` of errors containing `err`, closed under the `Unwrap`
methods, and for each error in it the specs of its methods (`errorIsNode`); a predicate `M` says
what an `Is` method's `true` means.

The tree walk `is(err, target, targetComparable)` is translated (`wp_is`). `Is` itself is a
trusted model (`TrustedCode/errors.lean`): Go's `Is` with its one reflection call,
`reflectlite.TypeOf(target).Comparable()`, replaced by `true`, which is Go's answer for the
`nil` and pointer targets `wp_Is` admits. -/

/-- A pointer error: a non-nil error whose dynamic type is a pointer type `*T` and whose value
is a pointer, such as `errors.New`'s `*errorString` (`wp_New_ptr`). Go's `==` on two such errors
is the equality of their types and pointers, Lean's equality of the interface values. -/
def IsPointerError [FfiSyntax] [GoGlobalContext] (ii : GoInterfaceOk) : Prop :=
  ∃ (T : go.GoType) (l : Loc), ii.ty = go.PointerType T ∧ ii.v = #l

/-- The specs `Is(err, target)` needs of one error `ii` of the tree `S`:
* `Is(error) bool` (if `ii` has it) is called with `target` and returns a `bool`, `true` only if
  `M ii`;
* `Unwrap() error` returns an error in `S`;
* `Unwrap() []error` returns a slice of errors in `S`. -/
def errorIsNode (S : GoError → Prop) (M : GoInterfaceOk → Prop) (target : GoError)
    (ii : GoInterfaceOk) : IProp GF :=
  iprop(
    "#HIs" ∷ (if methodSet ii.ty !! go!"Is" = some (go.Signature [go.error] false [go.bool]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Is" ii.v)) (Val #target))
      {{ (b : Bool), RET #b; ⌜b = true → M ii⌝ }})
      else iprop(True)) ∗
    "#HUnwrap" ∷ (if methodSet ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #()))
      {{ (e : GoError), RET #e; ⌜S e⌝ }})
      else if methodSet ii.ty !! go!"Unwrap" =
          some (go.Signature [] false [go.GoType.SliceType go.error]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #()))
      {{ (s : GoSlice) (dq : DFrac) (es : List GoError), RET #s;
          s ↦*{dq} es ∗ ⌜∀ e ∈ es, S e⌝ }})
      else iprop(True)))

/-- Every non-nil error of `S` satisfies `errorIsNode`. -/
abbrev errorIsTree (S : GoError → Prop) (M : GoInterfaceOk → Prop) (target : GoError) :
    IProp GF :=
  iprop(□ ∀ ii : GoInterfaceOk, ⌜S (interface.ok ii)⌝ -∗ errorIsNode (GF := GF) S M target ii)

/-- A leaf error without an `Is(error) bool` method is a one-error tree, for any `M`. -/
theorem errorIsTree_leaf (ii : GoInterfaceOk) (M : GoInterfaceOk → Prop) (target : GoError)
    (hleaf : isLeafError ii)
    (hIs : methodSet ii.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])) :
    ⊢ errorIsTree (GF := GF) (· = interface.ok ii) M target := by
  obtain ⟨-, hU1, hU2⟩ := hleaf
  iintro !> %ii' %h
  cases h
  unfold errorIsNode
  simp only [hIs, hU1, hU2, ↓reduceIte]
  isplitr <;> itrivial

/-- The errors of the tree `S` whose dynamic type is that of `target` hold a pointer, as
`target` does for a pointer error: Go's typing, which the model (with no typing of interface
values) does not have. What Go's `err == target` needs to compare two such errors. -/
def TreeTyped [FfiSyntax] [GoGlobalContext] (S : GoError → Prop) (target : GoError) : Prop :=
  ∀ ii tii, S (interface.ok ii) → target = interface.ok tii → ii.ty = tii.ty →
    ∃ l : Loc, ii.v = #l

omit package_sem in
/-- A one-error tree of a pointer error is `TreeTyped`. -/
theorem treeTyped_pointer (ii : GoInterfaceOk) (target : GoError) (h : IsPointerError ii) :
    TreeTyped (· = interface.ok ii) target := by
  intro ii' _ hii' _ _
  cases hii'
  obtain ⟨_, l, -, hl⟩ := h
  exact ⟨l, hl⟩

end wps

end errors

end Perennial
