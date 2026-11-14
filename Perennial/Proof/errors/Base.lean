/-
Shared definitions of the proofs of the Go `errors` package: its `isPkgInit`, the
predicates of the specs of `Unwrap`, `AsType`, `As` and `Is` (`isUnwrappable`,
`isErrorTree`, `errorIsTree`, ...), and lemmas about them.
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
`errors: *target must be interface or implement error` (when `err` is not `nil`). For a
named type of a translated package, `go_type_set` proves or refutes the second disjunct from
the type's method set (its package's `Assumptions`). -/
def AsTarget [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] (T : go.GoType) : Prop :=
  (∃ elems, underlying T = go.InterfaceType elems) ∨ go.typeSetContains T go.error = true

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-! ### Package variables made by `errors.New`

`var X = errors.New(msg)` allocates a fresh `errorString{s: msg}` and stores the pointer in `X`,
which Go never writes after initialization. `newVar X msg` keeps both cells, for good: `X`'s,
and the `errorString`'s field `s`, so that two such variables whose messages differ hold
different pointers (`newVar_ne`: `io.EOF` is not `io.ErrUnexpectedEOF`, nor `errors.ErrUnsupported`
`oserror.ErrNotExist`), and `Error()` returns `msg`. (Variables with the same message are distinct
pointers too in Go, as each `New` allocates; the field does not tell them apart.) -/

/-- **The global `X` holds `errors.New(msg)`** (persistent): a fixed `*errorString` whose field
`s` holds `msg` for good, and whose `Error()` returns `msg`. -/
def newVar (X msg : GoString) : IProp GF :=
  iprop(∃ x : Loc,
    globalAddr X ↦□ interface.mkOk (go.GoType.PointerType errorString.ty) #x ∗
    x.[errors.errorString, go!"s"] ↦□ msg ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType errorString.ty) go!"Error" #x)) (Val #()))
        {{ Φ }})

instance newVar_persistent (X msg : GoString) : Persistent (newVar (GF := GF) X msg) := by
  unfold newVar; infer_instance

/-- Two `errorString`s whose fields hold different messages are different pointers. -/
theorem errorString_ne (x y : Loc) (m1 m2 : GoString) (h : m1 ≠ m2) :
    (x.[errors.errorString, go!"s"] ↦□ m1 : IProp GF) ⊢
      y.[errors.errorString, go!"s"] ↦□ m2 -∗ ⌜x ≠ y⌝ := by
  iintro #H1 #H2
  by_cases hxy : x = y
  · subst hxy
    icombine H1 H2 gives %he
    exact absurd he h
  · ipureintro; exact hxy

/-- **Two `errors.New` variables with different messages hold different errors**: the values
of `X` and `Y` (loaded through any persistent points-to of the globals) differ. -/
theorem newVar_ne (X Y m1 m2 : GoString) (h : m1 ≠ m2) (v1 v2 : GoInterface) :
    newVar (GF := GF) X m1 ⊢ newVar (GF := GF) Y m2 -∗ globalAddr X ↦□ v1 -∗
      globalAddr Y ↦□ v2 -∗ ⌜v1 ≠ v2⌝ := by
  iintro #HX #HY #Hv1 #Hv2
  iunfold newVar at HX HY
  icases HX with ⟨%x, #HXg, #HXs, -⟩
  icases HY with ⟨%y, #HYg, #HYs, -⟩
  icombine Hv1 HXg gives %h1
  icombine Hv2 HYg gives %h2
  ihave %hxy := errorString_ne x y m1 m2 h $$ HXs HYs
  ipureintro
  subst h1 h2
  intro he
  apply hxy
  unfold interface.mkOk at he
  injection he with he
  injection he with _ he
  exact go.intoVal_inj he

/-- The package-initialized state (persistent): `ErrUnsupported` holds its `errors.New` error
(`errorType`, a runtime type descriptor, has no cell: `TrustedCode/errors.lean`). -/
abbrev isInit : IProp GF :=
  iprop("#HErrUnsupported" ∷ newVar ErrUnsupported go!"unsupported operation")

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.errors :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.errors :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.errors

/-- `errors.ErrUnsupported` holds `errors.New("unsupported operation")`. -/
theorem errUnsupported_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢
      newVar (GF := GF) ErrUnsupported go!"unsupported operation" :=
  isInit_access

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

omit [GooseSemantics] [GooseInterp] in
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

omit [GooseSemantics] [GooseInterp] go_gctx hG sem package_sem in
theorem asTypeHide_intro {P Q : IProp GF} : (□ asTypeHide P -∗ Q) ⊢ (□ P -∗ Q) := .rfl

omit [GooseSemantics] [GooseInterp] go_gctx hG sem package_sem in
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
def IsPointerError [GooseExts] [GoGlobalContext] (ii : GoInterfaceOk) : Prop :=
  ∃ (T : go.GoType) (l : Loc), ii.ty = go.PointerType T ∧ ii.v = #l

/-- The specs `Is(err, target)` needs of one error `ii` of the tree `S`, as relations: `I ii b`,
that `ii.Is(target)` may return `b`; `U ii cs`, that `ii`'s `Unwrap` may return `cs` (`[e]` for
`Unwrap() error`, the slice's errors for `Unwrap() []error`):
* `Is(error) bool` (if `ii` has it) is called with `target` and returns a `b` with `I ii b`;
  without it, `I ii false`;
* `Unwrap() error` returns an error `e` in `S` with `U ii [e]`;
* `Unwrap() []error` returns a slice of errors `es` in `S` with `U ii es`;
* without either, `U ii []`.

Exact relations (functions: `I ii b ↔ b = f ii`, `U ii cs ↔ cs = ch ii`) make `Is` a function
of the tree (`isWalk_det`), as Go's is for errors whose methods are deterministic;
`errorIsNode` is the over-approximation, `I ii b := b = true → M ii` and `U ii cs := cs ⊆ S`. -/
def errorWalkNode (S : GoError → Prop) (I : GoInterfaceOk → Bool → Prop)
    (U : GoInterfaceOk → List GoError → Prop) (target : GoError) (ii : GoInterfaceOk) :
    IProp GF :=
  iprop(
    "#HIs" ∷ (if methodSet ii.ty !! go!"Is" = some (go.Signature [go.error] false [go.bool]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Is" ii.v)) (Val #target))
      {{ (b : Bool), RET #b; ⌜I ii b⌝ }})
      else iprop(⌜I ii false⌝)) ∗
    "#HUnwrap" ∷ (if methodSet ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #()))
      {{ (e : GoError), RET #e; ⌜S e ∧ U ii [e]⌝ }})
      else if methodSet ii.ty !! go!"Unwrap" =
          some (go.Signature [] false [go.GoType.SliceType go.error]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #()))
      {{ (s : GoSlice) (dq : DFrac) (es : List GoError), RET #s;
          s ↦*{dq} es ∗ ⌜(∀ e ∈ es, S e) ∧ U ii es⌝ }})
      else iprop(⌜U ii []⌝)))

/-- Every non-nil error of `S` satisfies `errorWalkNode`. -/
abbrev errorWalkTree (S : GoError → Prop) (I : GoInterfaceOk → Bool → Prop)
    (U : GoInterfaceOk → List GoError → Prop) (target : GoError) : IProp GF :=
  iprop(□ ∀ ii : GoInterfaceOk, ⌜S (interface.ok ii)⌝ -∗ errorWalkNode (GF := GF) S I U target ii)

/-- The over-approximating `Is` relation: a `true` only if `M ii`. -/
abbrev isRelOf (M : GoInterfaceOk → Prop) : GoInterfaceOk → Bool → Prop :=
  fun ii b => b = true → M ii

/-- The over-approximating `Unwrap` relation: errors of `S`. -/
abbrev unwrapRelOf (S : GoError → Prop) : GoInterfaceOk → List GoError → Prop :=
  fun _ cs => ∀ e ∈ cs, S e

/-- The specs `Is(err, target)` needs of one error `ii` of the tree `S`, over-approximated:
* `Is(error) bool` (if `ii` has it) is called with `target` and returns a `bool`, `true` only if
  `M ii`;
* `Unwrap() error` returns an error in `S`;
* `Unwrap() []error` returns a slice of errors in `S`. -/
abbrev errorIsNode (S : GoError → Prop) (M : GoInterfaceOk → Prop) (target : GoError)
    (ii : GoInterfaceOk) : IProp GF :=
  errorWalkNode (GF := GF) S (isRelOf M) (unwrapRelOf S) target ii

/-- Every non-nil error of `S` satisfies `errorIsNode`. -/
abbrev errorIsTree (S : GoError → Prop) (M : GoInterfaceOk → Prop) (target : GoError) :
    IProp GF :=
  errorWalkTree (GF := GF) S (isRelOf M) (unwrapRelOf S) target

/-- A leaf error without an `Is(error) bool` method is a one-error tree, for any `M`. -/
theorem errorIsTree_leaf (ii : GoInterfaceOk) (M : GoInterfaceOk → Prop) (target : GoError)
    (hleaf : isLeafError ii)
    (hIs : methodSet ii.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])) :
    ⊢ errorIsTree (GF := GF) (· = interface.ok ii) M target := by
  obtain ⟨-, hU1, hU2⟩ := hleaf
  iintro !> %ii' %h
  cases h
  unfold errorWalkNode
  simp only [hIs, hU1, hU2, ↓reduceIte]
  isplitr
  · ipureintro; intro h; cases h
  · ipureintro; intro _ h; cases h

/-- A tree is an over-approximating one, an `Is` method's `true` meaning `I ii true`. -/
theorem errorIsTree_of_walk (S : GoError → Prop) (I : GoInterfaceOk → Bool → Prop)
    (U : GoInterfaceOk → List GoError → Prop) (target : GoError) :
    errorWalkTree (GF := GF) S I U target ⊢ errorIsTree (GF := GF) S (fun ii => I ii true) target := by
  iintro #Ht !> %ii %hS
  ihave Hn := Ht $$ %ii %hS
  unfold errorWalkNode
  iNamed Hn
  isplitl
  · by_cases h : methodSet ii.ty !! go!"Is" = some (go.Signature [go.error] false [go.bool])
    · simp only [h, ↓reduceIte]
      iintro !> %Φ - HΦ
      wp_apply HIs as %b %Hb
      iapply HΦ
      ipureintro
      intro hb; subst hb; exact Hb
    · simp only [h, ↓reduceIte]
      ipureintro; intro h; cases h
  · by_cases h1 : methodSet ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error])
    · simp only [h1, ↓reduceIte]
      iintro !> %Φ - HΦ
      wp_apply HUnwrap as %e ⟨%He, -⟩
      iapply HΦ
      ipureintro
      exact ⟨He, fun c hc => by rw [List.mem_singleton.mp hc]; exact He⟩
    · by_cases h2 : methodSet ii.ty !! go!"Unwrap" =
          some (go.Signature [] false [go.GoType.SliceType go.error])
      · simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
        iintro !> %Φ - HΦ
        wp_apply HUnwrap as %s %dq %es ⟨Hs, %Hes, -⟩
        iapply HΦ
        iframe
        ipureintro
        exact ⟨Hes, Hes⟩
      · simp only [h1, h2, ↓reduceIte]
        ipureintro; intro _ h; cases h

/-- A leaf error without an `Is(error) bool` method is a one-error tree with exact relations: its
`Is` answers `false`, its `Unwrap` nothing. -/
theorem errorWalkTree_leaf (ii : GoInterfaceOk) (target : GoError) (hleaf : isLeafError ii)
    (hIs : methodSet ii.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])) :
    ⊢ errorWalkTree (GF := GF) (· = interface.ok ii) (fun _ b => b = false) (fun _ cs => cs = [])
      target := by
  obtain ⟨-, hU1, hU2⟩ := hleaf
  iintro !> %ii' %h
  cases h
  unfold errorWalkNode
  simp only [hIs, hU1, hU2, ↓reduceIte]
  isplitr <;> ipureintro <;> trivial

/-- The errors of the tree `S` whose dynamic type is that of `target` hold a pointer, as
`target` does for a pointer error: Go's typing, which the model (with no typing of interface
values) does not have. What Go's `err == target` needs to compare two such errors. -/
def TreeTyped [GooseExts] [GoGlobalContext] (S : GoError → Prop) (target : GoError) : Prop :=
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

/-! ### The answers of the walk -/

/-- The answers of Go's tree walk `is` on a list of errors, each walked in turn until one answers
`true` (`IsWalk` for one error), over the methods' relations `I` and `U` (`errorWalkNode`): an
error that is `target` (when `c`, `target`'s type comparable), or whose `Is` answers `true`, is a
`true`; otherwise its children (`U`) are walked; `nil` is a `false` (`target` not `nil` when `c`).
An inductive: the walk of a cyclic tree has no answer, as Go's does not return. -/
inductive IsWalkL (c : Bool) (I : GoInterfaceOk → Bool → Prop)
    (U : GoInterfaceOk → List GoError → Prop) (target : GoError) : List GoError → Bool → Prop
  | done : IsWalkL c I U target [] false
  | nilSkip {es b} : (c = true → target ≠ interface.nil) → IsWalkL c I U target es b →
      IsWalkL c I U target (interface.nil :: es) b
  | eq {ii es} : c = true → interface.ok ii = target →
      IsWalkL c I U target (interface.ok ii :: es) true
  | is {ii es} : (c = true → interface.ok ii ≠ target) → I ii true →
      IsWalkL c I U target (interface.ok ii :: es) true
  | hit {ii cs es} : (c = true → interface.ok ii ≠ target) → I ii false → U ii cs →
      IsWalkL c I U target cs true → IsWalkL c I U target (interface.ok ii :: es) true
  | miss {ii cs es b} : (c = true → interface.ok ii ≠ target) → I ii false → U ii cs →
      IsWalkL c I U target cs false → IsWalkL c I U target es b →
      IsWalkL c I U target (interface.ok ii :: es) b

/-- `b` is an answer of Go's walk `is(err, target, c)` (`IsWalkL` of `[err]`). -/
abbrev IsWalk (c : Bool) (I : GoInterfaceOk → Bool → Prop)
    (U : GoInterfaceOk → List GoError → Prop) (target : GoError) (err : GoError) (b : Bool) :
    Prop :=
  IsWalkL c I U target [err] b

section walk
variable {c : Bool} {I : GoInterfaceOk → Bool → Prop} {U : GoInterfaceOk → List GoError → Prop}
  {target : GoError}

/-- A list whose first error answers `false` answers what the rest does. -/
theorem IsWalkL.cons_false {e : GoError} {es : List GoError} {b : Bool}
    (h : IsWalk c I U target e false) (hes : IsWalkL c I U target es b) :
    IsWalkL c I U target (e :: es) b := by
  cases h with
  | nilSkip hn h' => cases h'; exact .nilSkip hn hes
  | miss hne hI hU hcs h' => cases h'; exact .miss hne hI hU hcs hes

/-- A list whose first error answers `true` answers `true`. -/
theorem IsWalkL.cons_true {e : GoError} {es : List GoError}
    (h : IsWalk c I U target e true) : IsWalkL c I U target (e :: es) true := by
  cases h with
  | nilSkip _ h' => cases h'
  | eq hc heq => exact .eq hc heq
  | is hne hI => exact .is hne hI
  | hit hne hI hU hcs => exact .hit hne hI hU hcs
  | miss _ _ _ _ h' => cases h'

/-- An error not `target`, whose `Is` answers `false`, answers what its children do. -/
theorem IsWalk.children {ii : GoInterfaceOk} {cs : List GoError} {b : Bool}
    (hne : c = true → interface.ok ii ≠ target) (hI : I ii false) (hU : U ii cs)
    (h : IsWalkL c I U target cs b) : IsWalk c I U target (interface.ok ii) b := by
  cases b
  · exact .miss hne hI hU h .done
  · exact .hit hne hI hU h

/-- **The walk is a function of the tree** when the methods' relations are. -/
theorem isWalkL_det (hI : ∀ ii b b', I ii b → I ii b' → b = b')
    (hU : ∀ ii cs cs', U ii cs → U ii cs' → cs = cs') {es : List GoError} {b b' : Bool}
    (h : IsWalkL c I U target es b) (h' : IsWalkL c I U target es b') : b = b' := by
  induction h generalizing b' with
  | done => cases h'; rfl
  | nilSkip _ _ ih => cases h' with
    | nilSkip _ h' => exact ih h'
  | eq hc heq => cases h' with
    | eq => rfl
    | is => rfl
    | hit => rfl
    | miss hne => exact absurd heq (hne hc)
  | is hne hI1 => cases h' with
    | eq => rfl
    | is => rfl
    | hit => rfl
    | miss _ hI2 => exact absurd (hI _ _ _ hI1 hI2) (by decide)
  | hit hne hI1 hU1 _ ih => cases h' with
    | eq => rfl
    | is => rfl
    | hit => rfl
    | miss _ _ hU2 hcs2 =>
      exact absurd (ih (hU _ _ _ hU1 hU2 ▸ hcs2)) (by decide)
  | miss hne hI1 hU1 _ _ ihc ih => cases h' with
    | eq hc heq => exact absurd heq (hne hc)
    | is _ hI2 => exact absurd (hI _ _ _ hI1 hI2).symm (by decide)
    | hit _ _ hU2 hcs2 => exact absurd (ihc (hU _ _ _ hU1 hU2 ▸ hcs2)) (by decide)
    | miss _ _ _ _ hes2 => exact ih hes2

/-- `errors.Is` is a function of the tree: two walks of one error with functional relations give
the same answer. -/
theorem isWalk_det (hI : ∀ ii b b', I ii b → I ii b' → b = b')
    (hU : ∀ ii cs cs', U ii cs → U ii cs' → cs = cs') {err : GoError} {b b' : Bool}
    (h : IsWalk c I U target err b) (h' : IsWalk c I U target err b') : b = b' :=
  isWalkL_det hI hU h h'

/-- Under the over-approximating relations, a `true` comes from an error of the tree that is
`target` or whose `Is` said so. -/
theorem isWalkL_true_mem {S : GoError → Prop} {M : GoInterfaceOk → Prop} {es : List GoError}
    (h : IsWalkL c (isRelOf M) (unwrapRelOf S) target es true) (hS : ∀ e ∈ es, S e) :
    ∃ ii, S (interface.ok ii) ∧ (interface.ok ii = target ∨ M ii) := by
  generalize hb : true = b at h
  induction h with
  | done => cases hb
  | nilSkip _ _ ih => exact ih (fun e he => hS e (List.mem_cons_of_mem _ he)) hb
  | eq _ heq => exact ⟨_, hS _ List.mem_cons_self, Or.inl heq⟩
  | is _ hI => exact ⟨_, hS _ List.mem_cons_self, Or.inr (hI rfl)⟩
  | hit _ _ hU _ ih => exact ih hU rfl
  | miss _ _ _ _ _ _ ih => exact ih (fun e he => hS e (List.mem_cons_of_mem _ he)) hb

/-- When `c`, an error that is `target` answers `true`. -/
theorem isWalk_eq_true {ii : GoInterfaceOk} {b : Bool} (hc : c = true)
    (heq : interface.ok ii = target) (h : IsWalk c I U target (interface.ok ii) b) : b = true := by
  cases h with
  | eq => rfl
  | is => rfl
  | hit => rfl
  | miss hne => exact absurd heq (hne hc)

end walk

end wps

end errors

end Perennial
