/-
Specs for the Go `errors` package.
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

/-- `errors.New(msg)` returns an error (an `*errorString`) whose `Error()` returns `msg`.
Proven first because it is used during package initialization (to create
global error variables). -/
theorem wp_New (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! New)) (Val #msg))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }} }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  ipersist s
  wp_auto
  iapply HΦ
  imodintro
  iintro %Φ HΦ
  dsimp only
  rw [method_unfold]
  wp_auto
  iexact HΦ

theorem wp_errorType_init :
    {{ (True : IProp GF) }}
      (App (Val errorType.init) (Val #()))
    {{ RET #(); True }} := by
  -- Unprovable: `errorType'init` is opaque (an axiom in Perennial/Code/errors.lean):
  -- `var errorType = reflectlite.TypeOf((*error)(nil)).Elem()` is not translated
  -- (`errors.toml` excludes it and the `internal/reflectlite` import), so goose emits only
  -- an axiomatized `errorType'init : val`, which has no semantics.
  sorry

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.errors get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.errors }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnsupported go.error as _
  wp_apply wp_New as %_ _
  wp_apply wp_errorType_init
  iframe Hown
  is_pkg_init_finish

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

theorem wp_Unwrap (err : GoError) :
    {{ isUnwrappable (GF := GF) err }}
      (App (Val (@! Unwrap)) (Val #err))
    {{ (err' : GoError), RET #err'; True }} := by
  wp_start as #Hunwrap
  wp_auto
  cases err with
  | nil =>
    dsimp only
    wp_auto
    wp_end
  | ok ii =>
    dsimp only
    cases Hhas_unwrap : go.typeSetContains ii.ty
      (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
    · simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_end
    · simp only [↓reduceIte]
      wp_auto
      have hu : underlying (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])]) =
          go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])] :=
        go.is_underlying
      simp only [go.typeSetContains, hu, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at Hhas_unwrap
      simp only [isUnwrappable, Hhas_unwrap, ↓reduceIte]
      wp_apply Hunwrap as %_ _
      wp_end

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

/-- Spec of the recursive helper `asType(err, ppe)`. `ppe` points to the
lazily allocated `*E` target passed to `As` methods. (New in Lean.) -/
theorem wp_asType (S : GoError → Prop) (err : GoError) (ppe pe : Loc)
    {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.GoType} [IntoValTyped (GF := GF) T' T] :
    {{ "#Htree" ∷ isErrorTree (GF := GF) S T' T ∗ "%HS" ∷ ⌜S err⌝ ∗
        "Hppe" ∷ ppe ↦ pe ∗
        "Hpe" ∷ (⌜pe = Loc.null⌝ ∨ ∃ v : T', pe ↦ v) }}
      (App (App (Val #(functions asType [T])) (Val #err)) (Val #ppe))
    {{ (e : T') (found : Bool) (pe' : Loc), RET (PairV #e #found);
        ppe ↦ pe' ∗ (⌜pe' = Loc.null⌝ ∨ ∃ v : T', pe' ↦ v) }} := by
  iloeb as IH generalizing %err %pe
  irevert IH
  iapply asTypeHide_intro
  iintro #IH
  wp_start as H
  iNamed H
  wp_alloc r1 as Hr1
  wp_auto
  wp_alloc r2 as Hr2
  wp_auto
  iclear Hr1 Hr2
  ihave HI : (∃ (e : GoError) (pe' : Loc),
      "err" ∷ err_ptr ↦ e ∗ "%HSe" ∷ ⌜S e⌝ ∗ "Hppe" ∷ ppe ↦ pe' ∗
      "Hpe" ∷ (⌜pe' = Loc.null⌝ ∨ ∃ v : T', pe' ↦ v) :
      IProp GF) $$ [err Hppe Hpe]
  · iexists err, pe
    iframe
    ipureintro; exact HS
  wp_for HI
  haveI : T ↓u underlying T := ⟨rfl⟩
  wp_auto
  cases e with
  | nil =>
    dsimp only
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
  | ok ii =>
    ihave Hnode := Htree $$ %ii %HSe
    iNamed Hnode
    dsimp only
    obtain ⟨x, hx⟩ := asTypeTyped_val Htyped
    rw [hx]
    -- (the value bound by the type assertion is `#x` only after `hx`)
    wp_pures
    wp_alloc ok_ptr as ok
    wp_pures
    wp_alloc e_ptr as e
    wp_pures
    generalize (if go.isInterfaceType (underlying T) = true then go.typeSetContains ii.ty T
      else decide (ii.ty = T)) = b
    cases b
    case true =>
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
    wp_store; wp_pures; wp_store; wp_pures; wp_load; wp_pures
    -- the `As` statement, joined before the `Unwrap` switch: it either returns
    -- or falls through with an updated `*ppe`
    wp_join (Q := fun v => iprop(
        (⌜v = executeVal⌝ ∗ ∃ q : Loc, "ppe" ∷ ppe_ptr ↦ ppe ∗ "err" ∷ err_ptr ↦ interface.ok ii ∗
          "Hppe" ∷ ppe ↦ q ∗ "Hpe" ∷ (⌜q = Loc.null⌝ ∨ ∃ v : T', q ↦ v)) ∨
        (∃ (e : T') (q : Loc), ⌜v = returnVal (PairV #e #true)⌝ ∗ ppe ↦ q ∗
          (⌜q = Loc.null⌝ ∨ ∃ v : T', q ↦ v)))) at next with [ppe err Hppe Hpe]
    wp_auto
    have hu : underlying (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])]) =
        go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])] :=
      go.is_underlying
    cases hAs : go.typeSetContains ii.ty
      (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])])
    case' true =>
      simp only [go.typeSetContains, hu, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hAs
      simp only [hAs, ↓reduceIte]
      wp_auto
      by_cases hnull : pe' = Loc.null
      case' pos =>
        subst hnull
        wp_auto
        iclear Hpe
        wp_apply HAs $$ [$«$r0»] as %b %v' Hv
        cases b
        case true =>
          wp_auto
          iright; iexists _, _; iframe; ipureintro; rfl
        wp_auto
        ihave Hpe : (⌜«$r0_ptr» = Loc.null⌝ ∨ ∃ v : T', «$r0_ptr» ↦ v : IProp GF) $$ [Hv]
        · iright; iexists _; iexact Hv
        ileft; iframe; ipureintro; rfl
      case' neg =>
        icases Hpe with (%h | ⟨%v, Hv⟩)
        · exact absurd h hnull
        simp only [hnull, decide_false]
        wp_auto
        wp_apply HAs $$ [$Hv] as %b %v' Hv
        cases b
        case true =>
          wp_auto
          iright; iexists _, _; iframe; ipureintro; rfl
        wp_auto
        ihave Hpe : (⌜pe' = Loc.null⌝ ∨ ∃ v : T', pe' ↦ v : IProp GF) $$ [Hv]
        · iright; iexists _; iexact Hv
        ileft; iframe; ipureintro; rfl
    case' false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      ileft; iframe; ipureintro; rfl
    iintro HQ
    icases HQ with (⟨%Hv, %pe', ppe, err, Hppe, Hpe⟩ | ⟨%e0, %q, %Hv, Hppe, Hpe⟩)
    rotate_left
    · subst Hv
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
    subst Hv
    wp_auto
    have hu1 : underlying (go.InterfaceType
        [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])]) =
        go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])] :=
      go.is_underlying
    have hu2 : underlying (go.InterfaceType
        [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])]) =
        go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])] :=
      go.is_underlying
    cases hU : go.typeSetContains ii.ty
      (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
    case true =>
      simp only [go.typeSetContains, hu1, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hU
      simp only [hU, ↓reduceIte]
      wp_auto
      wp_apply HUnwrap as %e' %HSe'
      cases e' with
      | nil =>
        wp_auto
        wp_for_post
        iapply HΦ
        iframe
      | ok ii' =>
        wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        exact HSe'
    case false =>
      simp only [go.typeSetContains, hu1, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_false_iff_not] at hU
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      cases hU2 : go.typeSetContains ii.ty
        (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])])
      case true =>
        simp only [go.typeSetContains, hu2, go.typeSetElemsContains, go.typeSetElemContains,
          List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hU2
        simp only [hU, ↓reduceIte]
        simp only [hU2, ↓reduceIte]
        wp_auto
        wp_apply HUnwrap as %s %dq %es ⟨Hs, %Hes⟩
        ihave %Hlen := ownSlice_len _ _ _ $$ Hs
        ihave HI2 : (∃ (j : w64) (q : Loc) (e2 : GoError),
            "i" ∷ i_ptr ↦ j ∗ "Hs" ∷ s ↦*{dq} es ∗ "err" ∷ err_ptr ↦ e2 ∗
            "Hppe" ∷ ppe ↦ q ∗ "Hpe" ∷ (⌜q = Loc.null⌝ ∨ ∃ v : T', q ↦ v) ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i Hs err Hppe Hpe]
        · iexists W64 0, _, _
          iframe
          ipureintro; word
        wp_for HI2
        wp_if_destruct
        · simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
          list_elem es (sint.nat j) as e2'
          wp_apply wp_load_slice_index s (sint.Z j) es dq e2' Hj.1 $$ [Hs] with Hs
          · iframe; ipureintro; exact He2'_lookup
          have HSe2' : S e2' := Hes e2' (List.mem_of_getElem? He2'_lookup)
          cases e2' with
          | nil =>
            wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, _, _
            iframe
            ipureintro; word
          | ok ii2 =>
            irevert IH
            iapply asTypeHide_elim
            iintro #IH
            wp_auto
            wp_apply IH $$ %(interface.ok ii2) %q [Hppe Hpe] as %x0 %ok0 %q' ⟨Hppe, Hpe⟩
            · iframe; iframe #; ipureintro; exact HSe2'
            cases ok0
            case true =>
              wp_auto
              wp_for_post
              wp_for_post
              iapply HΦ
              iframe
            case false =>
              wp_auto
              wp_for_post
              iframe
              iexists j + W64 1, _, _
              iframe
              ipureintro; word
        · wp_for_post
          iapply HΦ
          iframe
      case false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        wp_for_post
        iapply HΦ
        iframe

/-- The parameter `S` and the precondition `isErrorTree S T' T ∗ ⌜S err⌝` specify the
methods of the errors in the tree of `err`; see the section comment. -/
theorem wp_AsType (S : GoError → Prop) (err : GoError) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} [IntoValTyped (GF := GF) T' T] :
    {{ "#Htree" ∷ isErrorTree (GF := GF) S T' T ∗ "%HS" ∷ ⌜S err⌝ }}
      (App (Val #(functions AsType [T])) (Val #err))
    {{ (e : T') (found : Bool), RET (PairV #e #found); True }} := by
  wp_start as H
  iNamed H
  wp_auto
  cases err with
  | nil =>
    wp_auto
    wp_end
  | ok ii =>
    wp_auto
    wp_apply wp_asType S (interface.ok ii) pe_ptr (zero_val Loc) $$ [pe] as %e %found %pe' _
    · iframe; iframe #; iframe %; ileft; ipureintro; rfl
    wp_end

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

/-- Spec of `errors.As(err, target)` for a target `*T`, `l` (axiom). `As` walks the error tree of
`err` as `AsType[T]` does (its precondition is `wp_AsType`'s), calling the `As` methods with
`target` itself, and stores a matching error in `*l`; it finds the target's type by reflection
(`internal/reflectlite`, not translated). Go's `As` panics if `T` is neither an interface type
nor implements `error` (`errors: *target must be interface or implement error`); the premise
`hT` excludes that case. (A caller discharges it from method-set facts about `T`, as it does
for `isLeafError`. `As` also panics on a `nil` target, which `l ↦ v` excludes.)

It is not proved from a translation of `As` as `Is` is (`wp_Is`): `As` and `as` use reflection
throughout (`reflectlite.ValueOf(target)`, `Kind`, `IsNil`, `Elem`, `Implements(errorType)`,
`TypeOf(err).AssignableTo(targetType)`, `targetVal.Elem().Set(ValueOf(err))`), with the target
type a run-time value, so a model would replace most of `as` by axioms about typed reflection
(what `AsTypeTyped` assumes for `AsType`), not a few small ones. -/
axiom wp_As [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
    [sem : go.Semantics] [package_sem : errors.Assumptions]
    (S : GoError → Prop) (err : GoError) (l : Loc) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T')
    (hT : go.isInterfaceType (underlying T) = true ∨ go.typeSetContains T go.error = true) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ isErrorTree (GF := GF) S T' T ∗ ⌜S err⌝ ∗
        l ↦ v }}
      (App (App (Val (@! As)) (Val #err)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ (b : Bool) (v' : T'), RET #b; l ↦ v' }}

/-! ### `Is`

`Is(err, target)` walks the error tree of `err` as `AsType` does, checking at each error `e`
whether `e == target` (when `target`'s dynamic type is comparable, which it finds by reflection)
and calling `e.Is(target)` if `e` has an `Is(error) bool` method. Its precondition is the
analogue of `isErrorTree`: a pure set `S` of errors containing `err`, closed under the `Unwrap`
methods, and for each error in it the specs of its methods (`errorIsNode`); a predicate `M` says
what an `Is` method's `true` means.

The tree walk `is(err, target, targetComparable)` is translated (`wp_is`). `Is` itself is a
trusted model (`TrustedCode/errors.lean`): Go's `Is` with its one reflection call,
`reflectlite.TypeOf(target).Comparable()`, replaced by a call of `reflectliteComparable`, which
has no body and whose spec is an axiom (`wp_reflectliteComparable`: `true` for a pointer
type). -/

/-- A pointer error: a non-nil error whose dynamic type is a pointer type `*T` and whose value
is a pointer, such as `errors.New`'s `*errorString` (`wp_New_ptr`). Go's `==` on two such errors
is the equality of their types and pointers, Lean's equality of the interface values. -/
def IsPointerError [FfiSyntax] [GoGlobalContext] (ii : GoInterfaceOk) : Prop :=
  ∃ (T : go.GoType) (l : Loc), ii.ty = go.PointerType T ∧ ii.v = #l

/-- `errors.New(msg)` as `wp_New`, telling also that the error is a pointer error. -/
theorem wp_New_ptr (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! New)) (Val #msg))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        ⌜IsPointerError err⌝ ∗
        □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }} }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  ipersist s
  wp_auto
  iapply HΦ
  isplitl []
  · ipureintro; exact ⟨_, x, rfl, rfl⟩
  imodintro
  iintro %Φ HΦ
  dsimp only
  rw [method_unfold]
  wp_auto
  iexact HΦ

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

/-- `is(err, target, c)` (the tree walk of `Is`): it returns `true` only if an error of the tree
is `target` or has an `Is` method that returned `true` (`M`), and, when `c` (`target`'s type is
comparable), it returns `true` if `err` is `target`. For `c`, `target` is a pointer error and
the tree's errors of its type are pointers (`TreeTyped`), so that `err == target` does not
panic. -/
theorem wp_is (S : GoError → Prop) (M : GoInterfaceOk → Prop) (err target : GoError) (c : Bool)
    (hS : S err)
    (hc : c = true → (∃ tii, target = interface.ok tii ∧ IsPointerError tii) ∧ TreeTyped S target) :
    {{ errorIsTree (GF := GF) S M target }}
      (App (App (App (Val (@! is')) (Val #err)) (Val #target)) (Val #c))
    {{ (b : Bool), RET #b;
        ⌜b = true → ∃ ii, S (interface.ok ii) ∧ (interface.ok ii = target ∨ M ii)⌝ ∗
        ⌜b = false → c = true → err ≠ interface.nil → err ≠ target⌝ }} := by
  iloeb as IH generalizing %err %hS
  irevert IH
  iapply asTypeHide_intro
  iintro #IH
  wp_start as #Htree
  wp_auto
  ihave HI : (∃ e : GoError,
      "err" ∷ err_ptr ↦ e ∗ "%HSe" ∷ ⌜S e⌝ ∗
      "%He" ∷ ⌜(c = true ∧ err ≠ interface.nil ∧ err = target) → e = err⌝ : IProp GF) $$ [err]
  · iexists err
    iframe
    ipureintro; exact ⟨hS, fun _ => rfl⟩
  wp_for HI
  -- the comparison `targetComparable && err == target`, joined
  wp_bind (If _ _ _)
  iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ⌜c = true → e ≠ target⌝ ∗
      "target" ∷ target_ptr ↦ target ∗ "err" ∷ err_ptr ↦ e ∗ "targetComparable" ∷ targetComparable_ptr ↦ c ∨
      ⌜v = returnVal #true ∧ c = true ∧ e = target⌝)) $$ [target err targetComparable]
  · cases c
    · wp_auto
      ileft
      iframe
      ipureintro; simp
    obtain ⟨⟨tii, rfl, T, l, hT, hl⟩, htyped⟩ := hc rfl
    wp_auto
    cases e with
    | nil =>
      dsimp only
      wp_auto
      ileft
      iframe
      ipureintro; exact ⟨rfl, fun _ h => by cases h⟩
    | ok ii =>
      dsimp only
      by_cases hty : ii.ty = tii.ty
      · obtain ⟨l', hl'⟩ := htyped ii tii HSe rfl hty
        simp only [hty, ↓reduceIte, hT, hl, hl']
        wp_auto
        have hii : ∀ jj : GoInterfaceOk, jj.ty = tii.ty → jj.v = tii.v → jj = tii := by
          intro jj h1 h2; cases jj; cases tii; simp_all
        wp_if_destruct
        · subst Hif
          iright
          ipureintro
          refine ⟨trivial, trivial, ?_⟩
          rw [hii ii hty (by rw [hl', hl])]
        · ileft
          iframe
          ipureintro
          intro _ h
          apply Hif
          cases h
          rw [hl] at hl'
          exact (go.intoVal_inj hl').symm
      · simp only [hty, ↓reduceIte]
        wp_auto
        ileft
        iframe
        ipureintro
        refine ⟨rfl, fun _ h => hty ?_⟩
        cases h; rfl
  iintro %v Hv
  icases Hv with (⟨%Hv, %Hne, target, err, targetComparable⟩ | %Hret)
  rotate_left
  · obtain ⟨rfl, rfl, rfl⟩ := Hret
    wp_auto
    wp_for_post
    iapply HΦ
    ipureintro
    obtain ⟨⟨tii, rfl, -⟩, -⟩ := hc rfl
    exact ⟨fun _ => ⟨tii, HSe, Or.inl rfl⟩, fun h => by cases h⟩
  subst Hv
  wp_auto
  -- the final `b = false` obligation, at every `return false`
  have Hfalse : c = true → err ≠ interface.nil → err ≠ target := by
    intro hc1 hn heq
    exact Hne hc1 ((He ⟨hc1, hn, heq⟩).trans heq)
  cases e with
  | nil =>
    dsimp only
    wp_auto
    wp_for_post
    iapply HΦ
    ipureintro
    exact ⟨fun h => absurd h (by decide), fun _ => Hfalse⟩
  | ok ii =>
    ihave Hnode := Htree $$ %ii %HSe
    iNamed Hnode
    dsimp only
    have huIs : underlying (go.InterfaceType [go.MethodElem go!"Is" (go.Signature [go.error] false [go.bool])]) =
        go.InterfaceType [go.MethodElem go!"Is" (go.Signature [go.error] false [go.bool])] :=
      go.is_underlying
    -- the `Is` method, joined before the `Unwrap` switch
    wp_join (Q := fun v => iprop(
        (⌜v = executeVal⌝ ∗ "err" ∷ err_ptr ↦ (interface.ok ii : GoError) ∗
          "target" ∷ target_ptr ↦ target ∗ "targetComparable" ∷ targetComparable_ptr ↦ c) ∨
        ⌜v = returnVal #true ∧ M ii⌝)) at next with [err target targetComparable]
    cases hIs : go.typeSetContains ii.ty
      (go.InterfaceType [go.MethodElem go!"Is" (go.Signature [go.error] false [go.bool])])
    case' true =>
      simp only [go.typeSetContains, huIs, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hIs
      simp only [hIs, ↓reduceIte]
      wp_auto
      wp_apply HIs as %b %Hb
      cases b
      case true =>
        wp_auto
        iright; ipureintro; exact ⟨rfl, Hb rfl⟩
      wp_auto
      ileft; iframe; ipureintro; rfl
    case' false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      ileft; iframe; ipureintro; rfl
    iintro HQ
    icases HQ with (⟨%Hv, err, target, targetComparable⟩ | %Hret)
    rotate_left
    · obtain ⟨rfl, hM⟩ := Hret
      wp_auto
      wp_for_post
      iapply HΦ
      ipureintro
      exact ⟨fun _ => ⟨ii, HSe, Or.inr hM⟩, fun h => absurd h (by decide)⟩
    subst Hv
    wp_auto
    have hu1 : underlying (go.InterfaceType
        [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])]) =
        go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])] :=
      go.is_underlying
    have hu2 : underlying (go.InterfaceType
        [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])]) =
        go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])] :=
      go.is_underlying
    -- a new error of the tree, to continue the loop with
    have Hnext : ∀ e' : GoError, (c = true ∧ err ≠ interface.nil ∧ err = target) → e' = err := by
      intro e' h
      exact absurd ((He h).trans h.2.2) (Hne h.1)
    cases hU : go.typeSetContains ii.ty
      (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
    case true =>
      simp only [go.typeSetContains, hu1, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hU
      simp only [hU, ↓reduceIte]
      wp_auto
      wp_apply HUnwrap as %e' %HSe'
      cases e' with
      | nil =>
        wp_auto
        wp_for_post
        iapply HΦ
        ipureintro
        exact ⟨fun h => absurd h (by decide), fun _ => Hfalse⟩
      | ok ii' =>
        wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        exact ⟨HSe', Hnext _⟩
    case false =>
      simp only [go.typeSetContains, hu1, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_false_iff_not] at hU
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      cases hU2 : go.typeSetContains ii.ty
        (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])])
      case true =>
        simp only [go.typeSetContains, hu2, go.typeSetElemsContains, go.typeSetElemContains,
          List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hU2
        simp only [hU, ↓reduceIte]
        simp only [hU2, ↓reduceIte]
        wp_auto
        wp_apply HUnwrap as %s %dq %es ⟨Hs, %Hes⟩
        ihave %Hlen := ownSlice_len _ _ _ $$ Hs
        ihave HI2 : (∃ (j : w64) (e2 : GoError),
            "i" ∷ i_ptr ↦ j ∗ "Hs" ∷ s ↦*{dq} es ∗ "err" ∷ err_ptr ↦ e2 ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i Hs err]
        · iexists W64 0, _
          iframe
          ipureintro; word
        wp_for HI2
        wp_if_destruct
        · simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
          list_elem es (sint.nat j) as e2'
          irevert IH
          iapply asTypeHide_elim
          iintro #IH
          wp_apply wp_load_slice_index s (sint.Z j) es dq e2' Hj.1 $$ [Hs] with Hs
          · iframe; ipureintro; exact He2'_lookup
          have HSe2' : S e2' := Hes e2' (List.mem_of_getElem? He2'_lookup)
          (try wp_auto)
          wp_apply IH $$ %e2' %HSe2' [] as %b0 ⟨%Hb0, -⟩
          · iframe #
          cases b0
          case true =>
            wp_auto
            wp_for_post
            wp_for_post
            iapply HΦ
            ipureintro
            exact ⟨fun _ => Hb0 rfl, fun h => absurd h (by decide)⟩
          case false =>
            wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, _
            iframe
            ipureintro; word
        · wp_for_post
          iapply HΦ
          ipureintro
          exact ⟨fun h => absurd h (by decide), fun _ => Hfalse⟩
      case false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        wp_for_post
        iapply HΦ
        ipureintro
        exact ⟨fun h => absurd h (by decide), fun _ => Hfalse⟩

/-- Spec of `reflectliteComparable(target)` (axiom), the model's name for Go's
`reflectlite.TypeOf(target).Comparable()` in `Is` (`TrustedCode/errors.lean`): it returns
whether `target`'s dynamic type is comparable, so `true` for a pointer type (Go's pointers are
comparable). It does not say more of other types. -/
axiom wp_reflectliteComparable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : HeapGS hlc GF] [sem : go.Semantics] (tii : GoInterfaceOk) :
    {{ (True : IProp GF) }}
      (App (Val (@! reflectliteComparable)) (Val #(interface.ok tii)))
    {{ (c : Bool), RET #c; ⌜(∃ T, tii.ty = go.PointerType T) → c = true⌝ }}

/-- Spec of `errors.Is(err, target)`, for a `nil` or pointer `target` (`IsPointerError`, such as
an `errors.New` error), whose type Go's `reflectlite` finds comparable
(`wp_reflectliteComparable`). Its precondition is the error tree of `err`
(`errorIsTree S M target ∗ ⌜S err⌝`), whose errors of `target`'s type hold pointers
(`TreeTyped`, Go's typing). It returns `err == target` if either is `nil`; otherwise `true` if
`err == target` (its first check), and `true` only if some error of the tree is `target` or has
an `Is` method that returned `true` (`M`).

For a `target` of another comparable type Go's `Is` compares it with the errors of the tree of
its type with `==`, which panics if they hold values that are not comparable (an interface field
holding a slice): so `target` is restricted to pointers. -/
theorem wp_Is (S : GoError → Prop) (M : GoInterfaceOk → Prop) (err target : GoError)
    (htarget : ∀ tii, target = interface.ok tii → IsPointerError tii)
    (htyped : TreeTyped S target) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ errorIsTree (GF := GF) S M target ∗ ⌜S err⌝ }}
      (App (App (Val (@! Is)) (Val #err)) (Val #target))
    {{ (b : Bool), RET #b;
        ⌜(err = interface.nil ∨ target = interface.nil) → b = decide (err = target)⌝ ∗
        ⌜∀ tii, target = interface.ok tii → IsPointerError tii → err = target → b = true⌝ ∗
        ⌜∀ tii, target = interface.ok tii → IsPointerError tii → err ≠ interface.nil →
          b = true → ∃ ii, S (interface.ok ii) ∧ (interface.ok ii = target ∨ M ii)⌝ }} := by
  wp_start as ⟨#Htree, %HS⟩
  wp_auto
  cases err with
  | nil =>
    dsimp only
    wp_auto
    cases target with
    | nil =>
      dsimp only
      wp_auto
      iapply HΦ
      ipureintro
      exact ⟨fun _ => (by simp), fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | ok tii =>
      dsimp only
      wp_auto
      iapply HΦ
      ipureintro
      exact ⟨fun _ => (by simp), fun _ _ _ h => (by cases h), fun _ _ _ h => absurd rfl h⟩
  | ok ii =>
    cases target with
    | nil =>
      dsimp only
      wp_auto
      iapply HΦ
      ipureintro
      exact ⟨fun _ => (by simp), fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | ok tii =>
      dsimp only
      wp_auto
      obtain ⟨T, l, hT, hl⟩ := htarget tii rfl
      wp_apply wp_reflectliteComparable tii as %c %Hc
      have hc : c = true := Hc ⟨T, hT⟩
      subst hc
      (try wp_auto)
      rw [show (go!"errors.is" : GoString) = is' from rfl]
      wp_apply wp_is S M (interface.ok ii) (interface.ok tii) true HS
        (fun _ => ⟨⟨tii, rfl, T, l, hT, hl⟩, htyped⟩) $$ [] as %b ⟨%Hb1, %Hb2⟩
      · iframe #
      iapply HΦ
      ipureintro
      refine ⟨fun h => (by rcases h with h | h <;> cases h), fun _ h _ heq => ?_,
        fun _ _ _ _ hb => Hb1 hb⟩
      cases b
      · exact absurd heq (Hb2 rfl rfl (by simp))
      · rfl

omit package_sem in
/-- A one-error tree of a pointer error is `TreeTyped`. -/
theorem treeTyped_pointer (ii : GoInterfaceOk) (target : GoError) (h : IsPointerError ii) :
    TreeTyped (· = interface.ok ii) target := by
  intro ii' _ hii' _ _
  cases hii'
  obtain ⟨_, l, -, hl⟩ := h
  exact ⟨l, hl⟩

/-- `errors.Is(err, target)` for a leaf `err` without an `Is` method and a `nil` or pointer
`target` (an `errors.New` error): `err == target`. If `err` has `target`'s type, it holds a
pointer (`TreeTyped`; `treeTyped_pointer` for a pointer error `err`). -/
theorem wp_Is_leaf (ii : GoInterfaceOk) (target : GoError) (hleaf : isLeafError ii)
    (hIs : methodSet ii.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]))
    (htarget : ∀ tii, target = interface.ok tii → IsPointerError tii)
    (htyped : TreeTyped (· = interface.ok ii) target) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors }}
      (App (App (Val (@! Is)) (Val #(interface.ok ii))) (Val #target))
    {{ RET #(decide (interface.ok ii = target)); True }} := by
  iintro %Φ #Hinit HΦ
  ihave #Htree := errorIsTree_leaf (GF := GF) ii (fun _ => False) target hleaf hIs
  wp_apply +noauto wp_Is (· = interface.ok ii) (fun _ => False) (interface.ok ii) target
    htarget htyped $$ [$Hinit $Htree] as %b ⟨%Hnil, %Heq, %Hsome⟩
  · ipureintro; rfl
  have hb : b = decide (interface.ok ii = target) := by
    cases target with
    | nil => exact Hnil (Or.inr rfl)
    | ok tii =>
      have hp := htarget tii rfl
      by_cases h : interface.ok ii = interface.ok tii
      · rw [decide_eq_true h]; exact Heq tii rfl hp h
      · rw [decide_eq_false h]
        cases b
        · rfl
        · obtain ⟨ii', hii', hm⟩ := Hsome tii rfl hp (by simp) rfl
          rw [hii'] at hm
          exact absurd (hm.resolve_right id) h
  rw [← hb]
  iapply HΦ
  itrivial

end wps

end errors

end Perennial
end
