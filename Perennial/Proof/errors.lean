/-
Specs for the Go `errors` package.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.errors
import Perennial.GeneratedProof.errors

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

/-- Proven first because it is used during package initialization (to create
global error variables). -/
theorem wp_New (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! New)) (Val #msg))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); True }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  wp_auto
  wp_end

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

end wps

end errors

end Perennial
end
