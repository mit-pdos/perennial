/-
Port of `new/proof/errors.v`: specs for the Go `errors` package.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.errors
import Perennial.GeneratedProof.errors

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace errors

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.errors :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.errors :=
  build_get_is_pkg_init_wf

/-- Proven first because it is used during package initialization (to create
global error variables). -/
theorem wp_New (msg : go_string) :
    {{ (True : IProp GF) }}
      (App (Val (@! New)) (Val #msg))
    {{ (err : interface.t_ok), RET #(interface.ok err); True }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  wp_auto
  wp_end

theorem wp_errorType_init :
    {{ (True : IProp GF) }}
      (App (Val errorType'init) (Val #()))
    {{ RET #(); True }} := by
  -- Unprovable: `errorType'init` is opaque (an axiom in Perennial/Code/errors.lean, as in
  -- Rocq): `var errorType = reflectlite.TypeOf((*error)(nil)).Elem()` is not translated
  -- (`errors.toml` excludes it and the `internal/reflectlite` import), so goose emits only
  -- an axiomatized `errorType'init : val`, which has no semantics.
  sorry -- Rocq: Admitted

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.errors get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.errors }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := interface.t) ErrUnsupported go.error as _
  wp_apply wp_New as %_ _
  wp_apply wp_errorType_init
  iframe Hown
  is_pkg_init_finish

def is_unwrappable (err : error.t) : IProp GF :=
  match err with
  | interface.nil => iprop(True)
  | interface.ok ii =>
    if method_set ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #()))
      {{ (err : interface.t_ok), RET #(interface.ok err); True }})
    else iprop(True)

instance is_unwrappable_persistent (err : error.t) : Persistent (is_unwrappable (GF := GF) err) := by
  unfold is_unwrappable
  split
  · infer_instance
  · split <;> infer_instance

theorem wp_Unwrap (err : error.t) :
    {{ is_unwrappable (GF := GF) err }}
      (App (Val (@! Unwrap)) (Val #err))
    {{ (err' : error.t), RET #err'; True }} := by
  wp_start as #Hunwrap
  wp_auto
  cases err with
  | nil =>
    dsimp only
    wp_auto
    wp_end
  | ok ii =>
    dsimp only
    cases Hhas_unwrap : go.type_set_contains ii.ty
      (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
    · simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_end
    · simp only [↓reduceIte]
      wp_auto
      have hu : underlying (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])]) =
          go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])] :=
        go.is_underlying
      simp only [go.type_set_contains, hu, go.type_set_elems_contains, go.type_set_elem_contains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at Hhas_unwrap
      simp only [is_unwrappable, Hhas_unwrap, ↓reduceIte]
      wp_apply Hunwrap as %_ _
      wp_end

/-! ### `AsType`

Lean deviation from Rocq (where `wp_AsType` has precondition `True` and is
`Admitted`): `AsType[E](err)` walks the error tree of `err`, calling the
`Unwrap() error`, `Unwrap() []error` and `As(any) bool` methods of every error
in the tree, so its precondition must specify these methods. We do so with a
pure set `S` of errors that contains `err` and is closed under the `Unwrap`
methods (`is_error_tree`); for each error in `S` the precondition gives the
specs of its methods (persistently) and a typing fact for the type assertion
`err.(E)` (`asType_typed`). The postcondition is unchanged.

The proof relies on goose translating a bare `return` with blank named results
(`func asType[E error](...) (_ E, _ bool)`) to the zero values; goose used to
emit `![E] "_"`, a free variable (the `_` results are bound anonymously), which
made those return paths stuck. -/

/-- The value extracted by a successful type assertion `ii.(T)` has Lean type
`T'` (for an interface type `T` the assertion returns the interface value
itself, otherwise the dynamic value). This is guaranteed by Go's typing; it is
not derivable in the model, which has no typing of interface values. -/
def asType_typed [GoSemanticsFunctions] (T' : Type) (T : go.type) (ii : interface.t_ok) : Prop :=
  if go.is_interface_type (underlying T) then
    go.type_set_contains ii.ty T = true → ∃ x : T', (#x : val) = #(interface.ok ii)
  else ii.ty = T → ∃ x : T', (#x : val) = ii.v

/-- The specs `AsType[T]` needs of one error `ii` of the tree `S`:
* `As(any) bool` (if `ii` has it) is called with a pointer `l` to a `T'`, may
  write the target, and returns a `bool`;
* `Unwrap() error` returns an error in `S`;
* `Unwrap() []error` returns a slice of errors in `S`. -/
def asType_node (S : error.t → Prop) (T' : Type) [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.type) (ii : interface.t_ok) : IProp GF :=
  iprop(
    "%Htyped" ∷ ⌜asType_typed T' T ii⌝ ∗
    "#HAs" ∷ (if method_set ii.ty !! go!"As" = some (go.Signature [go.any] false [go.bool]) then
      iprop(∀ (l : loc) (v : T'),
        {{ l ↦ v }}
          (App (Val #(methods ii.ty go!"As" ii.v)) (Val #(interface.mk_ok (go.PointerType T) #l)))
        {{ (b : Bool) (v' : T'), RET #b; l ↦ v' }})
      else iprop(True)) ∗
    "#HUnwrap" ∷ (if method_set ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #()))
      {{ (e : error.t), RET #e; ⌜S e⌝ }})
      else if method_set ii.ty !! go!"Unwrap" =
          some (go.Signature [] false [go.type.SliceType go.error]) then
      iprop({{ True }}
        (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #()))
      {{ (s : slice.t) (dq : DFrac) (es : List error.t), RET #s;
          s ↦*{dq} es ∗ ⌜∀ e ∈ es, S e⌝ }})
      else iprop(True)))

omit ffi [ffi_interp ffi] [ffi_semantics ext ffi] in
theorem asType_typed_val [GoSemanticsFunctions] {T' : Type} [ZeroVal T'] {T : go.type}
    {ii : interface.t_ok} (h : asType_typed T' T ii) :
    ∃ x : T', (if go.is_interface_type (underlying T) = true then
        (if go.type_set_contains ii.ty T = true then #(interface.ok ii) else #(zero_val T'))
      else if ii.ty = T then ii.v else #(zero_val T') : val) = #x := by
  unfold asType_typed at h
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

/-- Every non-nil error of `S` satisfies `asType_node`. -/
abbrev is_error_tree (S : error.t → Prop) (T' : Type) [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.type) : IProp GF :=
  iprop(□ ∀ ii : interface.t_ok, ⌜S (interface.ok ii)⌝ -∗ asType_node (GF := GF) S T' T ii)

instance is_error_tree_persistent (S : error.t → Prop) (T' : Type) [ZeroVal T']
    [TypedPointsto (GF := GF) T'] (T : go.type) :
    Persistent (is_error_tree (GF := GF) S T' T) := by
  unfold is_error_tree; infer_instance

/-- `P` under an opaque name, to keep the Löb induction hypothesis of `wp_asType`
(which contains `▷`s) away from the later stripping that the proof mode does for
every hypothesis mentioning `▷` at every symbolic execution step. -/
def asType_hide (P : IProp GF) : IProp GF := P

omit ffi [ffi_interp ffi] [ffi_semantics ext ffi] go_gctx hG sem package_sem in
theorem asType_hide_intro {P Q : IProp GF} : (□ asType_hide P -∗ Q) ⊢ (□ P -∗ Q) := .rfl

omit ffi [ffi_interp ffi] [ffi_semantics ext ffi] go_gctx hG sem package_sem in
theorem asType_hide_elim {P Q : IProp GF} : (□ P -∗ Q) ⊢ (□ asType_hide P -∗ Q) := .rfl

/-- Spec of the recursive helper `asType(err, ppe)`. `ppe` points to the
lazily allocated `*E` target passed to `As` methods. (New in Lean.) -/
theorem wp_asType (S : error.t → Prop) (err : error.t) (ppe pe : loc)
    {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.type} [IntoValTyped (GF := GF) T' T] :
    {{ "#Htree" ∷ is_error_tree (GF := GF) S T' T ∗ "%HS" ∷ ⌜S err⌝ ∗
        "Hppe" ∷ ppe ↦ pe ∗
        "Hpe" ∷ (⌜pe = loc.null⌝ ∨ ∃ v : T', pe ↦ v) }}
      (App (App (Val #(functions asType [T])) (Val #err)) (Val #ppe))
    {{ (e : T') (found : Bool) (pe' : loc), RET (PairV #e #found);
        ppe ↦ pe' ∗ (⌜pe' = loc.null⌝ ∨ ∃ v : T', pe' ↦ v) }} := by
  iloeb as IH generalizing %err %pe
  irevert IH
  iapply asType_hide_intro
  iintro #IH
  wp_start as H
  iNamed H
  wp_alloc r1 as Hr1
  wp_auto
  wp_alloc r2 as Hr2
  wp_auto
  iclear Hr1 Hr2
  ihave HI : (∃ (e : error.t) (pe' : loc),
      "err" ∷ err_ptr ↦ e ∗ "%HSe" ∷ ⌜S e⌝ ∗ "Hppe" ∷ ppe ↦ pe' ∗
      "Hpe" ∷ (⌜pe' = loc.null⌝ ∨ ∃ v : T', pe' ↦ v) :
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
    obtain ⟨x, hx⟩ := asType_typed_val Htyped
    rw [hx]
    generalize (if go.is_interface_type (underlying T) = true then go.type_set_contains ii.ty T
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
        (⌜v = execute_val⌝ ∗ ∃ q : loc, "ppe" ∷ ppe_ptr ↦ ppe ∗ "err" ∷ err_ptr ↦ interface.ok ii ∗
          "Hppe" ∷ ppe ↦ q ∗ "Hpe" ∷ (⌜q = loc.null⌝ ∨ ∃ v : T', q ↦ v)) ∨
        (∃ (e : T') (q : loc), ⌜v = return_val (PairV #e #true)⌝ ∗ ppe ↦ q ∗
          (⌜q = loc.null⌝ ∨ ∃ v : T', q ↦ v)))) at next with [ppe err Hppe Hpe]
    wp_auto
    have hu : underlying (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])]) =
        go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])] :=
      go.is_underlying
    cases hAs : go.type_set_contains ii.ty
      (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])])
    case' true =>
      simp only [go.type_set_contains, hu, go.type_set_elems_contains, go.type_set_elem_contains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hAs
      simp only [hAs, ↓reduceIte]
      wp_auto
      by_cases hnull : pe' = loc.null
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
        ihave Hpe : (⌜«$r0_ptr» = loc.null⌝ ∨ ∃ v : T', «$r0_ptr» ↦ v : IProp GF) $$ [Hv]
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
        ihave Hpe : (⌜pe' = loc.null⌝ ∨ ∃ v : T', pe' ↦ v : IProp GF) $$ [Hv]
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
        [go.MethodElem go!"Unwrap" (go.Signature [] false [go.type.SliceType go.error])]) =
        go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.type.SliceType go.error])] :=
      go.is_underlying
    cases hU : go.type_set_contains ii.ty
      (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
    case true =>
      simp only [go.type_set_contains, hu1, go.type_set_elems_contains, go.type_set_elem_contains,
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
      simp only [go.type_set_contains, hu1, go.type_set_elems_contains, go.type_set_elem_contains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_false_iff_not] at hU
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      cases hU2 : go.type_set_contains ii.ty
        (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.type.SliceType go.error])])
      case true =>
        simp only [go.type_set_contains, hu2, go.type_set_elems_contains, go.type_set_elem_contains,
          List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hU2
        simp only [hU, ↓reduceIte]
        simp only [hU2, ↓reduceIte]
        wp_auto
        wp_apply HUnwrap as %s %dq %es ⟨Hs, %Hes⟩
        ihave %Hlen := own_slice_len _ _ _ $$ Hs
        ihave HI2 : (∃ (j : w64) (q : loc) (e2 : error.t),
            "i" ∷ i_ptr ↦ j ∗ "Hs" ∷ s ↦*{dq} es ∗ "err" ∷ err_ptr ↦ e2 ∗
            "Hppe" ∷ ppe ↦ q ∗ "Hpe" ∷ (⌜q = loc.null⌝ ∨ ∃ v : T', q ↦ v) ∗
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
            iapply asType_hide_elim
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

/-- Lean deviation from Rocq: new parameter `S` and precondition
`is_error_tree S T' T ∗ ⌜S err⌝` (Rocq: `True`); see the section comment. -/
theorem wp_AsType (S : error.t → Prop) (err : error.t) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.type} [IntoValTyped (GF := GF) T' T] :
    {{ "#Htree" ∷ is_error_tree (GF := GF) S T' T ∗ "%HS" ∷ ⌜S err⌝ }}
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
    wp_apply wp_asType S (interface.ok ii) pe_ptr (zero_val loc) $$ [pe] as %e %found %pe' _
    · iframe; iframe #; iframe %; ileft; ipureintro; rfl
    wp_end

end wps

end errors

end Perennial
end
