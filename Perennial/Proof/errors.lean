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
  -- Unprovable: `errorType'init` is opaque (an axiom in Perennial/Code/errors.lean).
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

theorem wp_AsType (err : error.t) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.type} [IntoValTyped (GF := GF) T' T] :
    {{ (True : IProp GF) }}
      (App (Val #(functions AsType [T])) (Val #err))
    {{ (e : T') (found : Bool), RET (PairV #e #found); True }} := by
  -- Unprovable: `asType` calls the arbitrary `Unwrap`/`As` methods of `err`, about which the precondition says nothing.
  sorry -- Rocq: Admitted

end wps

end errors

end Perennial
end
