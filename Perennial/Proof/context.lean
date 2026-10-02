/-
Port of `new/proof/context.v`: specifications for Go's `context` package.

All specifications are `Admitted` in Rocq (and `wp_withCancel` is `Abort`ed, so
it is omitted here).

Lean notes:
* Rocq's nested Texan triples inside `is_Context` (iProps) are written out as
  `□ ∀ Φ, P -∗ ▷ (∀ x, Q -∗ Φ v) -∗ WP e {{ Φ }}`.
* The broadcast idiom fixes `hlc := HasLC.hasLC` and uses `[allG GF]` (Rocq
  `broadcast_chanG`); the package-init instances are generic in `hlc`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.context
import Perennial.GeneratedProof.context
import Perennial.Proof.sync.atomic
import Perennial.Proof.sync
import Perennial.Proof.time
import Perennial.Proof.errors
import Perennial.Golang.Theory.Chan.Idioms.Broadcast

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace context

/-! Context logical descriptor. -/
namespace Context_desc
structure t [ffi_syntax] (PROP : Type) where
  mk ::
  Values : gmap interface.t interface.t
  Deadline : Option time.Time.t
  Done : chan.t
  Done_gn : chan_names
  PDone : PROP
end Context_desc

section init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- Rocq `is_init`. -/
abbrev is_init : IProp GF :=
  iprop("Hgoroutines" ∷
    inv nroot (∃ g, sync.atomic.own_Int32 (global_addr context.goroutines) (DFrac.own 1) g) ∗
  "_" ∷ True)

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.context :=
  define_is_pkg_init is_init
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.context :=
  build_get_is_pkg_init_wf

end init

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open Context_desc

def is_Context_def (c : interface.t_ok) (s : Context_desc.t (IProp GF)) : IProp GF :=
  iprop(
  "#HDeadline" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (True -∗ Φ (PairV #(s.Deadline.getD (zero_val time.Time.t))
                          #(match s.Deadline with | none => false | some _ => true))) -∗
      WP (App (Val #(methods c.ty go!"Deadline" c.v)) (Val #())) {{ Φ }}) ∗
  "#HDone" ∷
    □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #s.Done) -∗
      WP (App (Val #(methods c.ty go!"Done" c.v)) (Val #())) {{ Φ }}) ∗
  "#HErr" ∷
    (∀ cl : broadcast.t, □ (∀ Φ : val → IProp GF,
      own_broadcast_chan s.Done s.Done_gn s.PDone cl -∗
      ▷ (∀ err : interface.t,
          (match cl with
           | .Done => iprop(⌜err ≠ interface.nil⌝)
           | _ => if err = interface.nil then own_broadcast_chan s.Done s.Done_gn s.PDone cl
                  else own_broadcast_chan s.Done s.Done_gn s.PDone .Done) -∗
          Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }})) ∗
  "#HDone_ch" ∷ own_broadcast_chan s.Done s.Done_gn s.PDone .Unknown)

/-- (Rocq: `is_Context` is made `Transparent` again right after being sealed.) -/
abbrev is_Context (c : interface.t_ok) (s : Context_desc.t (IProp GF)) : IProp GF :=
  is_Context_def c s

instance is_Context_pers (c : interface.t_ok) (s : Context_desc.t (IProp GF)) :
    Persistent (is_Context c s) := by
  unfold is_Context is_Context_def; infer_instance

theorem wp_Cause (ctx : interface.t_ok) (ctx_desc : Context_desc.t (IProp GF)) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗
        "#Hctx" ∷ is_Context ctx ctx_desc }}
      (App (Val (@! context.Cause)) (Val #(interface.ok ctx)))
    {{ (err : interface.t), RET #err; True }} := by
  -- Unprovable as stated: `Cause` calls `c.Value(&cancelCtxKey)`, whose spec `is_Context` does not provide.
  sorry -- Rocq: Admitted

theorem wp_parentCancelCtx (parent : interface.t_ok) (parent_desc : Context_desc.t (IProp GF)) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗
        "#Hctx" ∷ is_Context parent parent_desc }}
      (App (Val (@! context.parentCancelCtx)) (Val #(interface.ok parent)))
    {{ (ctx : loc) (ok : Bool), RET (PairV #ctx #ok);
        if ok then ∃ c : context.cancelCtx.t, ctx ↦ c
        else iprop(⌜ctx = loc.null⌝) }} := by
  -- Unprovable as stated: `parentCancelCtx` calls `parent.Value(&cancelCtxKey)`, whose spec `is_Context` does not provide.
  sorry -- Rocq: Admitted

theorem wp_propagateCancel (c : loc) (parent : interface.t_ok)
    (parent_desc : Context_desc.t (IProp GF)) (child : interface.t_ok) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗
        "Hparent" ∷ is_Context parent parent_desc ∗
        "Hc" ∷ c ↦ (zero_val context.cancelCtx.t) }}
      (App (App (Val (c @!! go.type.PointerType context.cancelCtx @!! go!"propagateCancel"))
        (Val #(interface.ok parent))) (Val #(interface.ok child)))
    {{ RET #(); True }} := by
  -- Unprovable as stated: calls `parentCancelCtx` (hence `parent.Value`, unspecified by `is_Context`) and `AfterFunc` methods.
  sorry -- Rocq: Admitted

theorem wp_WithCancel (PDone' : IProp GF) (ctx : interface.t_ok)
    (ctx_desc : Context_desc.t (IProp GF)) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗ is_Context ctx ctx_desc }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok ctx)))
    {{ (ctx' : interface.t_ok) (done' : chan.t) (cancel : func.t),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, PDone' -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        is_Context ctx' { ctx_desc with PDone := iprop(ctx_desc.PDone ∨ PDone'), Done := done' } }} := by
  -- Unprovable as stated: goes through `propagateCancel`, which calls `parent.Value` (unspecified by `is_Context`).
  sorry -- Rocq: Admitted

theorem wp_WithDeadlineCause (parent : interface.t_ok) (parent_desc : Context_desc.t (IProp GF))
    (d : time.Time.t) (cause : error.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗ is_Context parent parent_desc }}
      (App (App (App (Val (@! context.WithDeadlineCause)) (Val #(interface.ok parent))) (Val #d))
        (Val #cause))
    {{ (ctx' : interface.t_ok) (done' : chan.t) (cancel : func.t),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        is_Context ctx' { parent_desc with Deadline := some d, PDone := iprop(True), Done := done' } }} := by
  -- Unprovable as stated: goes through `propagateCancel`, which calls `parent.Value` (unspecified by `is_Context`).
  sorry -- Rocq: Admitted

theorem wp_WithDeadline (parent : interface.t_ok) (parent_desc : Context_desc.t (IProp GF))
    (d : time.Time.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗ is_Context parent parent_desc }}
      (App (App (Val (@! context.WithDeadline)) (Val #(interface.ok parent))) (Val #d))
    {{ (ctx' : interface.t_ok) (done' : chan.t) (cancel : func.t),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        is_Context ctx' { parent_desc with Deadline := some d, PDone := iprop(True), Done := done' } }} := by
  -- Unprovable as stated: calls `WithDeadlineCause` (see there).
  sorry -- Rocq: Admitted

theorem wp_WithTimeout (parent : interface.t_ok) (parent_desc : Context_desc.t (IProp GF))
    (timeout : time.Duration.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗ is_Context parent parent_desc }}
      (App (App (Val (@! context.WithTimeout)) (Val #(interface.ok parent))) (Val #(timeout)))
    {{ (ctx' : interface.t_ok) (done' : chan.t) (cancel : func.t) (d : time.Time.t),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        is_Context ctx' { parent_desc with Deadline := some d, PDone := iprop(True), Done := done' } }} := by
  -- Unprovable as stated: calls `WithDeadline` (see there).
  sorry -- Rocq: Admitted

end wps

end context

end Perennial
end
