/-
Port of `new/proof/context.v`: specifications for Go's `context` package.

All specifications are `Admitted` in Rocq (and `wp_withCancel` is `Abort`ed, so
it is omitted here). `wp_Cause` and `wp_parentCancelCtx` are proved here.

Lean deviations from Rocq (see the comments at each definition):
* `is_init` has an extra conjunct `"#Hclosedchan"`: the global `closedchan`
  holds a fixed channel (Go never writes it after initialization). Needed by
  `parentCancelCtx`, which compares `parent.Done()` with `closedchan`.
* `is_Context` has an extra conjunct `"#HValue"`, the spec of
  `c.Value(&cancelCtxKey)`: the result, if it is a `*cancelCtx`, is a valid one
  (`is_cancelCtx`). `Cause`, `parentCancelCtx` (and through it
  `propagateCancel`, `removeChild`) call `Value(&cancelCtxKey)` to find the
  innermost `*cancelCtx`; Rocq's `is_Context` gives no spec for `Value`.
* new definitions `cancelCtxKey_any`, `cancelCtx_lock_inv`, `is_cancelCtx`,
  `is_cancelCtx_any`, `is_init_access`.
* `wp_parentCancelCtx`: postcondition `is_cancelCtx ctx` instead of
  `∃ c, ctx ↦ c` in the `ok` case.

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

/-- Rocq `is_init`, plus (Lean deviation) `"#Hclosedchan"`: the global
`closedchan` holds a fixed channel. -/
abbrev is_init : IProp GF :=
  iprop("Hgoroutines" ∷
    inv nroot (∃ g, sync.atomic.own_Int32 (global_addr context.goroutines) (DFrac.own 1) g) ∗
  "#Hclosedchan" ∷ (∃ ch : chan.t, global_addr context.closedchan ↦□ ch) ∗
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

theorem is_init_access :
    is_pkg_init (PROP := IProp GF) pkg_id.context ⊢ is_init (GF := GF) := by
  with_unfolding_all exact is_pkg_init_access (PROP := IProp GF) pkg_id.context

/-- `&cancelCtxKey` converted to `any`: the key for which `Value` returns the
innermost enclosing `*cancelCtx`. -/
def cancelCtxKey_any [GoSemanticsFunctions] : interface.t :=
  interface.mk_ok (go.type.PointerType go.int) #(global_addr context.cancelCtxKey)

/-- Lock invariant of `c.mu` for a `*cancelCtx` `c`: the fields that the Go
code only accesses with `c.mu` held (`children` and `cause`; `done` and `err`
are `atomic.Value`s, also read without the lock). -/
def cancelCtx_lock_inv (c : loc) : IProp GF :=
  iprop(∃ (children : map.t) (cause : error.t),
    "children" ∷ struct_field_ref context.cancelCtx.t go!"children" c ↦ children ∗
    "cause" ∷ struct_field_ref context.cancelCtx.t go!"cause" c ↦ cause)

/-- `c` is a (shared) `*cancelCtx`. `atomic.Value` is implemented with
`unsafe.Pointer` conversions that the model cannot verify, so the spec of
`c.done.Load()` (it holds `nil` or a `chan struct{}`) is part of the
predicate. -/
def is_cancelCtx (c : loc) : IProp GF :=
  iprop(
  "#Hmu" ∷ sync.is_Mutex (struct_field_ref context.cancelCtx.t go!"mu" c) (cancelCtx_lock_inv c) ∗
  "#Hdone_Load" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ ch : Option chan.t,
          Φ #(match ch with
              | none => interface.nil
              | some ch => interface.mk_ok
                  (go.type.ChannelType go.chan_dir.sendrecv (go.type.StructType [])) #ch)) -∗
      WP (App (Val (struct_field_ref context.cancelCtx.t go!"done" c @!!
        go.type.PointerType sync.atomic.Value @!! go!"Load")) (Val #())) {{ Φ }}))

instance is_cancelCtx_pers (c : loc) : Persistent (is_cancelCtx (GF := GF) c) := by
  unfold is_cancelCtx; infer_instance

/-- The result of `Value(&cancelCtxKey)`: if it is a `*cancelCtx`, then it is a
valid one. -/
def is_cancelCtx_any (v : interface.t) : IProp GF :=
  match v with
  | interface.ok ii =>
    if ii.ty = go.type.PointerType context.cancelCtx then
      iprop(∃ c : loc, ⌜ii.v = #c⌝ ∗ is_cancelCtx c)
    else iprop(True)
  | interface.nil => iprop(True)

instance is_cancelCtx_any_pers (v : interface.t) : Persistent (is_cancelCtx_any (GF := GF) v) := by
  unfold is_cancelCtx_any
  split
  · split <;> infer_instance
  · infer_instance

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
  "#HDone_ch" ∷ own_broadcast_chan s.Done s.Done_gn s.PDone .Unknown ∗
  "#HValue" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ v : interface.t, is_cancelCtx_any v -∗ Φ #v) -∗
      WP (App (Val #(methods c.ty go!"Value" c.v)) (Val #cancelCtxKey_any)) {{ Φ }}))

/-- (Rocq: `is_Context` is made `Transparent` again right after being sealed.)

Lean deviation from Rocq: the last conjunct `"#HValue"` is new (see the file
header). It only specifies the key `&cancelCtxKey`; the `Values` field of
`Context_desc` stays unused, as in Rocq. -/
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
  wp_start as #Hctx
  unfold is_Context is_Context_def
  icases Hctx with ⟨#HDeadline, #HDone, #HErr, #HDone_ch, #HValue⟩
  wp_auto
  wp_apply HErr $$ [$HDone_ch] as %err -
  cases err with
  | nil =>
    wp_auto
    wp_end
  | ok ierr =>
    wp_auto
    unfold cancelCtxKey_any
    wp_apply HValue as %v #Hv
    cases v with
    | nil =>
      wp_auto
      wp_end
    | ok ii =>
      by_cases hty : ii.ty = go.type.PointerType context.cancelCtx
      · simp only [is_cancelCtx_any, hty, ↓reduceIte, decide_true]
        icases Hv with ⟨%cc, %hv, #Hcc⟩
        rw [hv]
        unfold is_cancelCtx
        icases Hcc with ⟨#Hmu, #Hdone_Load⟩
        wp_auto
        wp_apply sync.wp_Mutex__Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
        unfold cancelCtx_lock_inv
        icases Hinv with ⟨%children, %cause, Hchildren, Hcause⟩
        wp_auto
        wp_apply sync.wp_Mutex__Unlock $$ [$Hmu $Hlocked Hchildren Hcause]
        · inext; iexists _, _; iframe
        cases cause with
        | nil =>
          wp_auto
          wp_end
        | ok icause =>
          wp_auto
          wp_end
      · simp only [hty, ↓reduceIte, decide_false]
        wp_auto
        wp_end

/-- Lean deviation from Rocq: the postcondition in the `ok` case is
`is_cancelCtx ctx` (persistent knowledge that `ctx` is a valid shared
`*cancelCtx`) instead of Rocq's `∃ c, ctx ↦ c`. The returned `*cancelCtx` is
shared with every other user of the parent context (its fields are protected
by `ctx.mu` or are atomics), so full ownership of its points-to cannot be
returned. -/
theorem wp_parentCancelCtx (parent : interface.t_ok) (parent_desc : Context_desc.t (IProp GF)) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗
        "#Hctx" ∷ is_Context parent parent_desc }}
      (App (Val (@! context.parentCancelCtx)) (Val #(interface.ok parent)))
    {{ (ctx : loc) (ok : Bool), RET (PairV #ctx #ok);
        if ok then is_cancelCtx ctx
        else iprop(⌜ctx = loc.null⌝) }} := by
  wp_start as #Hctx
  ihave #Hpkg : is_pkg_init (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hi := is_init_access $$ Hpkg
  icases Hi with ⟨_, ⟨%closed, #Hclosed⟩, _⟩
  unfold is_Context is_Context_def
  icases Hctx with ⟨#HDeadline, #HDone, #HErr, #HDone_ch, #HValue⟩
  wp_auto
  wp_apply HDone
  by_cases h1 : parent_desc.Done = closed
  · simp only [h1, _root_.decide_true]
    wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  simp only [h1, _root_.decide_false]
  wp_auto
  by_cases h2 : parent_desc.Done = chan.nil
  · simp only [h2, _root_.decide_true]
    wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  simp only [h2, _root_.decide_false]
  wp_auto
  unfold cancelCtxKey_any
  wp_apply HValue as %v #Hv
  cases v with
  | nil =>
    wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  | ok ii =>
    by_cases hty : ii.ty = go.type.PointerType context.cancelCtx
    · simp only [is_cancelCtx_any, hty, ↓reduceIte, _root_.decide_true]
      icases Hv with ⟨%c, %hv, #Hc⟩
      rw [hv]
      wp_auto
      ihave #Hc' : is_cancelCtx c $$ []
      · iexact Hc
      unfold is_cancelCtx
      icases Hc' with ⟨#Hmu, #Hdone_Load⟩
      wp_apply Hdone_Load as %och
      cases och with
      | none =>
        wp_auto
        have h3 : decide (zero_val chan.t = parent_desc.Done) = false := by
          simp only [decide_eq_false_iff_not]; exact fun h => h2 h.symm
        simp only [h3]
        wp_auto
        wp_end
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro; trivial
      | some ch =>
        wp_auto
        by_cases h4 : ch = parent_desc.Done
        · simp only [h4, _root_.decide_true]
          wp_auto
          wp_end
          simp only [↓reduceIte]
          iexact Hc
        · simp only [h4, _root_.decide_false]
          wp_auto
          wp_end
          simp only [Bool.false_eq_true, ↓reduceIte]
          ipureintro; trivial
    · simp only [hty, ↓reduceIte, _root_.decide_false]
      wp_auto
      wp_end
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; trivial

theorem wp_propagateCancel (c : loc) (parent : interface.t_ok)
    (parent_desc : Context_desc.t (IProp GF)) (child : interface.t_ok) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗
        "Hparent" ∷ is_Context parent parent_desc ∗
        "Hc" ∷ c ↦ (zero_val context.cancelCtx.t) }}
      (App (App (Val (c @!! go.type.PointerType context.cancelCtx @!! go!"propagateCancel"))
        (Val #(interface.ok parent))) (Val #(interface.ok child)))
    {{ RET #(); True }} := by
  -- Still unprovable as stated (with `#HValue` the `parentCancelCtx` call is now covered):
  -- * `child.cancel(..)` and `child.Done()` are called, but the precondition says nothing
  --   about `child` (it would need a canceler spec for `child`);
  -- * `p.err.Load()` on the parent's `*cancelCtx` (`atomic.Value`, implemented with
  --   `unsafe.Pointer`; `is_cancelCtx` would need its spec, typing the stored value as an
  --   `error`), and the `p.children` map with `canceler` interface keys;
  -- * `parent.(afterFuncer)`: a parent with an `AfterFunc` method needs a spec for it;
  -- * the forked goroutine selects on `parent.Done()` and `child.Done()`.
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
  -- Unprovable as stated, independently of the parent's predicate: the postcondition fixes
  -- the `Done` channel `done'` of the new context when `WithCancel` returns, but
  -- `cancelCtx.Done` allocates its channel lazily, at the first `Done()` call (or uses
  -- `closedchan` if `cancel` runs first), so no such channel exists yet. Proving `is_Context`
  -- for a `*cancelCtx` would need `Context_desc.Done` to be determined later (ghost
  -- agreement), plus the `propagateCancel` gaps listed there and specs of
  -- `atomic.Value` (unverifiable `unsafe.Pointer` code).
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
  -- Unprovable as stated, independently of the parent's predicate: the postcondition fixes
  -- the `Done` channel `done'` of the new context when `WithCancel` returns, but
  -- `cancelCtx.Done` allocates its channel lazily, at the first `Done()` call (or uses
  -- `closedchan` if `cancel` runs first), so no such channel exists yet. Proving `is_Context`
  -- for a `*cancelCtx` would need `Context_desc.Done` to be determined later (ghost
  -- agreement), plus the `propagateCancel` gaps listed there and specs of
  -- `atomic.Value` (unverifiable `unsafe.Pointer` code).
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
  -- Unprovable as stated: calls `WithDeadlineCause` (see there: lazily created `Done`
  -- channel; also `time.AfterFunc` for the timer).
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
