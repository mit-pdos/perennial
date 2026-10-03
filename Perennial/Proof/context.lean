/-
Port of `new/proof/context.v`: specifications for Go's `context` package.

All specifications are `Admitted` in Rocq (and `wp_withCancel` is `Abort`ed, so
it is omitted here). Proved here: `wp_Cause`, `wp_parentCancelCtx`, and
`wp_WithDeadline` / `wp_WithTimeout` (from the specs of `WithDeadlineCause` /
`WithDeadline`); `wp_WithCancel`, `wp_WithDeadlineCause` and `wp_propagateCancel` stay
`sorry` (see the comments in their proofs: `atomic.Value` is unspecifiable in the model, and
`time.Time.Before`, `time.AfterFunc`, `Timer.Stop` have no model).

Lean deviations from Rocq (see the comments at each definition):
* Lazily determined Done channel. Rocq's `Context_desc` fixes the Done channel
  (`Done : chan.t`, `Done_gn : chan_names`) and `is_Context` has
  `"#HDone"`: `Done()` returns `s.Done` and `"#HDone_ch"`:
  `own_broadcast_chan s.Done s.Done_gn s.PDone Unknown`. This made `wp_WithCancel`,
  `wp_WithDeadlineCause`, `wp_WithDeadline`, `wp_WithTimeout` false as stated: their
  postconditions fix the new context's channel `done'` at return time, but
  `cancelCtx.Done` makes the channel lazily at the first `Done()` call, or `cancel`
  stores the shared, already closed `closedchan` if it runs first. Now:
  - `Context_desc.t`: the fields `Done` and `Done_gn : chan_names` are replaced by
    `Done_gn : Context_names`, two ghost names: `done_gn`, a one-shot cell holding the
    Done channel once it is determined, and `closed_gn`, the "context is done" flag.
  - new `Context_closed γ` (persistent: the context is done), replacing
    `own_broadcast_chan s.Done s.Done_gn s.PDone Done`;
  - new `is_Context_Done s ch γch` (persistent: `ch` is the Done channel; the done cell
    holds `ch`, and `ch` is a broadcast channel, with an existential proposition `Q`
    implying `□ s.PDone ∗ Context_closed s.Done_gn`), replacing
    `own_broadcast_chan s.Done s.Done_gn s.PDone Unknown`. Client lemmas:
    `is_Context_Done_is_chan`, `is_Context_Done_receive` (`recv_au`, e.g. for a `select`
    case), `is_Context_Done_nonblocking_receive`, `is_Context_Done_agree` (successive
    `Done()` calls return the same channel), `is_Context_Done_weaken`;
  - `is_Context`: `"#HDone"` returns some `ch` with `is_Context_Done s ch γch`;
    `"#HDone_ch"` is dropped; `"#HErr"` takes `Context_closed s.Done_gn` for `cl = Done`
    (nothing otherwise) and returns `□ s.PDone ∗ Context_closed s.Done_gn` for a non-nil
    error (where Rocq passes `own_broadcast_chan ... cl` in and out);
  - new `is_Context_weaken` (`is_Context` is monotone in `PDone`);
  - `wp_WithCancel`, `wp_WithDeadlineCause`, `wp_WithDeadline`, `wp_WithTimeout`: the
    existential `done' : chan.t` becomes `γ' : Context_names` and `Done := done'` becomes
    `Done_gn := γ'`.
* `wp_WithCancel`: the cancel function's precondition is `□ PDone'` instead of `PDone'`
  (closing the broadcast channel needs `□ PDone`).
* `wp_WithDeadlineCause`, `wp_WithDeadline`: the deadline is an existential `some d'` with
  `d' = d ∨ parent_desc.Deadline = some d'`, not `some d` (false when the parent's deadline
  is earlier: then `WithDeadlineCause` returns `WithCancel(parent)`).
* `is_init` has an extra conjunct `"#Hclosedchan"`: the global `closedchan`
  holds a fixed channel (Go never writes it after initialization). Needed by
  `parentCancelCtx`, which compares `parent.Done()` with `closedchan`.
* `is_Context` has an extra conjunct `"#HValue"`, the spec of
  `c.Value(&cancelCtxKey)`: the result, if it is a `*cancelCtx`, is a valid one
  (`is_cancelCtx`). `Cause`, `parentCancelCtx` (and through it
  `propagateCancel`, `removeChild`) call `Value(&cancelCtxKey)` to find the
  innermost `*cancelCtx`; Rocq's `is_Context` gives no spec for `Value`.
* new definitions `cancelCtxKey_any`, `cancelCtx_lock_inv`, `is_cancelCtx`,
  `is_cancelCtx_any`, `is_init_access`, `broadcast_chan_nonblocking_receive_Q`.
* `wp_parentCancelCtx`: postcondition `is_cancelCtx ctx` instead of
  `∃ c, ctx ↦ c` in the `ok` case.

Lean notes:
* Rocq's nested Texan triples inside `is_Context` (iProps) are written out as
  `□ ∀ Φ, P -∗ ▷ (∀ x, Q -∗ Φ v) -∗ WP e {{ Φ }}`.
* The broadcast idiom fixes `hlc := HasLC.hasLC` and uses `[allG GF]` (Rocq
  `broadcast_chanG`); the package-init instances are generic in `hlc`.
* A context whose Done channel is `nil` (never canceled, e.g. `Background()`) does not
  satisfy `is_Context`: `is_Context_Done` includes `is_chan`, which excludes `nil` (as did
  `own_broadcast_chan` in `"#HDone_ch"` before).
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

/-- Ghost names of a context (Lean deviation; see the file header). -/
structure Context_names where
  mk ::
  /-- `dghost_var (Option chan.t)`: the context's Done channel, fixed (as `some ch`, then
  discarded) by whoever determines it, e.g. the first `Done()` or `cancel` of a `*cancelCtx`. -/
  done_gn : GName
  /-- `dghost_var Bool`: `true` (discarded) once the context is done. -/
  closed_gn : GName

/-! Context logical descriptor. -/
namespace Context_desc
/-- Lean deviation from Rocq: Rocq's fields `Done : chan.t` and `Done_gn : chan_names` (the
Done channel and its names, fixed when the context is created) are replaced by
`Done_gn : Context_names`, the ghost names through which the Done channel is determined
later (see the file header). -/
structure t [ffi_syntax] (PROP : Type) where
  mk ::
  Values : gmap interface.t interface.t
  Deadline : Option time.Time.t
  Done_gn : Context_names
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

/-- The context with ghost names `γ` is done (canceled or past its deadline). Persistent;
replaces Rocq's `own_broadcast_chan s.Done s.Done_gn s.PDone broadcast.Done`. -/
def Context_closed (γ : Context_names) : IProp GF :=
  dghost_var γ.closed_gn .discard true

instance Context_closed_pers (γ : Context_names) : Persistent (Context_closed (GF := GF) γ) := by
  unfold Context_closed; infer_instance

/-- `ch` (with channel names `γch`) is the Done channel of the context `s`: the context's
done cell holds `ch`, and `ch` is a broadcast channel whose closing implies that `s` is done
(`Context_closed`) and `□ s.PDone`. Persistent; replaces Rocq's
`own_broadcast_chan s.Done s.Done_gn s.PDone broadcast.Unknown`.

The broadcast proposition `Q` is existential: a `*cancelCtx` whose channel is made by
`Done()` uses `Q := s.PDone ∗ Context_closed s.Done_gn`, while one whose `cancel` ran first
returns the shared, already closed `closedchan` (whose broadcast proposition is fixed at
package initialization), with `□ s.PDone ∗ Context_closed s.Done_gn` known when the done cell
is set. -/
def is_Context_Done_def (s : Context_desc.t (IProp GF)) (ch : chan.t) (γch : chan_names) :
    IProp GF :=
  iprop(dghost_var s.Done_gn.done_gn .discard (some ch) ∗
    ∃ Q : IProp GF, own_broadcast_chan ch γch Q .Unknown ∗
      □ (□ Q -∗ □ s.PDone ∗ Context_closed s.Done_gn))
@[irreducible] def is_Context_Done (s : Context_desc.t (IProp GF)) (ch : chan.t)
    (γch : chan_names) : IProp GF := is_Context_Done_def s ch γch
theorem is_Context_Done_unseal : @is_Context_Done = @is_Context_Done_def := by
  funext; with_unfolding_all rfl

instance is_Context_Done_pers (s : Context_desc.t (IProp GF)) (ch : chan.t) (γch : chan_names) :
    Persistent (is_Context_Done s ch γch) := by
  rw [is_Context_Done_unseal]; unfold is_Context_Done_def; infer_instance

def is_Context_def (c : interface.t_ok) (s : Context_desc.t (IProp GF)) : IProp GF :=
  iprop(
  "#HDeadline" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (True -∗ Φ (PairV #(s.Deadline.getD (zero_val time.Time.t))
                          #(match s.Deadline with | none => false | some _ => true))) -∗
      WP (App (Val #(methods c.ty go!"Deadline" c.v)) (Val #())) {{ Φ }}) ∗
  "#HDone" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ (ch : chan.t) (γch : chan_names), is_Context_Done s ch γch -∗ Φ #ch) -∗
      WP (App (Val #(methods c.ty go!"Done" c.v)) (Val #())) {{ Φ }}) ∗
  "#HErr" ∷
    (∀ cl : broadcast.t, □ (∀ Φ : val → IProp GF,
      (match cl with
       | .Done => Context_closed s.Done_gn
       | _ => iprop(True)) -∗
      ▷ (∀ err : interface.t,
          (match cl with
           | .Done => iprop(⌜err ≠ interface.nil⌝)
           | _ => if err = interface.nil then iprop(True)
                  else iprop(□ s.PDone ∗ Context_closed s.Done_gn)) -∗
          Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }})) ∗
  "#HValue" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ v : interface.t, is_cancelCtx_any v -∗ Φ #v) -∗
      WP (App (Val #(methods c.ty go!"Value" c.v)) (Val #cancelCtxKey_any)) {{ Φ }}))

/-- (Rocq: `is_Context` is made `Transparent` again right after being sealed.)

Lean deviations from Rocq (see the file header):
* `"#HDone"` returns some channel `ch` with `is_Context_Done s ch γch` instead of the fixed
  `s.Done`; Rocq's `"#HDone_ch"` (`own_broadcast_chan s.Done s.Done_gn s.PDone Unknown`) is
  dropped, as that knowledge now comes with `Done()`'s result.
* `"#HErr"`: the `own_broadcast_chan s.Done s.Done_gn s.PDone cl` resources are replaced by
  `Context_closed s.Done_gn` (precondition, only for `cl = Done`) and
  `□ s.PDone ∗ Context_closed s.Done_gn` (postcondition, for a non-nil error).
* the last conjunct `"#HValue"` is new. It only specifies the key `&cancelCtxKey`; the
  `Values` field of `Context_desc` stays unused, as in Rocq. -/
abbrev is_Context (c : interface.t_ok) (s : Context_desc.t (IProp GF)) : IProp GF :=
  is_Context_def c s

instance is_Context_pers (c : interface.t_ok) (s : Context_desc.t (IProp GF)) :
    Persistent (is_Context c s) := by
  unfold is_Context is_Context_def; infer_instance

/-! Client lemmas for the Done channel (they replace the `own_broadcast_chan` lemmas that
Rocq clients apply to `s.Done`). -/

theorem is_Context_Done_is_chan (s : Context_desc.t (IProp GF)) (ch : chan.t) (γch : chan_names) :
    is_Context_Done s ch γch ⊢ is_chan ch γch Unit := by
  rw [is_Context_Done_unseal]; unfold is_Context_Done_def
  iintro ⟨-, %Q, #Hbc, -⟩
  iapply own_broadcast_chan_is_chan $$ Hbc

/-- Successive `Done()` calls return the same channel. -/
theorem is_Context_Done_agree (s : Context_desc.t (IProp GF)) (ch1 ch2 : chan.t)
    (γ1 γ2 : chan_names) :
    is_Context_Done s ch1 γ1 ∗ is_Context_Done s ch2 γ2 ⊢ ⌜ch1 = ch2⌝ := by
  rw [is_Context_Done_unseal]; unfold is_Context_Done_def
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  ihave %h := dghost_var_agree _ _ _ _ _ $$ H1 H2
  ipureintro; exact Option.some.inj h

/-- Receiving from the Done channel (e.g. as a `select` case) returns only once the context is
done. -/
theorem is_Context_Done_receive (s : Context_desc.t (IProp GF)) (ch : chan.t) (γch : chan_names)
    (Φ : Unit → Bool → IProp GF) :
    ⊢ is_Context_Done s ch γch -∗
      (□ s.PDone ∗ Context_closed s.Done_gn -∗ Φ () false) -∗
      recv_au γch Unit Φ := by
  rw [is_Context_Done_unseal]; unfold is_Context_Done_def
  iintro ⟨-, %Q, #Hbc, #HQ⟩ HΦ
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
  iintro ⟨#Hq, -⟩
  iapply HΦ
  iapply HQ $$ Hq

/-- Variant of `own_broadcast_chan_nonblocking_receive` (for `Unknown`) that hands out the
broadcast proposition directly (no later credit needed). -/
theorem broadcast_chan_nonblocking_receive_Q (ch : chan.t) (γ : chan_names) (Q : IProp GF)
    (Φ : Unit → Bool → IProp GF) (Φnotready : IProp GF) :
    ⊢ own_broadcast_chan ch γ Q .Unknown -∗
      ((□ Q -∗ Φ () false) ∧ Φnotready) -∗
      nonblocking_recv_au_alt γ Unit Φ Φnotready := by
  iintro Hown HΦ
  icases own_broadcast_chan_open _ _ _ _ $$ Hown with ⟨%γch, #Hint, -⟩
  ihave #Hinv := is_broadcast_chan_internal_inv _ _ _ _ $$ Hint
  unfold nonblocking_recv_au_alt
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold broadcast_inv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hch
    imod Hmask with -
    icases HΦ with ⟨-, HΦ⟩
    imod Hclose $$ [Hch Hs] with -
    · inext; iexists .Idle; dsimp only; iframe
    imodintro
    iexact HΦ
  case RcvPending =>
    iintro Hch
    imod Hmask with -
    icases HΦ with ⟨-, HΦ⟩
    imod Hclose $$ [Hch Hs] with -
    · inext; iexists .RcvPending; dsimp only; iframe
    imodintro
    iexact HΦ
  case Closed.nil =>
    icases Hs with ⟨#HQ, #Hs⟩
    iintro Hch
    imod Hmask with -
    icases HΦ with ⟨HΦ, -⟩
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hs
    imodintro
    iapply HΦ $$ HQ
  all_goals (iexfalso; iexact Hs)

theorem is_Context_Done_nonblocking_receive (s : Context_desc.t (IProp GF)) (ch : chan.t)
    (γch : chan_names) (Φ : Unit → Bool → IProp GF) (Φnotready : IProp GF) :
    ⊢ is_Context_Done s ch γch -∗
      ((□ s.PDone ∗ Context_closed s.Done_gn -∗ Φ () false) ∧ Φnotready) -∗
      nonblocking_recv_au_alt γch Unit Φ Φnotready := by
  rw [is_Context_Done_unseal]; unfold is_Context_Done_def
  iintro ⟨-, %Q, #Hbc, #HQ⟩ HΦ
  iapply broadcast_chan_nonblocking_receive_Q _ _ _ _ _ $$ Hbc
  isplit
  · iintro #Hq
    icases HΦ with ⟨HΦ, -⟩
    iapply HΦ
    iapply HQ $$ Hq
  · icases HΦ with ⟨-, HΦ⟩
    iexact HΦ

/-- The Done proposition can be weakened. -/
theorem is_Context_Done_weaken (s : Context_desc.t (IProp GF)) (P' : IProp GF) (ch : chan.t)
    (γch : chan_names) :
    ⊢ □ (s.PDone -∗ P') -∗ is_Context_Done s ch γch -∗
      is_Context_Done { s with PDone := P' } ch γch := by
  rw [is_Context_Done_unseal]; unfold is_Context_Done_def
  iintro #HP ⟨#Hd, %Q, #Hbc, #HQ⟩
  isplitl []
  · iexact Hd
  iexists Q
  isplitl []
  · iexact Hbc
  imodintro
  iintro #Hq
  icases HQ $$ Hq with ⟨#Hp, #Hc⟩
  isplitl []
  · imodintro; iapply HP $$ Hp
  · iexact Hc

theorem is_Context_weaken (c : interface.t_ok) (s : Context_desc.t (IProp GF)) (P' : IProp GF) :
    ⊢ □ (s.PDone -∗ P') -∗ is_Context c s -∗ is_Context c { s with PDone := P' } := by
  unfold is_Context is_Context_def
  iintro #HP ⟨#HDeadline, #HDone, #HErr, #HValue⟩
  isplitl []
  · iexact HDeadline
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    iapply HDone
    · itrivial
    inext
    iintro %ch %γch #Hch
    iapply HΦ
    iapply is_Context_Done_weaken $$ HP Hch
  isplitl []
  · iintro %cl
    imodintro
    iintro %Φ Hpre HΦ
    ihave #HErr' := HErr $$ %cl
    iapply HErr' $$ Hpre
    inext
    iintro %err Herr
    iapply HΦ
    cases cl
    case Done => iexact Herr
    all_goals
      dsimp only
      by_cases herr : err = interface.nil
      · simp only [herr, ↓reduceIte]; itrivial
      · simp only [herr, ↓reduceIte]
        icases Herr with ⟨#Hp, #Hc⟩
        isplitl []
        · imodintro; iapply HP $$ Hp
        · iexact Hc
  · iexact HValue

theorem wp_Cause (ctx : interface.t_ok) (ctx_desc : Context_desc.t (IProp GF)) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗
        "#Hctx" ∷ is_Context ctx ctx_desc }}
      (App (Val (@! context.Cause)) (Val #(interface.ok ctx)))
    {{ (err : interface.t), RET #err; True }} := by
  wp_start as #Hctx
  unfold is_Context is_Context_def
  icases Hctx with ⟨#HDeadline, #HDone, #HErr, #HValue⟩
  wp_auto
  ihave #HErr' := HErr $$ %broadcast.t.Unknown
  wp_apply HErr' as %err -
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
  icases Hctx with ⟨#HDeadline, #HDone, #HErr, #HValue⟩
  wp_auto
  wp_apply HDone as %done %γdone #Hdone
  by_cases h1 : done = closed
  · simp only [h1, _root_.decide_true]
    wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  simp only [h1, _root_.decide_false]
  wp_auto
  by_cases h2 : done = chan.nil
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
        have h3 : decide (zero_val chan.t = done) = false := by
          simp only [decide_eq_false_iff_not]; exact fun h => h2 h.symm
        simp only [h3]
        wp_auto
        wp_end
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro; trivial
      | some ch =>
        wp_auto
        by_cases h4 : ch = done
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

/-- Lean deviations from Rocq: the new context's Done channel is no longer a fixed `done'`
(it does not exist yet when `WithCancel` returns), the postcondition gives fresh ghost names
`γ'` instead; the cancel function's precondition is `□ PDone'` instead of `PDone'` (closing a
broadcast channel needs the persistent `□ PDone`, and observers of the Done channel get
`□ (ctx_desc.PDone ∨ PDone')`). -/
theorem wp_WithCancel (PDone' : IProp GF) (ctx : interface.t_ok)
    (ctx_desc : Context_desc.t (IProp GF)) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗ is_Context ctx ctx_desc }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok ctx)))
    {{ (ctx' : interface.t_ok) (γ' : Context_names) (cancel : func.t),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, □ PDone' -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        is_Context ctx' { ctx_desc with PDone := iprop(ctx_desc.PDone ∨ PDone'), Done_gn := γ' } }} := by
  -- Unprovable: `WithCancel` builds a `*cancelCtx`, whose `Done`, `Err` and `cancel` methods
  -- (and `withCancel`'s call of `propagateCancel`) use the `atomic.Value` fields `done` and
  -- `err`. `atomic.Value`'s methods are translated Go code that reinterprets the `any` field
  -- `v` of a `Value` as an `efaceWords` struct of two `unsafe.Pointer`s (`Load`: `vp :=
  -- (*efaceWords)(unsafe.Pointer(v)); LoadPointer(&vp.typ)`, likewise `Store`/`Swap`/
  -- `CompareAndSwap`, which also use `runtime_procPin`). The model has no such layout law:
  -- `struct_field_ref efaceWords.t "typ" l` is unrelated to `struct_field_ref Value.t "v" l`,
  -- and an `interface.t` value is not a pair of words, so no spec of `Value.Load`/`Store` is
  -- provable from `l ↦ (v : Value.t)` (the loads hit unowned memory). With trusted models of
  -- `atomic.Value`'s methods (as for `sync.Mutex`), the remaining proof obligations are:
  -- * `withCancel`/`propagateCancel`: a `*cancelCtx` invariant (lock invariant of `c.mu` with
  --   `children`, each child with its stored `cancel` spec, and `cause`; an `inv` for the
  --   `done`/`err` cells, the done cell `Context_names.done_gn` and the closed flag), the
  --   `parentCancelCtx` branch (`p.err.Load()`, `p.children` map with `canceler` keys; it
  --   needs `is_cancelCtx_any` to relate the found `p`'s names and `PDone` to the parent's
  --   when `p.done.Load() == parent.Done()`), the `parent.(afterFuncer)` branch (a spec for
  --   the parent's `AfterFunc`, or the knowledge that its type has none), and the goroutine
  --   branch (`select` on `parent.Done()` / `child.Done()`);
  -- * the cancel closure: `c.cancel(true, Canceled, nil)`, including `removeChild` and the
  --   iteration over `c.children` (map `range` with interface keys);
  -- * `is_init` must additionally provide the `Canceled` global (a non-nil `error`) and the
  --   broadcast state of `closedchan` (closed, with `Q := True`).
  sorry -- Rocq: Admitted

/-- Lean deviations from Rocq: no fixed Done channel `done'` (fresh ghost names `γ'`, see
`wp_WithCancel`), and the deadline is `some d'` with `d' = d ∨ parent_desc.Deadline = some d'`
instead of `some d`: Rocq's `Deadline := Some d` is false when the parent's deadline `cur`
is before `d`, as `WithDeadlineCause` then returns `WithCancel(parent)`, whose `Deadline()` is
the parent's `cur`. -/
theorem wp_WithDeadlineCause (parent : interface.t_ok) (parent_desc : Context_desc.t (IProp GF))
    (d : time.Time.t) (cause : error.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗ is_Context parent parent_desc }}
      (App (App (App (Val (@! context.WithDeadlineCause)) (Val #(interface.ok parent))) (Val #d))
        (Val #cause))
    {{ (ctx' : interface.t_ok) (γ' : Context_names) (cancel : func.t) (d' : time.Time.t),
        RET (PairV #(interface.ok ctx') #cancel);
        ⌜d' = d ∨ parent_desc.Deadline = some d'⌝ ∗
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        is_Context ctx'
          { parent_desc with Deadline := some d', PDone := iprop(True), Done_gn := γ' } }} := by
  -- Unprovable: besides the `*cancelCtx` gaps of `wp_WithCancel` (`atomic.Value`), it calls
  -- `cur.Before(d)` (`time.Time.Before`), `time.AfterFunc` and (in `timerCtx.cancel`)
  -- `c.timer.Stop()`, which are neither translated (`Perennial/Code/time.toml`) nor
  -- axiomatized (Rocq has no specs for them).
  sorry -- Rocq: Admitted

/-- Lean deviations from Rocq: as for `wp_WithDeadlineCause`. -/
theorem wp_WithDeadline (parent : interface.t_ok) (parent_desc : Context_desc.t (IProp GF))
    (d : time.Time.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗ is_Context parent parent_desc }}
      (App (App (Val (@! context.WithDeadline)) (Val #(interface.ok parent))) (Val #d))
    {{ (ctx' : interface.t_ok) (γ' : Context_names) (cancel : func.t) (d' : time.Time.t),
        RET (PairV #(interface.ok ctx') #cancel);
        ⌜d' = d ∨ parent_desc.Deadline = some d'⌝ ∗
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        is_Context ctx'
          { parent_desc with Deadline := some d', PDone := iprop(True), Done_gn := γ' } }} := by
  wp_start as #Hctx
  wp_auto
  wp_apply wp_WithDeadlineCause $$ [$Hctx] as %ctx' %γ' %cancel %d' ⟨%hd, #Hcancel, #Hctx'⟩
  wp_end
  iframe #
  ipureintro; exact hd

/-- Lean deviation from Rocq: no fixed Done channel `done'` (see `wp_WithCancel`). -/
theorem wp_WithTimeout (parent : interface.t_ok) (parent_desc : Context_desc.t (IProp GF))
    (timeout : time.Duration.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.context ∗ is_Context parent parent_desc }}
      (App (App (Val (@! context.WithTimeout)) (Val #(interface.ok parent))) (Val #(timeout)))
    {{ (ctx' : interface.t_ok) (γ' : Context_names) (cancel : func.t) (d : time.Time.t),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        is_Context ctx'
          { parent_desc with Deadline := some d, PDone := iprop(True), Done_gn := γ' } }} := by
  wp_start as #Hctx
  wp_auto
  wp_apply time.wp_Now as %now -
  wp_apply time.wp_Time__Add as %d -
  wp_apply wp_WithDeadline $$ [$Hctx] as %ctx' %γ' %cancel %d' ⟨-, #Hcancel, #Hctx'⟩
  wp_end
  iframe #

end wps

end context

end Perennial
end
