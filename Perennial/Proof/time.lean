/-
Specs for the Go `time` package.

Notes:
* The `Time` arithmetic is translated and proved (`Time.wp_Add`, `Time.wp_Sub`,
  `Time.wp_Before`, `Time.wp_Equal`, `wp_Since`, `wp_Until`, ...); the specs only say that
  these return some value (no panics; `Sub` saturates, the others wrap or fall back to the wall
  clock). `Since` and `Until` read the global `startNano`, so they take `isPkgInit`
  (`isInit`); they call `Now`, whose spec `wp_Now` is an axiom (`Now` reads the clock through
  the `go:linkname` `runtimeNow`). The model of `runtimeIsBubbled` (true only inside a
  `testing/synctest` bubble) is an arbitrary boolean (`TrustedCode/time.lean`).
* The axioms bind their package assumptions (`[package_sem : time.Assumptions]`) explicitly.
* `AfterFunc` is translated; the runtime's `newTimer` (a fresh `*Timer` and a goroutine that
  calls the callback) is modeled in `TrustedCode/time.lean`. `Stop` of its timers is the axiom
  `Timer.wp_Stop_func`.
* `wp_After` needs the channel theory, which fixes `hlc := HasLC.hasLC` and
  `[allG GF]`; it lives in its own section. `Pos.Countable time.Time.t` (for the
  channel ghost state) is defined here.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.time
public import Perennial.GeneratedProof.time
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace time

instance Time.countable [FfiSyntax] : Pos.Countable time.Time :=
  .ofInjective (fun t => Pos.Countable.encode (t.wall', t.ext', t.loc'))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- The package invariant: the global `startNano` (`runtimeNano() - 1`, set by the package's
initialization; Go never writes it afterwards) holds a fixed value. `Since` and `Until` read
it. -/
abbrev isInit : IProp GF :=
  iprop(∃ v : w64, globalAddr time.startNano ↦□ v)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.time :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.time :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.time get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.time }} := by
  -- Unprovable: `UTC'init`, `Local'init`, ... are opaque (axioms in Perennial/Code/time.lean).
  sorry

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.time ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.time

theorem Time.wp_sec (t : Loc) (tv : time.Time) :
    {{ (t ↦ tv : IProp GF) }}
      (App (Val (t @!! go.GoType.PointerType time.Time.ty @!! go!"sec")) (Val #()))
    {{ (x : w64), RET #x; t ↦ tv }} := by
  wp_start as Ht
  wp_auto
  wp_if_destruct
  · iapply HΦ $$ Ht
  · iapply HΦ $$ Ht

theorem Time.wp_unixSec (t : Loc) (tv : time.Time) :
    {{ (t ↦ tv : IProp GF) }}
      (App (Val (t @!! go.GoType.PointerType time.Time.ty @!! go!"unixSec")) (Val #()))
    {{ (x : w64), RET #x; t ↦ tv }} := by
  wp_start as Ht
  wp_auto
  wp_apply Time.wp_sec $$ [$Ht] as %x Ht
  iapply HΦ $$ Ht

theorem Time.wp_nsec (t : Loc) (tv : time.Time) :
    {{ (t ↦ tv : IProp GF) }}
      (App (Val (t @!! go.GoType.PointerType time.Time.ty @!! go!"nsec")) (Val #()))
    {{ (x : w32), RET #x; t ↦ tv }} := by
  wp_start as Ht
  wp_auto
  wp_end

theorem Time.wp_UnixNano' (t : time.Time) :
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"UnixNano")) (Val #()))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_auto
  wp_apply Time.wp_unixSec $$ [$t] as %x t
  wp_apply Time.wp_nsec $$ [$t] as %y -
  wp_end

theorem Time.wp_UnixNano (l : Loc) (t : time.Time) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"UnixNano")) (Val #()))
    {{ (x : w64), RET #x; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply Time.wp_UnixNano' as %x -
  iapply HΦ $$ Hl

/-- Spec of `time.Now` (axiom). -/
axiom wp_Now [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
    [sem : go.Semantics] [package_sem : time.Assumptions] :
    {{ (True : IProp GF) }}
      (App (Val (@! time.Now)) (Val #()))
    {{ (t : time.Time), RET #t; True }}

/-- `(*Time).stripMono()`: some new value of `*t`. -/
theorem Time.wp_stripMono (l : Loc) (tv : time.Time) :
    {{ (l ↦ tv : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"stripMono")) (Val #()))
    {{ (tv' : time.Time), RET #(); l ↦ tv' }} := by
  wp_start as Hl
  wp_auto
  wp_if_destruct
  · wp_end
  · wp_apply Time.wp_sec $$ [$Hl] as %x Hl
    wp_end

/-- `(*Time).addSec(d)`: some new value of `*t`. -/
theorem Time.wp_addSec (l : Loc) (tv : time.Time) (d : w64) :
    {{ (l ↦ tv : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"addSec")) (Val #d))
    {{ (tv' : time.Time), RET #(); l ↦ tv' }} := by
  wp_start as Hl
  wp_auto
  wp_if_destruct
  · wp_if_destruct <;> (try wp_if_destruct) <;> wp_end
  · wp_if_destruct
    · wp_if_destruct
      · wp_end
      · wp_apply Time.wp_stripMono $$ [$Hl] as %tv' Hl
        wp_if_destruct <;> (try wp_if_destruct) <;> wp_end
    · wp_apply Time.wp_stripMono $$ [$Hl] as %tv' Hl
      wp_if_destruct <;> (try wp_if_destruct) <;> wp_end

/-- Spec of `Time.Add`: some time. -/
theorem Time.wp_Add (t : time.Time) (d : time.Duration) :
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"Add")) (Val #d))
    {{ (t : time.Time), RET #t; True }} := by
  wp_start
  wp_auto
  wp_apply Time.wp_nsec $$ [$t] as %ns t
  wp_if_destruct <;> (try wp_if_destruct) <;>
    (wp_apply Time.wp_addSec $$ [$t] as %tv' t
     repeat' (first | wp_if_destruct | wp_apply Time.wp_stripMono $$ [$t] as %tv'' t)
     all_goals wp_end)

/-- `(*Time).Add`: the value method on `*l` (`ptr_Add_unfold`, the method set of `*Time`). -/
theorem Time.wp_ptr_Add (l : Loc) (t : time.Time) (d : time.Duration) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Add")) (Val #d))
    {{ (t' : time.Time), RET #t'; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply Time.wp_Add as %t' -
  iapply HΦ $$ Hl

/-- Spec of `Time.Before`: some `bool`. -/
theorem Time.wp_Before (t u : time.Time) :
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"Before")) (Val #u))
    {{ (b : Bool), RET #b; True }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply Time.wp_sec $$ [$t] as %ts t
    wp_apply Time.wp_sec $$ [$u] as %us u
    repeat' (first | wp_if_destruct | wp_apply Time.wp_nsec $$ [$t] as %tn t |
      wp_apply Time.wp_nsec $$ [$u] as %un u)
    all_goals wp_end
  · wp_end

/-- `(*Time).Before`. -/
theorem Time.wp_ptr_Before (l : Loc) (t u : time.Time) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Before")) (Val #u))
    {{ (b : Bool), RET #b; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply Time.wp_Before as %b -
  iapply HΦ $$ Hl

/-- Spec of `Time.Equal`: some `bool`. -/
theorem Time.wp_Equal (t u : time.Time) :
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"Equal")) (Val #u))
    {{ (b : Bool), RET #b; True }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply Time.wp_sec $$ [$t] as %ts t
    wp_apply Time.wp_sec $$ [$u] as %us u
    repeat' (first | wp_if_destruct | wp_apply Time.wp_nsec $$ [$t] as %tn t |
      wp_apply Time.wp_nsec $$ [$u] as %un u)
    all_goals wp_end
  · wp_end

/-- Spec of `subMono`: some duration. -/
theorem wp_subMono (t u : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! time.subMono)) (Val #t)) (Val #u))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_auto
  repeat' wp_if_destruct
  all_goals wp_end

/-- Spec of `Time.Sub`: some duration. -/
theorem Time.wp_Sub (t u : time.Time) :
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"Sub")) (Val #u))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply Time.wp_sec $$ [$t] as %ts t
    wp_apply Time.wp_sec $$ [$u] as %us u
    wp_apply Time.wp_nsec $$ [$t] as %tn t
    wp_apply Time.wp_nsec $$ [$u] as %un u
    wp_apply Time.wp_ptr_Add $$ [$u] as %u' u
    wp_apply Time.wp_Equal as %b -
    wp_if_destruct
    · wp_end
    · wp_apply Time.wp_ptr_Before $$ [$t] as %b' t
      wp_if_destruct <;> wp_end
  · wp_apply wp_subMono as %d -
    wp_end

/-- `(*Time).Sub`. -/
theorem Time.wp_ptr_Sub (l : Loc) (t u : time.Time) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Sub")) (Val #u))
    {{ (d : w64), RET #d; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply Time.wp_Sub as %d -
  iapply HΦ $$ Hl

theorem wp_runtimeNano :
    {{ (True : IProp GF) }}
      (App (Val (@! time.runtimeNano)) (Val #()))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  wp_end

theorem wp_runtimeIsBubbled :
    {{ (True : IProp GF) }}
      (App (Val (@! time.runtimeIsBubbled)) (Val #()))
    {{ (b : Bool), RET #b; True }} := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  wp_end

/-- Spec of `time.Since`: some duration (`Now().Sub(t)`, or `t`'s monotonic reading
subtracted from the current one). It reads the global `startNano` (`isPkgInit`). -/
theorem wp_Since (t : time.Time) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
      (App (Val (@! time.Since)) (Val #t))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨%sn, #Hsn⟩
  wp_auto
  repeat' (first | wp_if_destruct |
    (wp_apply wp_runtimeIsBubbled as %b -; cases b <;> (try wp_auto)) |
    wp_apply wp_runtimeNano as %x - | wp_apply wp_subMono as %d - |
    wp_apply wp_Now as %now - | wp_apply Time.wp_Sub as %d - |
    wp_apply Time.wp_ptr_Sub $$ [$t] as %d t)
  all_goals wp_end

/-- Spec of `time.Until`: some duration (`t.Sub(Now())`, or the current monotonic reading
subtracted from `t`'s). It reads the global `startNano` (`isPkgInit`). -/
theorem wp_Until (t : time.Time) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
      (App (Val (@! time.Until)) (Val #t))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨%sn, #Hsn⟩
  wp_auto
  repeat' (first | wp_if_destruct |
    (wp_apply wp_runtimeIsBubbled as %b -; cases b <;> (try wp_auto)) |
    wp_apply wp_runtimeNano as %x - | wp_apply wp_subMono as %d - |
    wp_apply wp_Now as %now - | wp_apply Time.wp_Sub as %d - |
    wp_apply Time.wp_ptr_Sub $$ [$t] as %d t)
  all_goals wp_end

set_option goose.wp.extras true in
theorem wp_arbitraryTime :
    {{ (True : IProp GF) }}
      (App (Val time.arbitraryTime) (Val #()))
    {{ (t : time.Time), RET #t; True }} := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  rw [show go.GoType.Named go!"time.Time" [] = time.Time.ty by with_unfolding_all rfl]
  wp_auto
  wp_end

theorem wp_Sleep (d : time.Duration) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.Sleep)) (Val #d))
    {{ RET #(); True }} := by
  wp_start
  wp_end

end wps

/-- `t` was returned by `NewTimer` (opaque): the runtime allocated it as the head of one of its
timers (`runtime.timeTimer`: the `Timer`'s fields followed by the runtime's state) and set its
`initTimer`, so that `Stop` and `Reset` may call the runtime's `stopTimer` and `resetTimer` on
it. Only the axiom `wp_NewTimer` provides it; no points-to gives it, so a `Timer` the program
allocates, or a copy of one, is not one. Its meaning is fixed by the axioms that mention it
(`wp_NewTimer`, `Timer.wp_Stop`, `Timer.wp_Reset`); nothing else is proved about it (the value
`False` only shows that the type is inhabited: Lean does not unfold an `opaque`). -/
opaque newTimerMade {GF : BundledGFunctors} (t : Loc) : IProp GF := iprop(False)

section chan_wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem wp_After (d : time.Duration) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.After)) (Val #d))
    {{ (ch : Loc) (γ : ChanNames), RET #ch;
        isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }} := by
  wp_start
  rw [show go.GoType.Named go!"time.Time" [] = time.Time.ty by with_unfolding_all rfl]
  wp_apply chan.wp_make2 (V := time.Time) $$ [] as %ch %γ ⟨#His, -, Hown⟩
  · ipureintro; decide
  imod start_bag (fun _ => iprop(True)) _ ch γ trivial $$ His Hown with #Hch
  wp_apply wp_fork $$ []
  · wp_apply wp_arbitraryTime as %t -
    wp_apply wp_bag_send $$ [$Hch]
    itrivial
  wp_end

/-! ### Timers (the trust boundary: `NewTimer`, `Timer.Stop` and `Timer.Reset` are not
translated; the runtime's timers are not modelled)

A `*Timer` from `NewTimer` is `isTimer t ch γ`: its `C` field holds, for good, a channel `ch` on
which a receive may yield some time (a bag of times, `isChanBag`, with no logical content), and
`t` is one of the runtime's timers (`newTimerMade t`). The specs say nothing about *when* (or
whether) a value arrives: `Stop` and `Reset` return some `bool` and change nothing the proof can
observe. This over-approximates Go's timers (a stopped timer's channel delivers nothing; the
model allows it), which is sound for safety.

`newTimerMade t` is what makes `isTimer` unforgeable. The points-to of `C` alone is not: a
program can allocate its own `Timer` and copy `C` into it (`u := new(time.Timer); u.C = t.C`),
and Go's `Stop` and `Reset` on that `u` panic ("uninitialized Timer"); with the points-to of
`initTimer` as well, it could copy the whole struct (`*u = *t`), and the runtime's `stopTimer`
and `resetTimer` would treat the memory after `u` as their timer state. -/

/-- `t` is a `*Timer` made by `NewTimer`, whose channel `C` is `ch` (persistent). -/
def isTimer (t : Loc) (ch : Loc) (γ : ChanNames) : IProp GF :=
  iprop(structFieldRef time.Timer go!"C" t ↦□ ch ∗
    isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) ∗
    □ newTimerMade (GF := GF) t)

instance isTimer_persistent (t ch : Loc) (γ : ChanNames) :
    Persistent (isTimer (GF := GF) t ch γ) := by
  unfold isTimer; infer_instance

/-- Spec of `time.NewTimer(d)` (axiom): a `*Timer` (`isTimer`), one of the runtime's timers
(`newTimerMade`). -/
axiom wp_NewTimer [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
    [sem : go.Semantics] [package_sem : time.Assumptions] (d : time.Duration) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.NewTimer)) (Val #d))
    {{ (t : Loc) (ch : Loc) (γ : ChanNames), RET #t; isTimer t ch γ }}

/-- Spec of `(*Timer).Stop()` (axiom): some `bool`, for a timer made by `NewTimer` (`isTimer`, whose
`newTimerMade t` a `Timer` the program made, such as a copy, does not have). -/
axiom Timer.wp_Stop [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
    [sem : go.Semantics] [package_sem : time.Assumptions] (t ch : Loc) (γ : ChanNames) :
    {{ isTimer (GF := GF) t ch γ }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Stop")) (Val #()))
    {{ (b : Bool), RET #b; True }}

/-- Spec of `(*Timer).Reset(d)` (axiom): some `bool`, for a timer made by `NewTimer` (`isTimer`; see
`Timer.wp_Stop`). -/
axiom Timer.wp_Reset [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
    [sem : go.Semantics] [package_sem : time.Assumptions] (t ch : Loc) (γ : ChanNames)
    (d : time.Duration) :
    {{ isTimer (GF := GF) t ch γ }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Reset")) (Val #d))
    {{ (b : Bool), RET #b; True }}

/-! ### `AfterFunc` timers

`AfterFunc(d, f)` is translated: it calls the runtime's `newTimer` (modeled in
`TrustedCode/time.lean` as a fresh `*Timer` with `initTimer` set and a goroutine that calls the
callback) with `goFunc`, which runs `f` in a new goroutine. `Stop` is not translated (it calls
the runtime's `stopTimer`); `Timer.wp_Stop_func` is its spec. -/

/-- `t` is a `*Timer` made by `AfterFunc` (persistent): `initTimer` is set. Only `wp_AfterFunc`
gives it out (with no access to `C`, see `Timer.wp_Stop_func`). -/
def isFuncTimer (t : Loc) : IProp GF :=
  iprop(structFieldRef time.Timer go!"initTimer" t ↦□ true)

instance isFuncTimer_persistent (t : Loc) : Persistent (isFuncTimer (GF := GF) t) := by
  unfold isFuncTimer; infer_instance

theorem wp_when (d : time.Duration) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.when)) (Val #d))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_auto
  repeat' (first | wp_if_destruct | wp_apply wp_runtimeNano as %x -)
  all_goals wp_end

/-- `AfterFunc(d, f)`: `f()` runs in a new goroutine (the model ignores the delay, and an
execution in which `f` never runs is a prefix of one in which it does), so it must be safe to
run then (a panic in `f` that `f` does not recover is stuck, so its WP rules it out). -/
theorem wp_AfterFunc (d : time.Duration) (f : GoFunc) :
    {{ (WP (App (Val #f) (Val #())) {{ _v, True }} : IProp GF) }}
      (App (App (Val (@! time.AfterFunc)) (Val #d)) (Val #f))
    {{ (t : Loc), RET #t; isFuncTimer (GF := GF) t }} := by
  wp_start as Hf
  wp_auto
  wp_apply wp_when as %w -
  wp_func_call
  wp_call
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  iStructNamed t
  ipersist initTimer
  wp_bind (Fork _)
  iapply wp_fork $$ [Hf]
  · inext
    wp_apply wp_ArbitraryInt as %x1 -
    wp_apply wp_ArbitraryInt as %x2 -
    wp_func_call
    wp_call
    wp_auto
    wp_bind (Fork _)
    iapply wp_fork $$ [Hf]
    · inext; iexact Hf
    inext
    wp_auto
    itrivial
  inext
  wp_pures
  iapply HΦ
  unfold isFuncTimer
  iexact initTimer

/-- Spec of `(*Timer).Stop()` for a timer made by `AfterFunc` (axiom): some `bool`. Go's `Stop`
checks `initTimer` (set by the runtime's `newTimer`) and calls the runtime's `stopTimer`, which
stops the timer if it has not fired (so that `f` does not run) and reports whether it did; the
model of `newTimer` runs `f` regardless, so the result says nothing the proof can use.
`isFuncTimer t` cannot be obtained for a timer that is not `AfterFunc`'s (on which Go's
`stopTimer` would treat the memory after the `Timer` as runtime state): `initTimer` is
unexported, and `wp_AfterFunc` withholds the points-to of `C`, so the `Timer` cannot be
copied. -/
axiom Timer.wp_Stop_func [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [package_sem : time.Assumptions]
    (t : Loc) :
    {{ isFuncTimer (GF := GF) t }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Stop")) (Val #()))
    {{ (b : Bool), RET #b; True }}

end chan_wps

end time

end Perennial
end
