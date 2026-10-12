/-
Specs for the Go `time` package.

Notes:
* The axioms `wp_Now`, `wp_Until`, `Time.wp_Add` bind their package assumptions
  (`[package_sem : time.Assumptions]`) explicitly. `Time.Add` is translated (for its
  pointer-receiver method, `Time.wp_ptr_Add`), but `Time.wp_Add` stays an axiom: the body
  uses `&^`, which `GoOp GoBitClear` leaves without semantics, and calls the untranslated
  `addSec` and `stripMono`.
* The timer specs (`wp_NewTimer`, `Timer.wp_Stop`, `Timer.wp_Reset`, `wp_After`) need the
  channel theory, which fixes `hlc := HasLC.hasLC`; they live in their own section.
  `Pos.Countable time.Time.t` (for the channel ghost state) is defined here.
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

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.time :=
  define_is_pkg_init iprop(True)
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
    {{ (x : w32), RET #x; True }} := by
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

/-- Spec of `time.Until` (axiom). -/
axiom wp_Until [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
    [sem : go.Semantics] [package_sem : time.Assumptions] (deadline : time.Time) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.Until)) (Val #deadline))
    {{ (x : w64), RET #x; True }}

/-- Spec of `Time.Add` (axiom). -/
axiom Time.wp_Add [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
    [sem : go.Semantics] [package_sem : time.Assumptions] (t : time.Time) (d : time.Duration) :
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"Add")) (Val #d))
    {{ (t : time.Time), RET #t; True }}

/-- `(*Time).Add`: the value method on `*l` (`ptr_Add_unfold`, the method set of `*Time`). -/
theorem Time.wp_ptr_Add (l : Loc) (t : time.Time) (d : time.Duration) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Add")) (Val #d))
    {{ (t' : time.Time), RET #t'; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply Time.wp_Add as %t' -
  iapply HΦ $$ Hl

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

/-- `time.Since(t)`: some duration (`Since.impl`, a clock reading). -/
theorem wp_Since (t : time.Time) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.Since)) (Val #t))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  wp_end

end wps

section chan_wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-! ### Timers

`NewTimer` is a trusted model (`NewTimer.impl`); `Timer.Stop`, `Timer.Reset`, `when` and `After`
are translated, over the trusted runtime primitives `stopTimer`, `resetTimer` and `runtimeNano`.

A `*Timer` from `NewTimer` is `isTimer t ch γ`: its `C` field holds, for good, a channel `ch` on
which a receive may yield some time (a bag of times, `isChanBag`, with no logical content), and
its `initTimer` field holds `true`. The specs say nothing about *when* (or whether) a value
arrives: `Stop` and `Reset` return some `bool` and change nothing the proof can observe. -/

/-- `t` is a `*Timer` made by `NewTimer`, whose channel `C` is `ch` (persistent). -/
def isTimer (t : Loc) (ch : Loc) (γ : ChanNames) : IProp GF :=
  iprop(structFieldRef time.Timer go!"C" t ↦□ ch ∗
    structFieldRef time.Timer go!"initTimer" t ↦□ true ∗
    isChanBag γ ch (V := time.Time) (fun _ => iprop(True)))

instance isTimer_persistent (t ch : Loc) (γ : ChanNames) :
    Persistent (isTimer (GF := GF) t ch γ) := by
  unfold isTimer; infer_instance

theorem wp_NewTimer (d : time.Duration) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.NewTimer)) (Val #d))
    {{ (t : Loc) (ch : Loc) (γ : ChanNames), RET #t; isTimer t ch γ }} := by
  wp_start
  rw [show go.GoType.Named go!"time.Time" [] = time.Time.ty by with_unfolding_all rfl]
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_apply wp_ArbitraryInt as %x -
  wp_if_destruct
  all_goals
  wp_apply chan.wp_make2 (V := time.Time) $$ [] as %ch %γ ⟨#His, -, Hown⟩
  · ipureintro; decide
  imod start_bag (fun _ => iprop(True)) _ ch γ (by simp) $$ His Hown with #Hch
  wp_apply wp_fork $$ []
  · wp_pures
    wp_for
    try simp only [decide_eq_true_eq, ↓reduceIte]
    try wp_auto
    wp_apply wp_arbitraryTime as %t -
    wp_apply wp_bag_send $$ [$Hch]
    wp_for_post
    iempintro
  iapply wp_fupd
  wp_alloc tl as Ht
  iStructNamed Ht
  ipersist C
  ipersist initTimer
  imodintro
  iapply HΦ
  unfold isTimer
  iframe #

theorem wp_stopTimer (t : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.stopTimer)) (Val #t))
    {{ (b : Bool), RET #b; True }} := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  wp_end

theorem wp_resetTimer (t : Loc) (w p : w64) :
    {{ (True : IProp GF) }}
      (App (App (App (Val (@! time.resetTimer)) (Val #t)) (Val #w)) (Val #p))
    {{ (b : Bool), RET #b; True }} := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  wp_end

theorem wp_runtimeNano :
    {{ (True : IProp GF) }}
      (App (Val (@! time.runtimeNano)) (Val #()))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  wp_end

theorem wp_when (d : time.Duration) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.when)) (Val #d))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply wp_runtimeNano as %x -
    wp_end
  · wp_apply wp_runtimeNano as %x -
    wp_if_destruct <;> wp_end

theorem Timer.wp_Stop (t ch : Loc) (γ : ChanNames) :
    {{ isTimer (GF := GF) t ch γ }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Stop")) (Val #()))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as #Ht
  unfold isTimer
  icases Ht with ⟨#HC, #Hinit, #Hch⟩
  wp_auto
  wp_apply wp_stopTimer as %b -
  wp_end

theorem Timer.wp_Reset (t ch : Loc) (γ : ChanNames) (d : time.Duration) :
    {{ isTimer (GF := GF) t ch γ }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Reset")) (Val #d))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as #Ht
  unfold isTimer
  icases Ht with ⟨#HC, #Hinit, #Hch⟩
  wp_auto
  wp_apply wp_when as %w -
  wp_apply wp_resetTimer as %b -
  wp_end

theorem wp_After (d : time.Duration) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.After)) (Val #d))
    {{ (ch : Loc) (γ : ChanNames), RET #ch;
        isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }} := by
  wp_start
  wp_auto
  wp_apply wp_NewTimer as %t %ch %γ #Ht
  unfold isTimer
  icases Ht with ⟨#HC, #Hinit, #Hch⟩
  wp_auto
  wp_end

end chan_wps

end time

end Perennial
end
