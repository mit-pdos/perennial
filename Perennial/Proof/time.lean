/-
Specs for the Go `time` package.

Notes:
* The axioms `wp_Now`, `wp_Until`, `Time.wp_Add` bind their package assumptions
  (`[package_sem : time.Assumptions]`) explicitly.
* `wp_After` needs the channel theory, which fixes `hlc := HasLC.hasLC` and
  `[allG GF]`; it lives in its own section. `Pos.Countable time.Time.t` (for the
  channel ghost state) is defined here.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.time
import Perennial.GeneratedProof.time
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Bag

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

section chan_wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
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

end chan_wps

end time

end Perennial
end
