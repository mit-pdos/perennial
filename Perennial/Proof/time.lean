/-
Port of `new/proof/time.v`.

Lean notes:
* The Rocq axioms `wp_Now`, `wp_Until`, `wp_Time__Add` are stated without the
  package assumptions in Rocq (a Rocq bug: `Collection W` is not used by
  `Axiom`s). Here they bind `[package_sem : time.Assumptions]` explicitly.
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

instance Time.countable [ffi_syntax] : Pos.Countable time.Time.t :=
  .ofInjective (fun t => Pos.Countable.encode (t.wall', t.ext', t.loc'))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.time :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.time :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.time get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.time }} := by
  -- Unprovable: `UTC'init`, `Local'init`, ... are opaque (axioms in Perennial/Code/time.lean).
  sorry -- Rocq: Admitted

theorem wp_Time__sec (t : loc) (tv : time.Time.t) :
    {{ (t ↦ tv : IProp GF) }}
      (App (Val (t @!! go.type.PointerType time.Time @!! go!"sec")) (Val #()))
    {{ (x : w64), RET #x; t ↦ tv }} := by
  wp_start as Ht
  wp_auto
  wp_if_destruct
  · iapply HΦ $$ Ht
  · iapply HΦ $$ Ht

theorem wp_Time__unixSec (t : loc) (tv : time.Time.t) :
    {{ (t ↦ tv : IProp GF) }}
      (App (Val (t @!! go.type.PointerType time.Time @!! go!"unixSec")) (Val #()))
    {{ (x : w64), RET #x; t ↦ tv }} := by
  wp_start as Ht
  wp_auto
  wp_apply wp_Time__sec $$ [$Ht] as %x Ht
  iapply HΦ $$ Ht

theorem wp_Time__nsec (t : loc) (tv : time.Time.t) :
    {{ (t ↦ tv : IProp GF) }}
      (App (Val (t @!! go.type.PointerType time.Time @!! go!"nsec")) (Val #()))
    {{ (x : w32), RET #x; True }} := by
  wp_start as Ht
  wp_auto
  wp_end

theorem wp_Time__UnixNano' (t : time.Time.t) :
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time @!! go!"UnixNano")) (Val #()))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_auto
  wp_apply wp_Time__unixSec $$ [$t] as %x t
  wp_apply wp_Time__nsec $$ [$t] as %y -
  wp_end

theorem wp_Time__UnixNano (l : loc) (t : time.Time.t) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.type.PointerType time.Time @!! go!"UnixNano")) (Val #()))
    {{ (x : w64), RET #x; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply wp_Time__UnixNano' as %x -
  iapply HΦ $$ Hl

/-- Rocq `Axiom wp_Now` (Rocq omits the package assumptions; bound here). -/
axiom wp_Now [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
    [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
    [sem : go.Semantics] [package_sem : time.Assumptions] :
    {{ (True : IProp GF) }}
      (App (Val (@! time.Now)) (Val #()))
    {{ (t : time.Time.t), RET #t; True }}

/-- Rocq `Axiom wp_Until` (Rocq omits the package assumptions; bound here). -/
axiom wp_Until [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
    [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
    [sem : go.Semantics] [package_sem : time.Assumptions] (deadline : time.Time.t) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.Until)) (Val #deadline))
    {{ (x : w64), RET #x; True }}

/-- Rocq `Axiom wp_Time__Add` (Rocq omits the package assumptions; bound here). -/
axiom wp_Time__Add [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
    [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
    [sem : go.Semantics] [package_sem : time.Assumptions] (t : time.Time.t) (d : time.Duration.t) :
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time @!! go!"Add")) (Val #d))
    {{ (t : time.Time.t), RET #t; True }}

set_option goose.wp.extras true in
theorem wp_arbitraryTime :
    {{ (True : IProp GF) }}
      (App (Val time.arbitraryTime) (Val #()))
    {{ (t : time.Time.t), RET #t; True }} := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  rw [show go.type.Named go!"time.Time" [] = time.Time by with_unfolding_all rfl]
  wp_auto
  wp_end

theorem wp_Sleep (d : time.Duration.t) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.Sleep)) (Val #d))
    {{ RET #(); True }} := by
  wp_start
  wp_end

end wps

section chan_wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem wp_After (d : time.Duration.t) :
    {{ (True : IProp GF) }}
      (App (Val (@! time.After)) (Val #d))
    {{ (ch : loc) (γ : chan_names), RET #ch;
        is_chan_bag γ ch (V := time.Time.t) (fun _ => iprop(True)) }} := by
  wp_start
  rw [show go.type.Named go!"time.Time" [] = time.Time by with_unfolding_all rfl]
  wp_apply chan.wp_make2 (V := time.Time.t) $$ [] as %ch %γ ⟨#His, -, Hown⟩
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
