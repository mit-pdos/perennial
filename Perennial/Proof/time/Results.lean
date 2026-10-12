/-
Results of `time` derived from the linked ones: the methods of `*Time` lifted from the value
methods (`Time.wp_ptr_Add`, `Time.wp_ptr_Before`, `Time.wp_ptr_Sub`, `Time.wp_ptr_UnixNano`),
`Time.wp_UnixNano'` (the old name of `UnixNano`'s spec), and the two cases of `Timer.Stop`'s spec
(`Timer.wp_Stop_timer` for a `NewTimer` timer, `Timer.wp_Stop_func` for an `AfterFunc` one).
-/
module

public import Perennial.Proof.time.Link
public import Perennial.Proof.time.PtrMethods

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace time

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `Time.UnixNano()` (`UnixNano`'s one spec, `Time.wp_UnixNano`, under its old name). -/
theorem Time.wp_UnixNano' (t : time.Time) :
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"UnixNano")) (Val #()))
    {{ (x : w64), RET #x; True }} :=
  Time.wp_UnixNano t

/-- `(*Time).UnixNano`: the value method on `*l` (`ptr_UnixNano_unfold`). (Was
`Time.wp_UnixNano`, which is now the value method's spec.) -/
theorem Time.wp_ptr_UnixNano (l : Loc) (t : time.Time) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"UnixNano")) (Val #()))
    {{ (x : w64), RET #x; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply Time.wp_UnixNano as %x -
  iapply HΦ $$ Hl

/-- `(*Time).Add`: the value method on `*l` (`ptr_Add_unfold`, the method set of `*Time`). -/
theorem Time.wp_ptr_Add (l : Loc) (t : time.Time) (d : time.Duration) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Add")) (Val #d))
    {{ (t' : time.Time), RET #t'; l ↦ t }} :=
  Time.wp_ptr_Add_of Time.wp_Add l t d

/-- `(*Time).Before`. -/
theorem Time.wp_ptr_Before (l : Loc) (t u : time.Time) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Before")) (Val #u))
    {{ (b : Bool), RET #b; l ↦ t }} :=
  Time.wp_ptr_Before_of Time.wp_Before l t u

/-- `(*Time).Sub`. -/
theorem Time.wp_ptr_Sub (l : Loc) (t u : time.Time) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"Sub")) (Val #u))
    {{ (d : w64), RET #d; l ↦ t }} :=
  Time.wp_ptr_Sub_of Time.wp_Sub l t u

end results

section chan_results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `(*Timer).Stop()` for a timer made by `NewTimer` (`isTimer`): some `bool` (`Timer.wp_Stop`'s
first case; this was the axiom `Timer.wp_Stop`). -/
theorem Timer.wp_Stop_timer (t ch : Loc) (γ : ChanNames) :
    {{ isTimer (GF := GF) t ch γ }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Stop")) (Val #()))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ #Ht HΦ
  wp_apply Timer.wp_Stop t $$ [] as %b -
  · ileft; iexists ch, γ; iexact Ht
  iapply HΦ
  itrivial

/-- `(*Timer).Stop()` for a timer made by `AfterFunc` (`isFuncTimer`): some `bool`
(`Timer.wp_Stop`'s second case, see its docstring). -/
theorem Timer.wp_Stop_func (t : Loc) :
    {{ isFuncTimer (GF := GF) t }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Stop")) (Val #()))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ #Ht HΦ
  wp_apply Timer.wp_Stop t $$ [] as %b -
  · iright; iexact Ht
  iapply HΦ
  itrivial

end chan_results

end time

end Perennial
