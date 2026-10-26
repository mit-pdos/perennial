/-
The context `Background()` returns (`backgroundCtxVal`): the specs of its `Done` and
`Deadline` methods (promoted from the embedded `emptyCtx`; method-set wrappers, not functions of
the package's code), its `deadlineSpec`, and `parentCancelCtx(Background())`
(`wp_parentCancelCtx_background`: a second triple of `parentCancelCtx`, with the exact result,
proved from its code; `removeChild` and `propagateCancel` use it).
-/
module

public import Perennial.Proof.context.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace context

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

/-! ### `Background()` -/

theorem wp_background_Done :
    {{ (True : IProp GF) }}
      (App (Val #(methods backgroundCtx.ty go!"Done" #(zero_val backgroundCtx))) (Val #()))
    {{ RET #chan.nil; True }} := by
  wp_start
  wp_method_call
  wp_auto
  iapply HΦ
  itrivial

theorem wp_background_Deadline :
    {{ (True : IProp GF) }}
      (App (Val #(methods backgroundCtx.ty go!"Deadline" #(zero_val backgroundCtx))) (Val #()))
    {{ RET (PairV #(zero_val time.Time) #false); True }} := by
  wp_start
  wp_method_call
  wp_auto
  iapply HΦ
  itrivial

theorem wp_parentCancelCtx_background :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (Val (@! context.parentCancelCtx)) (Val #(interface.ok backgroundCtxVal)))
    {{ RET (PairV #Loc.null #false); True }} := by
  wp_start
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, ⟨%closed, #Hclosed⟩, _⟩
  wp_alloc par as Hpar
  wp_auto
  wp_apply wp_background_Done
  by_cases h : chan.nil = closed
  · simp only [h, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  · simp only [h, _root_.decide_false]
    wp_auto
    iapply HΦ; itrivial

theorem deadlineSpec_background : ⊢ deadlineSpec (GF := GF) backgroundCtxVal none := by
  unfold deadlineSpec
  simp only [Option.getD]
  imodintro
  iintro %Φ - HΦ
  iapply wp_background_Deadline
  · itrivial
  inext; iintro -
  iapply HΦ $$ []
  itrivial

end wps

end context

end Perennial
