/-
The proof of `context.Cause`.
-/
module

public import Perennial.Spec.context.Cause
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.Cause.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    context.Cause.spec (GF := GF) (hG := hG) := fun ctx ctx_desc => by
  wp_start as #Hctx
  unfold isContext isContextDef
  icases Hctx with ⟨#HDeadline, #HDone, #HErr, #HValue, -⟩
  wp_auto
  ihave #HErr' := HErr $$ %Broadcast.Unknown
  wp_apply HErr' as %err -
  cases err with
  | nil =>
    wp_auto
    wp_end
  | ok ierr =>
    wp_auto
    unfold cancelCtxKeyAny
    wp_apply HValue as %v #Hv
    cases v with
    | nil =>
      wp_auto
      wp_end
    | ok ii =>
      by_cases hty : ii.ty = go.GoType.PointerType context.cancelCtx.ty
      · simp only [isCancelCtxAny, hty, ↓reduceIte, decide_true]
        icases Hv with ⟨%cc, %hv, #Hcc⟩
        rw [hv]
        unfold isCancelCtx
        icases Hcc with ⟨%γc, %Pc, #Hcc⟩
        unfold isCancelCtxOf
        iNamed Hcc
        wp_auto
        wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
        unfold cancelCtxLockInv
        icases Hlk with ⟨%children, %cause, %od, %closed, Hchildren, Hcause, Hcl, Hod, HR⟩
        wp_auto
        wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod HR]
        · inext; iexists children, cause, od, closed; iframe
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

end proof

end Perennial
