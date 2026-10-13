/-
The proof of `sync.(*Once).Do`.
-/
module

public import Perennial.Spec.sync.Once__Do
public import Perennial.Spec.sync.Once__doSlow
public import Perennial.Spec.sync.atomic.Bool__Load

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.Once.Do.wp_proof
    (wp_Bool_Load : sync.atomic.Bool.Load.spec (GF := GF) (hG := hG))
    (wp_Once_doSlow : sync.Once.doSlow.spec (GF := GF) (hG := hG)) :
    sync.Once.Do.spec (GF := GF) (hG := hG) := fun o P Q f => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so it
  -- fails on goals mentioning variables introduced by a tactic)
  wp_start as ⟨#HO, #Hf⟩
  simp only [isOnce_unseal, isOnceDef]
  iNamed HO
  wp_auto_lc 1
  wp_apply_core wp_Bool_Load $$ [] [-]
  · iPkgInit
  iinv Qinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold OnceInv
  icases Hi with ⟨%done, done1, #HQ⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists done
  iframe done1
  iintro done1
  imod Hmask with _
  imod Hclose $$ [done1] with _
  · inext; iexists done; iframe done1; iframe #
  imodintro
  wp_auto
  cases done
  · (try wp_auto)
    wp_apply wp_Once_doSlow o P Q f $$ [] with HQ'
    · rw [isOnce_unseal]; unfold isOnceDef; iframe #; simp only [named]; ipureintro; exact Hal
    iapply HΦ $$ HQ'
  · (try wp_auto)
    iapply HΦ
    iapply HQ
    ipureintro; rfl

end proof

end Perennial
