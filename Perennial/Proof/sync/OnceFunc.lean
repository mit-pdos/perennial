/-
The proof of `sync.OnceFunc`.
-/
module

public import Perennial.Spec.sync.OnceFunc
public import Perennial.Spec.sync.Once__Do

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.OnceFunc.wp_proof
    (wp_Once_Do : sync.Once.Do.spec (GF := GF) (hG := hG)) :
    sync.OnceFunc.spec (GF := GF) (hG := hG) := fun f => by
  wp_start
  wp_auto
  iapply HΦ
  iintro %P %Q %E #HQp HP #Hf
  -- the once's precondition: `P` and the fields its call writes; its postcondition: `□ Q` and
  -- `d.valid`, which every call of the returned function reads after `d.once.Do`
  iStructNamed d
  imod sync.init_Once (structFieldRef sync.«struct#27ad43a3» go!"once" d_ptr)
    iprop(P ∗ structFieldRef sync.«struct#27ad43a3» go!"f" d_ptr ↦ f ∗
      structFieldRef sync.«struct#27ad43a3» go!"valid" d_ptr ↦ false ∗
      structFieldRef sync.«struct#27ad43a3» go!"p" d_ptr ↦ GoInterface.nil)
    iprop(□ Q ∗ structFieldRef sync.«struct#27ad43a3» go!"valid" d_ptr ↦□ true) E
    $$ [once HP f valid p] with #Ho
  · iframe
  imodintro
  imodintro
  wp_start
  wp_auto
  wp_apply wp_Once_Do $$ [$Ho] as ⟨#HQ, #Hv⟩
  · iintro !>
    wp_start as ⟨HP, Hfp, Hvalid, Hp⟩
    wp_apply wp_with_defer_recover as %defer %pnc Hdefer Hpnc
    -- (`wp_apply_raw`, not `wp_apply`: the post-processing of `wp_apply` runs `whnfR` on the
    -- continuation's premise outside the goal's context, which fails on `Q`, a variable
    -- introduced by `iintro`)
    wp_apply_raw Hf $$ HP
    iintro !> HQ
    ihave #HQ2 := HQp $$ HQ
    wp_auto
    ipersist Hvalid
    -- the deferred function: `recover()` returns `nil`, and `d.valid` is true
    wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
    iapply HΦ
    iframe #
  iapply HΦ $$ HQ

end proof

end Perennial
