/-
The proof of `sync.OnceValue`.
-/
module

public import Perennial.Spec.sync.OnceValue
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

theorem sync.OnceValue.wp_proof
    (wp_Once_Do : sync.Once.Do.spec (GF := GF) (hG := hG)) :
    sync.OnceValue.spec (GF := GF) (hG := hG) := fun {T'} _ _ {T} _ f => by
  wp_start
  wp_auto
  iapply HΦ
  iintro %P %Q %E #HQp HP #Hf
  -- as for `OnceFunc`, with `d.result`
  iStructNamed d
  imod sync.init_Once (structFieldRef (sync.«struct#a4b331e8» T') go!"once" d_ptr)
    iprop(P ∗ structFieldRef (sync.«struct#a4b331e8» T') go!"f" d_ptr ↦ f ∗
      structFieldRef (sync.«struct#a4b331e8» T') go!"valid" d_ptr ↦ false ∗
      structFieldRef (sync.«struct#a4b331e8» T') go!"p" d_ptr ↦ GoInterface.nil ∗
      ∃ r : T', structFieldRef (sync.«struct#a4b331e8» T') go!"result" d_ptr ↦ r)
    iprop(∃ v : T', □ Q v ∗ structFieldRef (sync.«struct#a4b331e8» T') go!"valid" d_ptr ↦□ true ∗
      structFieldRef (sync.«struct#a4b331e8» T') go!"result" d_ptr ↦□ v) E
    $$ [once HP f valid p result] with #Ho
  · iframe
  imodintro
  imodintro
  wp_start
  wp_auto
  wp_apply wp_Once_Do $$ [$Ho] as ⟨%v, #HQ, #Hv, #Hr⟩
  · iintro !>
    wp_start as ⟨HP, Hfp, Hvalid, Hp, %r, Hr⟩
    wp_apply wp_with_defer_recover as %defer %pnc Hdefer Hpnc
    -- (`wp_apply_raw`, not `wp_apply`: the post-processing of `wp_apply` runs `whnfR` on the
    -- continuation's premise outside the goal's context, which fails on `Q`, a variable
    -- introduced by `iintro`)
    wp_apply_raw Hf $$ HP
    iintro !> %v HQ
    ihave #HQ2 := HQp $$ HQ
    wp_auto
    ipersist Hvalid
    ipersist Hr
    wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
    iapply HΦ
    iframe #
  iapply HΦ $$ HQ

end proof

end Perennial
