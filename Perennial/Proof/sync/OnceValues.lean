/-
The proof of `sync.OnceValues`.
-/
module

public import Perennial.Spec.sync.OnceValues
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

theorem sync.OnceValues.wp_proof
    (wp_Once_Do : sync.Once.Do.spec (GF := GF) (hG := hG)) :
    sync.OnceValues.spec (GF := GF) (hG := hG) := fun {T1'} _ _ {T1} _ {T2'} _ _ {T2} _ f => by
  wp_start
  wp_auto
  iapply HΦ
  iintro %P %Q %E #HQp HP #Hf
  -- as for `OnceFunc`, with `d.r1` and `d.r2`
  iStructNamed d
  imod sync.init_Once (structFieldRef (sync.«struct#3b550fdf» T1' T2') go!"once" d_ptr)
    iprop(P ∗ structFieldRef (sync.«struct#3b550fdf» T1' T2') go!"f" d_ptr ↦ f ∗
      structFieldRef (sync.«struct#3b550fdf» T1' T2') go!"valid" d_ptr ↦ false ∗
      structFieldRef (sync.«struct#3b550fdf» T1' T2') go!"p" d_ptr ↦ GoInterface.nil ∗
      (∃ r : T1', structFieldRef (sync.«struct#3b550fdf» T1' T2') go!"r1" d_ptr ↦ r) ∗
      ∃ r : T2', structFieldRef (sync.«struct#3b550fdf» T1' T2') go!"r2" d_ptr ↦ r)
    iprop(∃ (v1 : T1') (v2 : T2'), □ Q v1 v2 ∗
      structFieldRef (sync.«struct#3b550fdf» T1' T2') go!"valid" d_ptr ↦□ true ∗
      structFieldRef (sync.«struct#3b550fdf» T1' T2') go!"r1" d_ptr ↦□ v1 ∗
      structFieldRef (sync.«struct#3b550fdf» T1' T2') go!"r2" d_ptr ↦□ v2) E
    $$ [once HP f valid p r1 r2] with #Ho
  · iframe
  imodintro
  imodintro
  wp_start
  wp_auto
  wp_apply wp_Once_Do $$ [$Ho] as ⟨%v1, %v2, #HQ, #Hv, #Hr1, #Hr2⟩
  · iintro !>
    wp_start as ⟨HP, Hfp, Hvalid, Hp, ⟨%r1, Hr1⟩, %r2, Hr2⟩
    wp_apply wp_with_defer_recover as %defer %pnc Hdefer Hpnc
    wp_apply Hf $$ HP as %v1 %v2 HQ
    ihave #HQ2 := HQp $$ HQ
    ipersist Hvalid
    ipersist Hr1
    ipersist Hr2
    wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
    iapply HΦ
    iframe #
  iapply HΦ $$ HQ

end proof

end Perennial
