/-
The proof of `io.ReadFull`.
-/
module

public import Perennial.Spec.io.ReadFull
public import Perennial.Spec.io.ReadAtLeast

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

theorem io.ReadFull.wp_proof
    (wp_ReadAtLeast : io.ReadAtLeast.spec (GF := GF) (hG := hG)) :
    io.ReadFull.spec (GF := GF) (hG := hG) := by
  intro ri Pre S E r0 p xs eof ueof
  wp_start as ⟨#Hr, #Heof, #Hueof, %Hpre, HS, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hp
  ihave Hi := io.isInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, HSB, -⟩
  iunfold errors.newVar at HSB
  icases HSB with ⟨%xsb, #HSB, -⟩
  wp_auto
  wp_apply wp_ReadAtLeast ri Pre S E r0 p xs p.len eof ueof _ $$ [Hp HS]
    as %n %err ⟨%ys, %Hys, Hp, HS, #Hres⟩
  · iframe Hr Heof Hueof HSB HS Hp
    ipureintro; exact Hpre
  wp_auto
  iapply HΦ
  iexists ys
  iframe Hp HS
  isplit
  · ipureintro; exact Hys
  have hm : sint.Z p.len = ((xs.length : Nat) : Int) := by word
  rw [hm]
  iapply io.readFullRes_of_readAtLeastRes E eof ueof _ r0 ys xs.length err Hys.2 $$ Hres

end proof

end Perennial
