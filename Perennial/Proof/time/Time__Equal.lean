/-
The proof of `time.Time.Equal`.
-/
module

public import Perennial.Spec.time.Time__Equal
public import Perennial.Spec.time.Time__sec
public import Perennial.Spec.time.Time__nsec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.Time.Equal.wp_proof
    (wp_Time_sec : time.Time.sec.spec (GF := GF) (hG := hG))
    (wp_Time_nsec : time.Time.nsec.spec (GF := GF) (hG := hG)) :
    time.Time.Equal.spec (GF := GF) (hG := hG) := by
  intro t u
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply wp_Time_sec $$ [$t] as t
    wp_apply wp_Time_sec $$ [$u] as u
    repeat' (first | wp_if_destruct | wp_apply wp_Time_nsec $$ [$t] as t |
      wp_apply wp_Time_nsec $$ [$u] as u)
    -- each leaf returns a literal: `time.Time.equal`'s value there
    all_goals first
      | (have hb : t.equal u = true := by
          clear wp_Time_sec wp_Time_nsec
          rw [time.Time.equal_of_not_mono (t := t) (u := u) ‹_›]; simp_all
         rw [hb]; wp_end)
      | (have hb : t.equal u = false := by
          clear wp_Time_sec wp_Time_nsec
          rw [time.Time.equal_of_not_mono (t := t) (u := u) ‹_›]; simp_all
         rw [hb]; wp_end)
  · rw [time.Time.equal_of_mono Hif]
    wp_end

end proof

end Perennial
