/-
The crash token of a generation.

A *generation* is the execution of the node between two crashes (or from the
start to the first crash). Each generation has its own ghost name (`CrashGS`,
part of the per-generation `GooseLocalGS`): the state interpretation owns
`notCrashed` for as long as the generation runs, and the crash adequacy theorem
(`goose_crash_adequacy`, `CrashAdequacy.lean`) turns it into the persistent
`crashed` when the generation crashes, and hands that to the recovery
procedure. The two are exclusive, so `crashed` of a generation is evidence that
it has crashed: a step of one of its threads, which owns the state
interpretation and with it `notCrashed`, can rule it out.
-/
module

public import Perennial.Ghost.DGhostVar

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI ProofMode

/-- The crash token of a generation (`dghostVar Unit` of the ambient `AllG`). -/
class CrashGS (GF : BundledGFunctors) where
  crashName : GName

variable {GF : BundledGFunctors} [AllG GF]

section defs
variable [hC : CrashGS GF]

/-- The generation has not crashed (owned by its state interpretation). -/
def notCrashed : IProp GF := dghostVar hC.crashName (.own 1) ()

/-- The generation has crashed. -/
def crashed : IProp GF := dghostVar hC.crashName .discard ()

instance crashed_persistent : Persistent (crashed (GF := GF)) := by
  unfold crashed; infer_instance

instance crashed_timeless : Timeless (crashed (GF := GF)) := by
  unfold crashed; infer_instance

instance notCrashed_timeless : Timeless (notCrashed (GF := GF)) := by
  unfold notCrashed; infer_instance

theorem notCrashed_crashed : ⊢ notCrashed (GF := GF) -∗ crashed -∗ False := by
  unfold notCrashed crashed
  iintro H1 H2
  icases dghostVar_valid_2 _ () _ () _ $$ H1 H2 with %⟨H, -⟩
  exact absurd (DFrac.valid_own_op_discard.mp H) (by simp)

/-- The crash of a generation. -/
theorem notCrashed_crash : ⊢ notCrashed (GF := GF) ==∗ crashed := by
  unfold notCrashed crashed
  exact dghostVar_persist _ 1 ()

end defs

theorem crashToken_init : ⊢@{IProp GF} |==> ∃ γ : GName, notCrashed (hC := ⟨γ⟩) := by
  unfold notCrashed
  exact dghostVar_alloc ()

end Perennial
