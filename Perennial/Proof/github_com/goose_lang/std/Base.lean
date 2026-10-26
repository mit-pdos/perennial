/-
Shared definitions of the proofs of `github.com/goose-lang/std`: its `isPkgInit`, a lemma
about loop indices, the predicate `isJoinHandle` of `JoinHandle` (with `jhP`, `jhInv`), and
`Mutex_is_Locker_of`, the `Locker` instance of a `sync.Mutex` derived from the specs of its
`Lock` and `Unlock` (as `sync.Mutex_is_Locker` in `Perennial/Proof/sync/Results.lean`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.github_com.goose_lang.std
public import Perennial.GeneratedProof.github_com.goose_lang.std
public import Perennial.Proof.math.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Perennial.Proof.github_com.goose_lang.std.std_core.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.CondDefs
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace github_com.goose_lang.std

theorem sint_nonneg_of_lt (i n : w64) (h : uint.Z i < uint.Z n) (hn : 0 ≤ sint.Z n) :
    0 ≤ sint.Z i ∧ sint.Z i = uint.Z i := by
  constructor <;> word

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.goose_lang.std :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.goose_lang.std :=
  build_get_is_pkg_init_wf

/-- `if done_b then P else True` (a `def`, so that the proof mode does not
unfold the `if`). -/
def jhP (done_b : Bool) (P : IProp GF) : IProp GF := if done_b then P else iprop(True)

abbrev jhInv (l : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ done_b : Bool,
    "done_b" ∷ typedPointsto (structFieldRef JoinHandle go!"done" l) done_b (DFrac.own 1) ∗
    "HP" ∷ jhP done_b P)

def isJoinHandle (l : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ (mu_l cond_l : Loc),
    "#mu" ∷ typedPointsto (structFieldRef JoinHandle go!"mu" l) mu_l DFrac.discard ∗
    "#cond" ∷ typedPointsto (structFieldRef JoinHandle go!"cond" l) cond_l DFrac.discard ∗
    "#Hcond" ∷ sync.isCond cond_l (interface.mk (go.GoType.PointerType sync.Mutex.ty) #mu_l) ∗
    "#Hlock" ∷ sync.isMutex mu_l (jhInv l P))

instance isJoinHandle_persistent (l : Loc) (P : IProp GF) :
    Persistent (isJoinHandle (GF := GF) l P) := by
  unfold isJoinHandle named; infer_instance

/-- A `sync.Mutex` is a `Locker` for its invariant, from the specs of its `Lock` and
`Unlock` (the proof of `sync.Mutex_is_Locker`, `Perennial/Proof/sync/Results.lean`). -/
theorem Mutex_is_Locker_of
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (m : Loc) (R : IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync -∗ sync.isMutex m R -∗
      sync.isLocker (interface.mk (go.GoType.PointerType sync.Mutex.ty) #m)
        iprop(sync.ownMutex m ∗ R) := by
  iintro #Hi #Hm
  unfold sync.isLocker
  isplitl
  · imodintro
    iintro %Φ _ HΦ
    wp_apply wp_Mutex_Lock $$ [$Hm] with H
    iapply HΦ $$ H
  · imodintro
    iintro %Φ ⟨Hown, HR⟩ HΦ
    wp_apply wp_Mutex_Unlock $$ [$Hm $Hown $HR]
    iapply HΦ
    itrivial

end wps

end github_com.goose_lang.std

end Perennial
end
